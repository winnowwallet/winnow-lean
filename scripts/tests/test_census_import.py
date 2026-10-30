"""scripts/import-census offline: the pinned signature, the health filter, the derived file, census-check.

A synthetic census is signed with a test key and served from a directory (as CENSUS_SOURCE does). The
census-check tests run Lean's census-check (CENSUS_CHECK, else Lean/.lake/build/bin/census-check); they
are skipped when it is not built, and fail instead under CI=true.
"""
import gzip
import hashlib
import importlib.machinery
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(Path(__file__).resolve().parent))
from test_ed25519_verify import sign  # noqa: E402

loader = importlib.machinery.SourceFileLoader('import_census', str(SCRIPTS / 'import-census'))
spec = importlib.util.spec_from_loader('import_census', loader)
census = importlib.util.module_from_spec(spec)
loader.exec_module(census)

SECRET = bytes(range(32))
PUBLIC, _ = sign(SECRET, b'')
OTHER_SECRET = bytes(range(1, 33))
TIP = 900_000
ONIONS = [c * 56 + '.onion' for c in 'abcdefg']


def clearnet_host(i):
    # a public IPv4 address in its own /16 (the app's netblock), for i < 8800
    return f'{11 + i // 100}.{i % 100}.7.7'


def catalog(clearnet=250, tor=ONIONS):
    entries = [{'host': clearnet_host(i), 'port': 8333, 'startHeight': TIP, 'userAgent': '/Satoshi:28.0.0/'}
               for i in range(clearnet)]
    entries.append({'host': '2a01:4f8::1', 'port': 8333, 'startHeight': TIP, 'userAgent': '/Satoshi:29.0.0/'})
    return {'date': '2026-10-27', 'networks': {
        'clearnet': entries,
        'tor': [{'host': h, 'port': 8333, 'startHeight': TIP, 'userAgent': '/Satoshi:28.0.0/'} for h in tor],
    }, 'schemaVersion': 1, 'tip': TIP}


def record(endpoint, network, score, days=27):
    return {'endpoint': endpoint, 'network': network, 'attemptDays': days, 'consistencyScore': score,
            'nearTipResponseDays': 0, 'aheadResponseDays': 0, 'status': 'measured'}


class CensusDirectory:
    """A census/ folder: peers.json (signed), peers.json.sig, health.json and its nodes artifact."""

    def __init__(self, root, document, nodes=None, secret=SECRET, health=True):
        self.root = Path(root)
        self.peers = census.census_json(document)
        public, signature = sign(secret, census.DOMAIN + self.peers)
        (self.root / 'peers.json').write_bytes(self.peers)
        (self.root / 'peers.json.sig').write_text(json.dumps(
            {'algorithm': 'ed25519', 'publicKey': public.hex(), 'signature': signature.hex()}))
        if health:
            artifact = gzip.compress(json.dumps({'asOf': '2026-10-27T12:00:00Z', 'nodes': nodes or [],
                                                 'schemaVersion': 1}).encode())
            digest = hashlib.sha256(artifact).hexdigest()
            self.artifact = f'health-nodes-{digest}.json.gz'
            (self.root / self.artifact).write_bytes(artifact)
            (self.root / 'health.json').write_text(json.dumps({
                'schemaVersion': 1, 'modelVersion': 'observed-consistency-1', 'asOf': '2026-10-27T12:00:00Z',
                'acceptedDays': ['2026-10-25', '2026-10-26', '2026-10-27'],
                'nodesArtifact': {'file': self.artifact, 'sha256': digest}}))


def census_check_binary():
    binary = os.environ.get('CENSUS_CHECK') or str(SCRIPTS.parent / 'Lean/.lake/build/bin/census-check')
    return binary if Path(binary).exists() else None


class ImportTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.dir = Path(self.tmp.name)
        self.source = self.dir / 'census'
        self.source.mkdir()
        self.out = self.dir / 'out'
        self.keys = self.dir / 'keys.txt'
        self.keys.write_text('# test key\n' + PUBLIC.hex() + '\n')
        self.checker = self.dir / 'census-check'
        self.checker.write_text('#!/bin/sh\necho "census-check: $1 accepted"\n')
        self.checker.chmod(0o755)

    def run_import(self, checker=None):
        return census.run('c' * 40, census.Source('c' * 40, self.source), destination=self.out,
                          keys_path=self.keys, checker=checker or self.checker, log=lambda _: None)

    def shipped(self):
        return json.loads((self.out / 'peers.json').read_bytes())

    def test_inconsistent_clearnet_entries_are_dropped_and_the_rest_kept_in_order(self):
        nodes = [record(f'{clearnet_host(i)}:8333', 'ipv4', 40.0) for i in range(5)]
        nodes += [record(f'{clearnet_host(5)}:8333', 'ipv4', 69.9),
                  record(f'{clearnet_host(6)}:8333', 'ipv4', 70.0),                 # at the threshold: kept
                  record(f'{clearnet_host(7)}:8333', 'ipv4', 10.0, days=2),         # too few days: kept
                  record(f'{clearnet_host(8)}:8333', 'ipv4', None, days=1),         # no score yet: kept
                  record('[2a01:4f8::1]:8333', 'ipv6', 0.0),                        # IPv6 in brackets
                  record(ONIONS[0] + ':8333', 'tor', 0.0)]                          # overlays: counted only
        document = catalog()
        d = CensusDirectory(self.source, document, nodes)
        lines = self.run_import()
        shipped = self.shipped()
        dropped = {clearnet_host(i) for i in range(6)} | {'2a01:4f8::1'}
        expected = [e for e in document['networks']['clearnet'] if e['host'] not in dropped]
        self.assertEqual(shipped['networks']['clearnet'], expected)
        self.assertEqual(shipped['networks']['tor'], document['networks']['tor'])
        # the derived file is the census's own style of the reduced document
        self.assertEqual((self.out / 'peers.json').read_bytes(), census.census_json({**document, 'networks': {
            'clearnet': expected, 'tor': document['networks']['tor']}}))
        source = (self.out / 'peers-source.txt').read_text()
        self.assertIn('Peers: census ccccccc of 2026-10-27', source)
        self.assertIn('health clearnet: 251 -> 244 (10 covered, 7 dropped', source)
        self.assertIn('health tor: 7 kept as published (1 covered, 1 with score', source)
        self.assertIn(f'signed peers.json: sha256 {hashlib.sha256(d.peers).hexdigest()}', source)
        self.assertIn('derived from the signed file', source)
        self.assertEqual(lines[0], 'Peers: census ccccccc of 2026-10-27')

    def test_nothing_dropped_ships_the_signed_bytes(self):
        d = CensusDirectory(self.source, catalog(), [record(f'{clearnet_host(0)}:8333', 'ipv4', 100.0)])
        self.run_import()
        self.assertEqual((self.out / 'peers.json').read_bytes(), d.peers)
        self.assertIn('the signed bytes', (self.out / 'peers-source.txt').read_text())

    def test_under_200_after_the_filter_keeps_the_list_unfiltered(self):
        d = CensusDirectory(self.source, catalog(clearnet=205),
                            [record(f'{clearnet_host(i)}:8333', 'ipv4', 0.0) for i in range(10)])
        self.run_import()
        self.assertEqual((self.out / 'peers.json').read_bytes(), d.peers)
        self.assertIn('kept unfiltered: only 196 would remain, under 200', (self.out / 'peers-source.txt').read_text())

    def test_no_health_record_ships_the_signed_list_unfiltered(self):
        d = CensusDirectory(self.source, catalog(), health=False)
        self.run_import()
        self.assertEqual((self.out / 'peers.json').read_bytes(), d.peers)
        self.assertIn('health: unfiltered: the census has no health.json', (self.out / 'peers-source.txt').read_text())

    def test_a_record_on_another_network_does_not_match(self):
        CensusDirectory(self.source, catalog(), [record(f'{clearnet_host(0)}:8333', 'tor', 0.0)])
        self.run_import()
        self.assertEqual(len(self.shipped()['networks']['clearnet']), 251)

    def assertRefused(self, message):
        with self.assertRaisesRegex(census.Refused, message):
            self.run_import()
        self.assertFalse((self.out / 'peers.json').exists())

    def test_a_tampered_byte_is_refused(self):
        CensusDirectory(self.source, catalog())
        data = bytearray((self.source / 'peers.json').read_bytes())
        data[data.index(b'900000') + 5] = ord('1')
        (self.source / 'peers.json').write_bytes(bytes(data))
        self.assertRefused('does not verify under the pinned census key')

    def test_a_signature_by_another_key_is_refused(self):
        CensusDirectory(self.source, catalog(), secret=OTHER_SECRET)
        self.assertRefused('not the pinned key')

    def test_a_signature_naming_the_pinned_key_must_still_verify(self):
        CensusDirectory(self.source, catalog())
        sig = json.loads((self.source / 'peers.json.sig').read_text())
        _, other = sign(OTHER_SECRET, census.DOMAIN + (self.source / 'peers.json').read_bytes())
        (self.source / 'peers.json.sig').write_text(json.dumps({**sig, 'signature': other.hex()}))
        self.assertRefused('does not verify')

    def test_another_algorithm_or_a_malformed_signature_file_is_refused(self):
        CensusDirectory(self.source, catalog())
        sig = json.loads((self.source / 'peers.json.sig').read_text())
        (self.source / 'peers.json.sig').write_text(json.dumps({**sig, 'algorithm': 'ecdsa'}))
        self.assertRefused('not ed25519')
        (self.source / 'peers.json.sig').write_text('{"algorithm":"ed25519"}')
        self.assertRefused('not a signature file')

    def test_a_nodes_artifact_that_is_not_what_its_name_says_is_refused(self):
        d = CensusDirectory(self.source, catalog())
        (self.source / d.artifact).write_bytes(gzip.compress(b'{"nodes": []}'))
        self.assertRefused('not .* \\(its name\\)')

    def test_health_naming_an_artifact_with_another_digest_is_refused(self):
        CensusDirectory(self.source, catalog())
        health = json.loads((self.source / 'health.json').read_text())
        health['nodesArtifact']['sha256'] = 'f' * 64
        (self.source / 'health.json').write_text(json.dumps(health))
        self.assertRefused('they disagree')

    def test_a_list_census_check_refuses_is_not_written(self):
        CensusDirectory(self.source, catalog())
        failing = self.dir / 'failing-check'
        failing.write_text('#!/bin/sh\necho "census-check: thin"; exit 1\n')
        failing.chmod(0o755)
        with self.assertRaisesRegex(census.Refused, 'would not use'):
            self.run_import(checker=failing)
        self.assertEqual(list(self.out.iterdir()), [])

    def test_the_census_style_round_trips_swift_output(self):
        # JSONEncoder [.prettyPrinted, .sortedKeys]: "\/" escaped, UTF-8 as is, no final newline
        swift = ('{\n  "date" : "2026-10-27",\n  "networks" : {\n    "clearnet" : [\n      {\n'
                 '        "host" : "1.2.3.4",\n        "port" : 8333,\n        "startHeight" : 900000,\n'
                 '        "userAgent" : "\\/Satoshi:29.1.0\\/König\\"q\\\\\\u0001\\/"\n      }\n    ]\n  },\n'
                 '  "schemaVersion" : 1,\n  "tip" : 900000\n}').encode()
        self.assertEqual(census.census_json(json.loads(swift)), swift)


@unittest.skipUnless(census_check_binary() or os.environ.get('CI') == 'true', 'census-check is not built')
class CensusCheckTests(unittest.TestCase):
    def check(self, document):
        binary = census_check_binary()
        self.assertIsNotNone(binary, 'census-check is not built')
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'peers.json'
            path.write_bytes(document if isinstance(document, bytes) else census.census_json(document))
            run = subprocess.run([binary, str(path)], stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            return run.returncode, run.stdout

    def test_a_good_list_passes_with_its_counts(self):
        code, out = self.check(catalog(clearnet=60))
        self.assertEqual(code, 0, out)
        self.assertIn('2026-10-27, tip 900000: 61 clearnet, 7 tor', out)

    def test_fewer_than_50_clearnet_entries_fail(self):
        code, out = self.check(catalog(clearnet=48))
        self.assertEqual(code, 1, out)
        self.assertIn('thin', out)

    def test_a_private_host_fails(self):
        document = catalog(clearnet=60)
        document['networks']['clearnet'][3]['host'] = '192.168.1.1'
        code, out = self.check(document)
        self.assertEqual(code, 1, out)
        self.assertIn('endpoint', out)

    def test_one_netblock_twice_fails(self):
        document = catalog(clearnet=60)
        document['networks']['clearnet'][3]['host'] = '11.0.9.9'
        code, out = self.check(document)
        self.assertEqual((code, 'diversity' in out), (1, True), out)

    def test_not_json_or_another_schema_fails(self):
        self.assertEqual(self.check(b'{"schemaVersion": 1, ')[0], 1)
        self.assertEqual(self.check({**catalog(clearnet=60), 'schemaVersion': 2})[0], 1)

    def test_the_importer_runs_it_on_what_it_writes(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / 'census'
            source.mkdir()
            CensusDirectory(source, catalog(clearnet=220), [record(f'{clearnet_host(0)}:8333', 'ipv4', 1.0)])
            keys = Path(directory) / 'keys.txt'
            keys.write_text(PUBLIC.hex() + '\n')
            lines = census.run('d' * 40, census.Source('d' * 40, source), destination=Path(directory) / 'out',
                               keys_path=keys, checker=census_check_binary(), log=lambda _: None)
            self.assertIn('220 clearnet, 7 tor', lines[-1])


if __name__ == '__main__':
    unittest.main()
