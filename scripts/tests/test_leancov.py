"""Offline unit tests for scripts/leancov: CLI parsing, suite selection, exclude lists,
leancov binary/repo resolution order, and --report invocation."""
import importlib.machinery
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

SCRIPTS = Path(__file__).resolve().parents[1]
loader = importlib.machinery.SourceFileLoader('winnow_leancov', str(SCRIPTS / 'leancov'))
spec = importlib.util.spec_from_loader('winnow_leancov', loader)
lc = importlib.util.module_from_spec(spec)
loader.exec_module(lc)


def _make_fake_repo(base, name='leancov', with_bin=True):
    repo = base / name
    repo.mkdir(parents=True, exist_ok=True)
    (repo / 'lakefile.lean').write_text('package leancov\n')
    exe = repo / '.lake' / 'build' / 'bin' / 'leancov'
    if with_bin:
        exe.parent.mkdir(parents=True, exist_ok=True)
        exe.write_text('#!/bin/sh\nexit 0\n')
        exe.chmod(0o755)
    return repo, exe


def _make_standalone_bin(base, name='leancov'):
    bindir = base / 'bin'
    bindir.mkdir(parents=True, exist_ok=True)
    exe = bindir / name
    exe.write_text('#!/bin/sh\nexit 0\n')
    exe.chmod(0o755)
    return exe


class TestParseArgsAndSuites(unittest.TestCase):
    def test_defaults(self):
        with mock.patch.dict(os.environ, {}, clear=True):
            args = lc.parse_args([])
        self.assertEqual(args.suites, [])
        self.assertFalse(args.fast)
        self.assertFalse(args.report)
        self.assertFalse(args.no_build)
        self.assertFalse(args.clean)
        self.assertFalse(args.list)
        self.assertEqual(args.jobs, 4)
        self.assertIsNone(args.leancov_dir)
        self.assertEqual(args.sort, 'cog')
        self.assertEqual(args.top, 20)
        self.assertFalse(args.no_files)
        self.assertFalse(args.no_kinds)
        self.assertFalse(args.missed)
        self.assertIsNone(args.min_cov)
        self.assertIsNone(args.max_crap)
        self.assertIsNone(args.max_cog_crap)

    def test_flags_and_env_jobs(self):
        with mock.patch.dict(os.environ, {'COVERAGE_JOBS': '7'}, clear=True):
            env_args = lc.parse_args([])
        self.assertEqual(env_args.jobs, 7)

        args = lc.parse_args([
            '--fast', '--report', '--no-build', '--clean', '--jobs', '2',
            '--leancov-dir', '/tmp/custom-leancov', '--sort', 'crap', '--top', '15',
            '--no-files', '--no-kinds', '--missed',
            '--min-cov', '78.5', '--max-crap', '70', '--max-cog-crap', '90',
            'crypto-test', 'journeys',
        ])
        self.assertTrue(args.fast)
        self.assertTrue(args.report)
        self.assertTrue(args.no_build)
        self.assertTrue(args.clean)
        self.assertEqual(args.jobs, 2)
        self.assertEqual(args.leancov_dir, '/tmp/custom-leancov')
        self.assertEqual(args.sort, 'crap')
        self.assertEqual(args.top, 15)
        self.assertTrue(args.no_files)
        self.assertTrue(args.no_kinds)
        self.assertTrue(args.missed)
        self.assertAlmostEqual(args.min_cov, 78.5)
        self.assertAlmostEqual(args.max_crap, 70.0)
        self.assertAlmostEqual(args.max_cog_crap, 90.0)
        self.assertEqual(args.suites, ['crypto-test', 'journeys'])

    def test_select_suites_filtering(self):
        self.assertEqual(lc.select_suites([], fast=False), list(lc.SUITES))
        fast = lc.select_suites([], fast=True)
        self.assertEqual(fast, lc.FAST_SUITES)
        self.assertEqual(len(fast), 13)
        self.assertNotIn('journeys', fast)
        for reg in lc.REGTEST:
            self.assertNotIn(reg, fast)
        # explicit suites override --fast
        self.assertEqual(lc.select_suites(['journeys', 'io-test'], fast=True), ['journeys', 'io-test'])
        with self.assertRaises(SystemExit) as ctx:
            lc.select_suites(['crypto-test', 'not-a-suite'])
        self.assertIn('not-a-suite', str(ctx.exception))

    def test_report_selection(self):
        self.assertEqual(lc.report_selection(lc.parse_args([])), ([], ''))
        self.assertEqual(lc.report_selection(lc.parse_args(['--report'])), ([], ''))
        self.assertEqual(lc.report_selection(lc.parse_args(['--report', 'journeys'])), (['journeys'], 'journeys'))
        self.assertEqual(
            lc.report_selection(lc.parse_args(['--report', 'crypto-test', 'records-test'])),
            (['crypto-test', 'records-test'], 'crypto-test-records-test'),
        )
        self.assertEqual(lc.report_selection(lc.parse_args(['--report', '--fast'])), (lc.FAST_SUITES, 'fast'))

    def test_list_cli(self):
        res = subprocess.run(
            [sys.executable, str(SCRIPTS / 'leancov'), '--list'],
            check=True, capture_output=True, text=True,
        )
        lines = [line.split() for line in res.stdout.strip().splitlines()]
        listed = {parts[0]: (parts[1], parts[2]) for parts in lines}
        self.assertEqual(set(listed), set(lc.SUITES))
        self.assertEqual(listed['crypto-test'], ('Lean', 'fast'))
        self.assertEqual(listed['io-test'], ('Lean', 'regtest'))
        self.assertEqual(listed['journeys'], ('LeanApp', 'journeys'))


class TestSuitesAndExcludes(unittest.TestCase):
    def test_suite_partition_and_packages(self):
        for name, (pkg, extra) in lc.SUITES.items():
            self.assertIn(pkg, ('Lean', 'LeanApp'), name)
            self.assertIsInstance(extra, list)
        self.assertTrue(lc.REGTEST.issubset(lc.SUITES))
        self.assertIn('journeys', lc.SUITES)
        fast_set = set(lc.FAST_SUITES)
        self.assertEqual(fast_set & lc.REGTEST, set())
        self.assertNotIn('journeys', fast_set)
        self.assertEqual(fast_set | lc.REGTEST | {'journeys'}, set(lc.SUITES))

    def test_exclude_lists(self):
        for required in ('Proofs/', 'Spec/', 'Test.lean', 'Regtest.lean', 'Secp.lean', 'SecpCt.lean'):
            self.assertIn(required, lc.LEAN_EXCLUDES)
        for required in ('Project.lean', 'Test.lean', 'Journeys.lean', 'IosProject.lean', 'FoundationVectors.lean'):
            self.assertIn(required, lc.APP_EXCLUDES)


class TestResolveLeancov(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.base = Path(self.tmp.name).resolve()
        self.fake_root = self.base / 'workspace' / 'winnow-lean'
        self.fake_root.mkdir(parents=True)

    def test_resolution_order_arg_env_sibling_path(self):
        arg_repo, arg_exe = _make_fake_repo(self.base / 'arg', 'leancov')
        env_repo, env_exe = _make_fake_repo(self.base / 'env', 'leancov')
        sib_repo, sib_exe = _make_fake_repo(self.fake_root.parent, 'leancov')
        path_exe = _make_standalone_bin(self.base / 'path')

        with mock.patch.object(lc, 'ROOT', self.fake_root), \
             mock.patch.object(lc.shutil, 'which', return_value=str(path_exe)):
            # 1. --leancov-dir wins over $LEANCOV_DIR, ../leancov, and PATH
            with mock.patch.dict(os.environ, {'LEANCOV_DIR': str(env_repo)}, clear=True):
                self.assertEqual(lc.resolve_leancov(str(arg_repo)), (arg_repo, arg_exe))
            # 2. $LEANCOV_DIR wins over ../leancov and PATH
            with mock.patch.dict(os.environ, {'LEANCOV_DIR': str(env_repo)}, clear=True):
                self.assertEqual(lc.resolve_leancov(None), (env_repo, env_exe))
            # 3. ../leancov wins over PATH when no arg/env is set
            with mock.patch.dict(os.environ, {}, clear=True):
                self.assertEqual(lc.resolve_leancov(None), (sib_repo, sib_exe))

        # 4. PATH is used when ../leancov does not exist
        isolated_root = self.base / 'isolated' / 'winnow-lean'
        isolated_root.mkdir(parents=True)
        with mock.patch.object(lc, 'ROOT', isolated_root), \
             mock.patch.dict(os.environ, {}, clear=True), \
             mock.patch.object(lc.shutil, 'which', return_value=str(path_exe)):
            self.assertEqual(lc.resolve_leancov(None), (None, path_exe))

    def test_path_inside_repo_recovers_repo_dir(self):
        repo, exe = _make_fake_repo(self.base / 'installed', 'leancov')
        link_dir = self.base / 'usrbin'
        link_dir.mkdir()
        link = link_dir / 'leancov'
        link.symlink_to(exe)
        isolated_root = self.base / 'isolated2' / 'winnow-lean'
        isolated_root.mkdir(parents=True)

        with mock.patch.object(lc, 'ROOT', isolated_root), \
             mock.patch.dict(os.environ, {}, clear=True), \
             mock.patch.object(lc.shutil, 'which', return_value=str(link)):
            self.assertEqual(lc.resolve_leancov(None), (repo, exe))

    def test_path_ignores_self_wrapper_script(self):
        isolated_root = self.base / 'isolated3' / 'winnow-lean'
        isolated_root.mkdir(parents=True)
        with mock.patch.object(lc, 'ROOT', isolated_root), \
             mock.patch.dict(os.environ, {}, clear=True), \
             mock.patch.object(lc.shutil, 'which', return_value=str(SCRIPTS / 'leancov')):
            with self.assertRaises(SystemExit) as ctx:
                lc.resolve_leancov(None)
        self.assertIn('PATH', str(ctx.exception))

    def test_invalid_explicit_env_fails_closed(self):
        missing = self.base / 'does-not-exist'
        path_exe = _make_standalone_bin(self.base / 'path2')
        with mock.patch.object(lc, 'ROOT', self.fake_root), \
             mock.patch.dict(os.environ, {'LEANCOV_DIR': str(missing)}, clear=True), \
             mock.patch.object(lc.shutil, 'which', return_value=str(path_exe)):
            with self.assertRaises(SystemExit) as ctx:
                lc.resolve_leancov(None)
        self.assertIn('repository not found', str(ctx.exception))

    def test_builds_missing_binary_in_repo(self):
        repo, exe = _make_fake_repo(self.base / 'unbuilt', 'leancov', with_bin=False)
        with mock.patch.object(lc, 'run') as mock_run:
            got_dir, got_exe = lc.resolve_leancov(str(repo))
        self.assertEqual((got_dir, got_exe), (repo, exe))
        mock_run.assert_called_once_with(['lake', 'build', 'leancov'], cwd=repo)

    def test_stage_requires_repo_dir(self):
        exe = _make_standalone_bin(self.base / 'path3')
        with self.assertRaises(SystemExit) as ctx:
            lc.stage_packages(None, exe)
        self.assertIn('LEANCOV_DIR', str(ctx.exception))


class TestReportInvocation(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.base = Path(self.tmp.name).resolve()
        self.out = self.base / 'out'
        self.profiles = self.out / 'profiles'
        self.profiles.mkdir(parents=True)
        self.sites = self.out / 'sites.json'
        self.sites.write_text('{}')
        (self.profiles / 'journeys.cov').write_bytes(b'LCOV0001')
        (self.profiles / 'crypto-test.cov').write_bytes(b'LCOV0001')

        self.captured = self.base / 'argv.json'
        self.fake_bin = self.base / 'bin' / 'leancov'
        self.fake_bin.parent.mkdir(parents=True)
        self.fake_bin.write_text(
            f'#!{sys.executable}\n'
            'import json, sys\n'
            f'open({str(self.captured)!r}, "w").write(json.dumps(sys.argv[1:]))\n'
        )
        self.fake_bin.chmod(0o755)

    def test_report_subset_and_full_with_path_binary(self):
        isolated_root = self.base / 'repo' / 'winnow-lean'
        isolated_root.mkdir(parents=True)

        with mock.patch.object(lc, 'ROOT', isolated_root), \
             mock.patch.object(lc, 'OUT', self.out), \
             mock.patch.object(lc, 'PROFILES', self.profiles), \
             mock.patch.object(lc, 'SITES', self.sites), \
             mock.patch.dict(os.environ, {}, clear=True), \
             mock.patch.object(lc.shutil, 'which', return_value=str(self.fake_bin)):
            # Subset report with flags
            with mock.patch.object(sys, 'argv', [
                'leancov', '--report', 'journeys', '--top', '15',
                '--no-files', '--no-kinds', '--missed',
                '--min-cov', '78', '--max-crap', '70', '--max-cog-crap', '90',
            ]):
                with self.assertRaises(SystemExit) as ctx:
                    lc.main()
            self.assertEqual(ctx.exception.code, 0)
            argv = json.loads(self.captured.read_text())
            self.assertEqual(argv[0], 'report')
            self.assertIn('--profile', argv)
            self.assertIn(str(self.profiles / 'journeys.cov'), argv)
            self.assertIn(str(self.out / 'coverage-journeys.json'), argv)
            self.assertIn(str(self.out / 'lcov-journeys.info'), argv)
            self.assertNotIn('--files', argv)
            self.assertNotIn('--kinds', argv)
            self.assertIn('--missed', argv)
            self.assertIn('--min-cov', argv)
            self.assertIn('--max-crap', argv)
            self.assertIn('--max-cog-crap', argv)

            # Full report uses --profile-dir
            with mock.patch.object(sys, 'argv', ['leancov', '--report']):
                with self.assertRaises(SystemExit) as ctx:
                    lc.main()
            self.assertEqual(ctx.exception.code, 0)
            argv = json.loads(self.captured.read_text())
            self.assertIn('--profile-dir', argv)
            self.assertIn(str(self.profiles), argv)
            self.assertIn('--files', argv)
            self.assertIn('--kinds', argv)

            # Missing profile exits non-zero
            with mock.patch.object(sys, 'argv', ['leancov', '--report', 'fuzz']):
                with self.assertRaises(SystemExit) as ctx:
                    lc.main()
            self.assertIn('missing profile', str(ctx.exception))


if __name__ == '__main__':
    unittest.main()
