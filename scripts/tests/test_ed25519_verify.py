"""scripts/ed25519_verify.py against RFC 8032's test vectors 1-3 (section 7.1) and altered inputs."""
import hashlib
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS))
import ed25519_verify as ed  # noqa: E402

# (secret key, public key, message, signature), RFC 8032 section 7.1, TEST 1 to TEST 3
VECTORS = [
    ('9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60',
     'd75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a', '',
     'e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b'),
    ('4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb',
     '3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c', '72',
     '92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00'),
    ('c5aa8df43f9f837bedb7442f31dcb7b166d38535076f094b85ce3a2e0b4458f7',
     'fc51cd8e6218a1a38da47ed00230f0580816ed13ba3303ac5deb911548908025', 'af82',
     '6291d657deec24024827e69c3abe01a30ce548a284743a445e3680d7db5ac3ac18ff9b538d16f290ae67f760984dc6594a7c15e9716ed28dc027beceea1ec40a'),
]


def encode(point):
    x, y, z, _ = point
    zi = pow(z, ed.P - 2, ed.P)
    x, y = x * zi % ed.P, y * zi % ed.P
    return (y | (x & 1) << 255).to_bytes(32, 'little')


def sign(secret, message):
    """RFC 8032 5.1.6, for tests only: (public key, signature)."""
    h = hashlib.sha512(secret).digest()
    a = int.from_bytes(h[:32], 'little')
    a = (a & ((1 << 254) - 8)) | (1 << 254)
    public = encode(ed._multiply(a, ed.BASE))
    r = int.from_bytes(hashlib.sha512(h[32:] + message).digest(), 'little') % ed.L
    big_r = encode(ed._multiply(r, ed.BASE))
    k = int.from_bytes(hashlib.sha512(big_r + public + message).digest(), 'little') % ed.L
    return public, big_r + ((r + k * a) % ed.L).to_bytes(32, 'little')


class Ed25519VerifyTests(unittest.TestCase):
    def test_rfc8032_vectors_verify(self):
        for _, public, message, signature in VECTORS:
            with self.subTest(public=public[:8]):
                self.assertTrue(ed.verify(bytes.fromhex(public), bytes.fromhex(message), bytes.fromhex(signature)))

    def test_the_test_signer_reproduces_the_vectors(self):
        # the signer the census tests use is RFC 8032's: it gives the vectors' keys and signatures
        for secret, public, message, signature in VECTORS:
            self.assertEqual(sign(bytes.fromhex(secret), bytes.fromhex(message)),
                             (bytes.fromhex(public), bytes.fromhex(signature)))

    def test_a_tampered_message_is_refused(self):
        _, public, message, signature = VECTORS[2]
        for altered in ['af83', 'ae82', 'af', 'af8200', '']:
            self.assertFalse(ed.verify(bytes.fromhex(public), bytes.fromhex(altered), bytes.fromhex(signature)))

    def test_another_key_or_an_altered_signature_is_refused(self):
        _, public, message, signature = VECTORS[1]
        self.assertFalse(ed.verify(bytes.fromhex(VECTORS[0][1]), bytes.fromhex(message), bytes.fromhex(signature)))
        sig = bytearray.fromhex(signature)
        for index in (0, 31, 32, 63):
            altered = bytearray(sig)
            altered[index] ^= 1
            self.assertFalse(ed.verify(bytes.fromhex(public), bytes.fromhex(message), bytes(altered)))

    def test_noncanonical_encodings_are_refused(self):
        _, public, message, signature = VECTORS[1]
        public, message, signature = bytes.fromhex(public), bytes.fromhex(message), bytes.fromhex(signature)
        # S + L is the same scalar mod L, but RFC 8032 requires S < L
        s = int.from_bytes(signature[32:], 'little') + ed.L
        self.assertFalse(ed.verify(public, message, signature[:32] + s.to_bytes(32, 'little')))
        # y = p (>= p) is no encoding of a point
        self.assertFalse(ed.verify(ed.P.to_bytes(32, 'little'), message, signature))
        # wrong lengths
        self.assertFalse(ed.verify(public[:31], message, signature))
        self.assertFalse(ed.verify(public, message, signature[:63]))

    def test_command_line(self):
        _, public, message, signature = VECTORS[2]
        with tempfile.NamedTemporaryFile() as f:
            f.write(bytes.fromhex(message))
            f.flush()
            script = [sys.executable, str(SCRIPTS / 'ed25519_verify.py')]
            self.assertEqual(subprocess.run(script + [public, signature, f.name], stdout=subprocess.DEVNULL).returncode, 0)
            self.assertEqual(subprocess.run(script + [VECTORS[0][1], signature, f.name],
                                            stdout=subprocess.DEVNULL).returncode, 1)


if __name__ == '__main__':
    unittest.main()
