#!/usr/bin/env python3
"""Ed25519 signature verification (RFC 8032, section 5.1.7), standard library only.

scripts/import-census verifies the census's signature over census/peers.json
with it, so a release build needs no package beyond Python itself. Only
verification is here: it handles public data and holds no secret, so constant
time does not matter.

    verify(public_key: bytes, message: bytes, signature: bytes) -> bool

Decoding follows RFC 8032 5.1.3: a coordinate y >= p, a point off the curve and
x = 0 with the sign bit set are refused; so is S >= L (5.1.7, step 1). The
group equation is the cofactored [8][S]B = [8]R + [8][k]A that 5.1.7 states.

Usage: scripts/ed25519_verify.py <public key hex> <signature hex> <file>
(exit 0 when the signature over the file's bytes is valid, 1 otherwise).
"""
import hashlib
import sys

P = 2 ** 255 - 19
L = 2 ** 252 + 27742317777372353535851937790883648493
D = -121665 * pow(121666, P - 2, P) % P
SQRT_M1 = pow(2, (P - 1) // 4, P)

# Points in extended homogeneous coordinates (X, Y, Z, T), x = X/Z, y = Y/Z, xy = T/Z (RFC 8032 5.1.4).
IDENTITY = (0, 1, 1, 0)


def _add(a, b):
    x1, y1, z1, t1 = a
    x2, y2, z2, t2 = b
    pa = (y1 - x1) * (y2 - x2) % P
    pb = (y1 + x1) * (y2 + x2) % P
    pc = 2 * t1 * t2 * D % P
    pd = 2 * z1 * z2 % P
    e, f, g, h = pb - pa, pd - pc, pd + pc, pb + pa
    return (e * f % P, g * h % P, f * g % P, e * h % P)


def _multiply(scalar, point):
    result = IDENTITY
    while scalar > 0:
        if scalar & 1:
            result = _add(result, point)
        point = _add(point, point)
        scalar >>= 1
    return result


def _equal(a, b):
    x1, y1, z1, _ = a
    x2, y2, z2, _ = b
    return (x1 * z2 - x2 * z1) % P == 0 and (y1 * z2 - y2 * z1) % P == 0


def _recover_x(y, sign):
    if y >= P:
        return None
    u = (y * y - 1) % P
    v = (D * y * y + 1) % P
    x = u * pow(v, 3, P) * pow(u * pow(v, 7, P), (P - 5) // 8, P) % P
    if (v * x * x - u) % P != 0:
        if (v * x * x + u) % P != 0:
            return None
        x = x * SQRT_M1 % P
    if x == 0 and sign:
        return None
    if x & 1 != sign:
        x = P - x
    return x


def _decode_point(data):
    if len(data) != 32:
        return None
    y = int.from_bytes(data, 'little')
    sign = y >> 255
    y &= (1 << 255) - 1
    x = _recover_x(y, sign)
    if x is None:
        return None
    return (x, y, 1, x * y % P)


_GY = 4 * pow(5, P - 2, P) % P
BASE = (_recover_x(_GY, 0), _GY, 1, _recover_x(_GY, 0) * _GY % P)


def verify(public_key, message, signature):
    """True when `signature` (64 bytes) is a valid Ed25519 signature of `message` by `public_key` (32 bytes)."""
    if len(public_key) != 32 or len(signature) != 64:
        return False
    a = _decode_point(public_key)
    r = _decode_point(signature[:32])
    if a is None or r is None:
        return False
    s = int.from_bytes(signature[32:], 'little')
    if s >= L:
        return False
    k = int.from_bytes(hashlib.sha512(signature[:32] + public_key + message).digest(), 'little') % L
    left = _multiply(8, _multiply(s, BASE))
    right = _multiply(8, _add(r, _multiply(k, a)))
    return _equal(left, right)


def main():
    if len(sys.argv) != 4:
        sys.exit('usage: scripts/ed25519_verify.py <public key hex> <signature hex> <file>')
    try:
        public_key, signature = bytes.fromhex(sys.argv[1]), bytes.fromhex(sys.argv[2])
    except ValueError:
        sys.exit('the public key and signature are hex')
    with open(sys.argv[3], 'rb') as f:
        message = f.read()
    ok = verify(public_key, message, signature)
    print('valid' if ok else 'invalid')
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
