-- The core library (`WinnowCore` in lakefile.toml): what transaction review needs and nothing else. Hashes and
-- the curve, BIP32 and key encoding, transactions, PSBTs and sighashes, descriptors and the addresses they
-- derive, spend review, what a reviewed send authorizes, and the header chain. No seed phrases, Unicode tables, coin selection, wallet naming
-- or I/O. `Winnow` imports it; scripts/check-core holds its import closure to an allowed list (CI runs it).
-- The curve in it is `SecpCt`'s code that runs (field, scalars, points, keys, BIP 340) and none of its proofs.
import Winnow.Crypto
import Winnow.Keys.BIP32
import Winnow.Keys.Taproot
import Winnow.Tx
import Winnow.Wallet.Descriptor
import Winnow.Wallet.SpendReview
import Winnow.Wallet.SegwitSpendReview
import Winnow.Wallet.SendAuthorization
import Winnow.Net.Params
import Winnow.Net.HeaderChain
