-- The core library (`WinnowCore` in lakefile.toml): what transaction review needs and nothing else. Hashes and
-- the curve, BIP32 and key encoding, transactions, PSBTs and sighashes, descriptors and the addresses they
-- derive, spend review, and the header chain. No seed phrases, Unicode tables, coin selection, wallet naming
-- or I/O. `Winnow` imports it; scripts/check-core holds its import closure to an allowed list (CI runs it).
-- `Secp.Fast` is in it: `Secp.Keys` and `Winnow.Keys.Secp256k1` name it as the compiled form of their proved
-- definitions (`@[implemented_by]`), which can only be attached where a definition is declared.
import Winnow.Crypto
import Winnow.Keys.BIP32
import Winnow.Keys.Taproot
import Winnow.Tx
import Winnow.Wallet.Descriptor
import Winnow.Wallet.SpendReview
import Winnow.Net.Params
import Winnow.Net.HeaderChain
