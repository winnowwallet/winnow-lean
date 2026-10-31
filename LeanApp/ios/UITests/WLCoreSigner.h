// A Bitcoin Core wallet as the other signer of a multisig account (upstream's CoreSigner): its own seed,
// its own libsecp256k1. The app gets its key as `[fp/86'/1'/0']tpub…/<0;1>/*`; Core gets the account's
// descriptor with that key's tprv in its place, and signs the PSBTs the app shares.
#import <Foundation/Foundation.h>

NS_ASSUME_NONNULL_BEGIN

@interface WLCoreSigner : NSObject
/// A new descriptor wallet `name` on the fixture's node.
- (instancetype)initWithWallet:(NSString *)name;
@property (readonly) NSString *wallet;
/// The key expression a Winnow signer is given.
@property (readonly) NSString *keyExpression;
/// Imports the account (the descriptor the app shows) with this wallet's private key in its place.
- (void)importAccount:(NSString *)descriptor;
/// The PSBT with this wallet's signatures added (walletprocesspsbt).
- (NSString *)sign:(NSString *)psbt;
@end

/// A descriptor with its checksum, as the node computes it (any `#…` already on it is dropped).
NSString *WLWithChecksum(NSString *descriptor);
/// The descriptor's address at `index` on its first branch (each `<a;b>` read as `a`), derived by the node.
NSString *WLDeriveAddress(NSString *descriptor, NSInteger index);

NS_ASSUME_NONNULL_END
