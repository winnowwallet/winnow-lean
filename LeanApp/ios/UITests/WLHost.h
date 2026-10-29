// The host side of a UI test run, reached from inside the simulator's test runner: the regtest node that
// `backend-test --fixture <dir>` left running, and host programs run with posix_spawn (Foundation's NSTask
// is unavailable on iOS, but the simulator runs macOS binaries and puts no sandbox on the runner).
#import <Foundation/Foundation.h>

NS_ASSUME_NONNULL_BEGIN

@interface WLHost : NSObject

/// The run's configuration: the JSON file named by WINNOW_UI_CONFIG (xcodebuild passes it to the runner as
/// TEST_RUNNER_WINNOW_UI_CONFIG), else `~/.winnow-lean-ui.json` on the host. Keys: `fixture` (the fixture
/// directory), `bitcoinCli`, `backendTest` (LeanApp's backend-test: the silent payment test receiver) and
/// optionally `screenshots`.
+ (instancetype)shared;

@property (readonly) NSString *fixtureDir;
@property (readonly) NSString *bitcoinCli;
@property (readonly) NSString *backendTest;
@property (readonly, nullable) NSString *screenshotDir;
@property (readonly) NSInteger p2p;
@property (readonly) NSInteger rpc;
@property (readonly) NSString *datadir;

/// Runs a host program with no environment (the runner's is the simulator's, wrong for a host binary) and
/// returns its standard output, trimmed. A nonzero exit raises, with the command and its standard error.
- (NSString *)run:(NSString *)path arguments:(NSArray<NSString *> *)arguments;

/// bitcoin-cli against the fixture's node; `wallet:` adds -rpcwallet (the fixture's funded wallet is `w`).
- (NSString *)cli:(NSArray<NSString *> *)arguments;
- (NSString *)wallet:(NSString *)wallet cli:(NSArray<NSString *> *)arguments;
- (id)cliJSON:(NSArray<NSString *> *)arguments;
- (id)wallet:(NSString *)wallet cliJSON:(NSArray<NSString *> *)arguments;

/// The node's mempool, a new address of the funded wallet, a block mined to it.
- (NSSet<NSString *> *)mempool;
- (NSString *)bankAddress;
- (void)mine:(NSInteger)blocks;
/// Pays `sats` from the funded wallet to `address` and mines it; the payment's txid.
- (NSString *)fund:(NSString *)address sats:(int64_t)sats;
/// A transaction in the mempool, decoded by the node (a confirmed one needs a wallet's gettransaction:
/// the node keeps no txindex).
- (NSDictionary *)transaction:(NSString *)txid;
/// The scriptPubKey (hex) the node derives for an address.
- (NSString *)scriptPubKey:(NSString *)address;
/// backend-test's silent payment test receiver (written from BIP352's receiving side): its code, and the
/// output script it finds in a transaction on the node.
- (NSString *)silentPaymentCode;
- (NSString *)silentPaymentExpectedScript:(NSString *)txid;

@end

NS_ASSUME_NONNULL_END
