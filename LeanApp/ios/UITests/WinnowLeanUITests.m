// The Lean app's UI journeys, in the simulator against the regtest node `backend-test --fixture` left
// running (scripts/ui-journeys, scripts/ui-fixture). Each launches the app in test mode with a fresh pinned seed, so a reused
// node never shows an earlier run's coins, and checks what the app shows against what the node holds.
#import <XCTest/XCTest.h>
#import "WLCoreSigner.h"
#import "WLHost.h"
#import "WLTest.h"

static const int64_t WLFunding = 5000000;
static const int64_t WLPayment = 1000000;
static const int64_t WLRecoveryPayment = 500000;
static const int64_t WLSilentPayment = 150000;
/// The builder's shortest recovery delay: one day.
static const NSInteger WLRecoveryBlocks = 144;

@interface WinnowLeanUITests : XCTestCase
@property (nonatomic, strong) XCUIApplication *app;
@property (nonatomic, copy) NSString *controlFile;
@end

@implementation WinnowLeanUITests

- (void)setUp {
    self.continueAfterFailure = NO;
    self.executionTimeAllowance = 900;
    self.controlFile = [NSTemporaryDirectory() stringByAppendingPathComponent:
        [NSString stringWithFormat:@"winnow-ui-%@.json", NSUUID.UUID.UUIDString]];
}

- (void)tearDown {
    [self.app terminate];
    [NSFileManager.defaultManager removeItemAtPath:self.controlFile error:nil];
}

/// What the app's Paste buttons read in test mode (`WINNOW_E2E_CONTROL_FILE`).
- (void)setClipboard:(NSString *)text {
    NSData *json = [NSJSONSerialization dataWithJSONObject:@{@"clipboard": text} options:0 error:nil];
    XCTAssertTrue([json writeToFile:self.controlFile atomically:YES]);
}

/// Launches the app in test mode on the fixture's node, as its only peer.
- (XCUIApplication *)launch:(NSString *)run extra:(NSDictionary<NSString *, NSString *> *)extra {
    WLHost *host = WLHost.shared;
    NSString *entropy = [[NSUUID.UUID.UUIDString stringByReplacingOccurrencesOfString:@"-" withString:@""] lowercaseString];
    NSMutableDictionary *env = [@{
        @"WINNOW_E2E": @"1",
        @"WINNOW_E2E_RUN": run,
        @"WINNOW_E2E_RESET": @"1",
        @"WINNOW_E2E_ENTROPY": entropy,
        @"WINNOW_E2E_NETWORK": @"regtest",
        @"WINNOW_E2E_PEER": [NSString stringWithFormat:@"127.0.0.1:%ld", (long)host.p2p],
        @"WINNOW_E2E_PEER_COUNT": @"1",
        @"WINNOW_E2E_SYNC_INTERVAL": @"3",
        @"WINNOW_E2E_CONTROL_FILE": self.controlFile,
    } mutableCopy];
    [env addEntriesFromDictionary:extra];
    self.app = [XCUIApplication new];
    self.app.launchEnvironment = env;
    [self.app launch];
    return self.app;
}

/// Creates the wallet (no phrase checklist since upstream 4228c6b: creation opens the wallet); the home
/// screen with its balance.
- (void)createWallet:(XCUIApplication *)app {
    XCTAssertTrue([WLElement(app, @"createWalletButton") waitForExistenceWithTimeout:60], @"onboarding did not open");
    WLShot(self, app, @"01-onboarding");
    WLTap(self, app, @"createWalletButton");
    XCTAssertTrue([WLElement(app, @"receiveButton") waitForExistenceWithTimeout:60], @"the wallet did not open");
    XCTAssertTrue([WLElement(app, @"balanceText") waitForExistenceWithTimeout:30]);
}

/// The receive address the app shows (its label skipped).
- (NSString *)receiveAddress:(XCUIApplication *)app {
    WLTap(self, app, @"receiveButton");
    XCUIElement *skip = WLElement(app, @"skipReceiveAddressLabelButton");
    if ([skip waitForExistenceWithTimeout:20]) [skip tap];
    XCUIElement *shown = WLElement(app, @"receiveAddress");
    XCTAssertTrue([shown waitForExistenceWithTimeout:30], @"Receive shows no address");
    NSString *address = WLText(shown);
    XCTAssertTrue([address hasPrefix:@"bcrt1"], @"not a regtest address: %@", address);
    return address;
}

- (int64_t)balance:(XCUIApplication *)app { return WLDigits(WLText(WLElement(app, @"balanceText"))); }

/// The one transaction that entered the mempool after `before`.
- (NSString *)newMempoolTransaction:(NSSet<NSString *> *)before within:(NSTimeInterval)timeout {
    __block NSString *txid = nil;
    WLPoll(timeout, 1, ^{
        NSMutableSet *now = [WLHost.shared.mempool mutableCopy];
        [now minusSet:before];
        txid = now.anyObject;
        return (BOOL)(txid != nil);
    });
    return txid;
}

/// Create a wallet, receive from the node, send to it and see the payment confirm: upstream's
/// test01CreateReceiveSendConfirm on regtest (the silent payment leg is not part of the Lean app yet).
- (void)testCreateReceiveSendConfirm {
    WLHost *host = WLHost.shared;
    NSString *destination = host.bankAddress;
    [self setClipboard:destination];
    XCUIApplication *app = [self launch:@"journey" extra:@{}];
    [self createWallet:app];

    NSString *address = [self receiveAddress:app];
    WLShot(self, app, @"03-receive");
    WLTap(self, app, @"closeReceiveButton");

    NSString *funding = [host fund:address sats:WLFunding];
    XCTAssertTrue(WLPoll(90, 1, ^{ return (BOOL)([self balance:app] == WLFunding); }),
                  @"the wallet did not find the confirmed payment (balance %lld)", [self balance:app]);
    XCTAssertTrue([WLElement(app, [@"historyPayment-" stringByAppendingString:funding]) waitForExistenceWithTimeout:20],
                  @"the funding transaction is missing from Activity");
    XCUIElement *sync = WLElement(app, @"syncSummaryText");
    XCTAssertTrue(WLPoll(60, 0.5, ^{ return [WLText(sync) isEqualToString:@"Up to date"]; }), @"sync: %@", WLText(sync));
    WLShot(self, app, @"04-home-funded");

    WLTap(self, app, @"openSendButton");
    WLTap(self, app, @"pasteDestinationButton");
    WLType(self, app, @"amountField", [NSString stringWithFormat:@"%lld", WLPayment]);
    WLTap(self, app, @"reviewButton");
    XCUIElement *send = WLElement(app, @"sendButton");
    XCTAssertTrue([send waitForExistenceWithTimeout:30], @"the payment review did not open");
    XCTAssertEqualObjects(WLText(WLElement(app, @"reviewDestination")), destination);
    XCTAssertEqual(WLDigits(WLText(WLElement(app, @"reviewAmount"))), WLPayment);
    int64_t fee = WLDigits(WLText(WLElement(app, @"reviewFee")));
    XCTAssertGreaterThan(fee, 0);
    WLShot(self, app, @"05-send-review");

    NSSet *before = host.mempool;
    WLTap(self, app, @"sendButton");
    NSString *txid = [self newMempoolTransaction:before within:60];
    XCTAssertNotNil(txid, @"the node never received the payment");
    NSString *script = [host scriptPubKey:destination];
    BOOL paysDestination = NO;
    for (NSDictionary *output in [host transaction:txid][@"vout"]) {
        if ([output[@"scriptPubKey"][@"hex"] isEqualToString:script]) {
            paysDestination = YES;
            XCTAssertEqual(llround([output[@"value"] doubleValue] * 1e8), WLPayment);
        }
    }
    XCTAssertTrue(paysDestination, @"the transaction the node accepted does not pay the reviewed destination");

    [host mine:1];
    XCTAssertTrue([WLElement(app, @"broadcastConfirmed") waitForExistenceWithTimeout:90],
                  @"the open receipt did not notice the confirmation");
    // the payment is to the node's wallet, which knows it once confirmed (the node keeps no txindex)
    NSDictionary *confirmed = [host wallet:@"w" cliJSON:@[@"gettransaction", txid]];
    XCTAssertGreaterThan([confirmed[@"confirmations"] integerValue], 0);
    WLShot(self, app, @"06-send-confirmed");
    WLTap(self, app, @"closeSendButton");
    XCTAssertTrue(WLPoll(60, 1, ^{ return (BOOL)([self balance:app] == WLFunding - WLPayment - fee); }),
                  @"balance after the payment: %lld", [self balance:app]);
    XCTAssertTrue([WLElement(app, [@"historyPayment-" stringByAppendingString:txid]) waitForExistenceWithTimeout:20],
                  @"the payment is missing from Activity");
    WLShot(self, app, @"07-home-after-send");
}

/// Advanced mode, through its alert, then the Wallet tab.
- (void)turnOnAdvanced:(XCUIApplication *)app {
    WLTap(self, app, @"advancedModeButton");
    XCUIElement *on = app.alerts.buttons[@"Turn on"];
    XCTAssertTrue([on waitForExistenceWithTimeout:10], @"no Advanced mode alert");
    [on tap];
    XCUIElement *wallet = app.tabBars.buttons[@"Wallet"];
    XCTAssertTrue([wallet waitForExistenceWithTimeout:15], @"Advanced mode shows no tabs");
    [wallet tap];
}

/// A label shown by the app, found by its text (zero-width spaces ignored).
- (XCUIElement *)text:(XCUIApplication *)app beginningWith:(NSString *)prefix {
    return [self text:app matching:[@"^" stringByAppendingString:[NSRegularExpression escapedPatternForString:prefix]]];
}

- (XCUIElement *)text:(XCUIApplication *)app matching:(NSString *)pattern {
    NSRegularExpression *re = [NSRegularExpression regularExpressionWithPattern:pattern options:0 error:nil];
    NSPredicate *p = [NSPredicate predicateWithBlock:^BOOL(id<XCUIElementAttributes> e, NSDictionary *b) {
        NSString *text = [e.label stringByReplacingOccurrencesOfString:@"\u200B" withString:@""];
        return [re firstMatchInString:text options:0 range:NSMakeRange(0, text.length)] != nil;
    }];
    return [app.staticTexts matchingPredicate:p].firstMatch;
}

/// The first input of the transaction `txid` in the mempool, with its witness.
- (NSDictionary *)spendingInput:(NSString *)txid {
    return [[WLHost.shared transaction:txid][@"vin"] firstObject];
}

/// Hex lengths of the witness's first `count` items, sorted.
static NSArray<NSNumber *> *WLWitnessSizes(NSArray<NSString *> *witness, NSUInteger count) {
    NSMutableArray *sizes = [NSMutableArray array];
    for (NSUInteger i = 0; i < count && i < witness.count; i++) [sizes addObject:@(witness[i].length)];
    return [sizes sortedArrayUsingSelector:@selector(compare:)];
}

/// Back to the Wallet tab's list (the builder and the account it opened are both on its stack).
- (void)backToWalletList:(XCUIApplication *)app {
    for (int i = 0; i < 4 && !WLElement(app, @"balanceText").exists; i++) {
        XCUIElement *back = app.navigationBars.buttons.firstMatch;
        if (back.exists) [back tap];
        [NSRunLoop.currentRunLoop runUntilDate:[NSDate dateWithTimeIntervalSinceNow:0.5]];
    }
    XCTAssertTrue([WLElement(app, @"balanceText") waitForExistenceWithTimeout:10], @"the Wallet tab did not return to its list");
}

/// The account's id: its descriptor's checksum.
static NSString *WLAccountID(NSString *descriptor) {
    NSRange hash = [descriptor rangeOfString:@"#" options:NSBackwardsSearch];
    return hash.location == NSNotFound ? @"" : [descriptor substringFromIndex:hash.location + 1];
}

/// Send, From: the account: the review names it and the signatures it needs; "Sign and continue" signs here
/// and opens the collection step (upstream #259's MultisigJourney send-tab leg).
- (void)sendFromAccount:(XCUIApplication *)app account:(NSString *)accountID to:(NSString *)destination
                  sats:(int64_t)amount needs:(NSString *)needs {
    [app.tabBars.buttons[@"Send"] tap];
    WLTap(self, app, [@"sendFrom-" stringByAppendingString:accountID]);
    XCTAssertTrue([WLElement(app, @"sendSourceNote") waitForExistenceWithTimeout:10], @"the account is not the source");
    [self setClipboard:destination];
    WLTap(self, app, @"pasteDestinationButton");
    WLType(self, app, @"amountField", [NSString stringWithFormat:@"%lld", amount]);
    WLTap(self, app, @"reviewButton");
    XCUIElement *signatures = WLElement(app, @"reviewSignatures");
    XCTAssertTrue([signatures waitForExistenceWithTimeout:30], @"the account review did not open");
    XCTAssertTrue([WLText(signatures) containsString:needs], @"review: %@", WLText(signatures));
    XCUIElement *sign = WLElement(app, @"sendButton");
    XCTAssertTrue(WLScrollTo(app, sign));
    XCTAssertEqualObjects(sign.label, @"Sign and continue");
    [sign tap];
    // the collection step replaces the review once this phone's signature is filed
    XCUIElement *count = WLElement(app, @"multisigSignatureCount");
    XCTAssertTrue(WLPoll(90, 0.5, ^{ return (BOOL)(count.exists || app.navigationBars[@"Collect signatures"].exists); }),
                  @"the collection step did not open");
    XCTAssertTrue(WLScrollTo(app, count), @"the collection step shows no signature count");
}

/// A 2-of-3 Taproot multisig account between the phone and two Bitcoin Core wallets, with a recovery path
/// letting any one of them spend a coin after a day (upstream's MultisigJourney, built in the app's own
/// builder from members): its first address must be Core's; the payment starts from Send with the account
/// as its source, "Sign and continue" signs it here, each Core wallet signs its copy with its own
/// libsecp256k1, the phone combines both (three signatures where two are needed), finalizes and broadcasts,
/// and Core must accept a witness carrying exactly two; the Transactions list shows the spend once, named
/// with the account. Then, past the delay, the phone alone spends the change on the recovery path: the
/// account page's "Send from this account" opens Send with the account under From, "Spend with" picks the
/// recovery path, and Core accepts the CSV-locked witness (the account page has no payment form of its own).
- (void)testMultisigTwoOfThreeWithRecovery {
    WLHost *host = WLHost.shared;
    NSString *run = [NSUUID.UUID.UUIDString substringToIndex:8];
    WLCoreSigner *core = [[WLCoreSigner alloc] initWithWallet:[@"ui-core-" stringByAppendingString:run]];
    WLCoreSigner *second = [[WLCoreSigner alloc] initWithWallet:[@"ui-core-second-" stringByAppendingString:run]];
    XCUIApplication *app = [self launch:@"multisig" extra:@{}];
    [self createWallet:app];
    [self turnOnAdvanced:app];

    // the account, in the app's builder: this phone and the two Core keys as members, any 2 of 3, any 1 after a day
    WLTap(self, app, @"multisigBuildButton");
    WLType(self, app, @"multisigBuildNameField", @"Phone and two Cores");
    for (WLCoreSigner *signer in @[core, second]) {
        [self setClipboard:signer.keyExpression];
        WLTap(self, app, @"multisigBuildAddMemberButton");
        WLTap(self, app, @"signerPickerPasteButton");
    }
    XCTAssertTrue([[self text:app beginningWith:@"Members · 3"] waitForExistenceWithTimeout:10], @"the two Core keys were not added");
    XCTAssertTrue([self text:app beginningWith:@"Any 2 of 3 members spend"].exists);
    XCTAssertTrue([[self text:app beginningWith:@"2 of 3: any 2 of the 3 keys sign a spend."] waitForExistenceWithTimeout:10],
                  @"no policy preview");
    WLTap(self, app, @"multisigBuildRecoveryToggle");
    XCTAssertTrue([[self text:app beginningWith:@"Any 1 of the 3 members"] waitForExistenceWithTimeout:10]);
    XCUIElement *days = WLElement(app, @"multisigBuildRecoveryDaysStepper");
    XCTAssertTrue(WLScrollTo(app, days));
    XCUIElement *delay = [self text:app matching:@"^After about \\d+ days \\("];
    XCTAssertTrue([WLText(delay) hasPrefix:@"After about 181 days (26,000 blocks)"], @"the default delay: %@", WLText(delay));
    for (int i = 0; i < 200 && ![WLText(delay) hasPrefix:@"After about 1 days"]; i++) [days.buttons[@"Decrement"] tap];
    XCTAssertEqualObjects(WLText(delay), ([NSString stringWithFormat:@"After about 1 days (%ld blocks)", (long)WLRecoveryBlocks]));
    WLShot(self, app, @"10-multisig-build");
    WLTap(self, app, @"multisigBuildCreateButton");
    XCTAssertTrue([WLElement(app, @"multisigBuildCreated") waitForExistenceWithTimeout:30], @"the account was not created");
    XCUIElement *created = WLElement(app, @"multisigCreatedDescriptor");
    XCTAssertTrue(WLScrollTo(app, created));
    NSString *descriptor = WLText(created);
    XCTAssertTrue([descriptor hasPrefix:@"tr("], @"not a descriptor: %@", descriptor);
    NSString *accountID = WLAccountID(descriptor);
    [core importAccount:descriptor];
    [second importAccount:descriptor];
    WLTap(self, app, @"multisigOpenAccountButton");

    // receive: the address on screen is Core's first address of the account
    NSString *first = WLDeriveAddress(descriptor, 0);
    XCUIElement *shown = WLElement(app, @"multisigReceiveAddress");
    XCTAssertTrue([shown waitForExistenceWithTimeout:20]);
    XCTAssertEqualObjects(WLText(shown), first, @"the account's first address is not Core's");
    NSString *funding = [host fund:first sats:WLFunding];
    XCUIElement *balance = WLElement(app, @"multisigBalance");
    XCTAssertTrue(WLPoll(90, 1, ^{ return (BOOL)(WLDigits(WLText(balance)) == WLFunding); }),
                  @"the account did not find %@ (balance %@)", funding, WLText(balance));
    WLShot(self, app, @"11-multisig-funded");

    // Send, From: the account; Sign and continue signs here; one signature is not enough
    NSString *destination = host.bankAddress;
    [self sendFromAccount:app account:accountID to:destination sats:WLPayment needs:@"needs 2 of 3"];
    XCUIElement *count = WLElement(app, @"multisigSignatureCount");
    XCTAssertTrue(WLPoll(60, 0.3, ^{ return [WLText(count) isEqualToString:@"1 of 2"]; }), @"after Sign and continue: %@", WLText(count));
    int64_t fee = WLDigits(WLText(WLElement(app, @"multisigFee")));
    XCTAssertGreaterThan(fee, 0);
    XCUIElement *broadcast = WLElement(app, @"multisigBroadcastButton");
    XCTAssertTrue(WLScrollTo(app, broadcast));
    XCTAssertFalse(broadcast.isEnabled, @"one signer alone cannot send");
    XCUIElement *shared = WLElement(app, @"multisigPSBTText");
    XCTAssertTrue(WLScrollTo(app, shared));
    NSString *phoneSigned = WLText(shared);
    // v0 opens with the unsigned transaction (global key 0x00), v2 with its version (0x02: "cHNidP8BAg")
    XCTAssertTrue([phoneSigned hasPrefix:@"cHNidP8BA"] && ![phoneSigned hasPrefix:@"cHNidP8BAg"], @"not a BIP174 v0 PSBT: %@", phoneSigned);
    WLShot(self, app, @"12-multisig-one-signature");

    // each Core wallet signs its own copy; the phone combines both
    NSArray *rounds = @[@[core, @"2 of 2"], @[second, @"3 of 2"]];
    for (NSArray *round in rounds) {
        WLCoreSigner *signer = round[0];
        NSString *expected = round[1];
        [self setClipboard:[signer sign:phoneSigned]];
        WLTap(self, app, @"psbtPasteButton");
        WLTap(self, app, @"addPSBTButton");
        XCTAssertTrue(WLPoll(30, 0.3, ^{ return [WLText(count) isEqualToString:expected]; }),
                      @"after %@: %@", signer.wallet, WLText(count));
    }

    // the phone finalizes and broadcasts; Core accepts a witness with exactly two signatures
    NSSet *before = host.mempool;
    WLTap(self, app, @"multisigBroadcastButton");
    XCTAssertTrue([WLElement(app, @"broadcastPending") waitForExistenceWithTimeout:30], @"the receipt did not open");
    NSString *txid = [self newMempoolTransaction:before within:30];
    XCTAssertNotNil(txid, @"Core did not accept the multisig payment");
    NSDictionary *input = [self spendingInput:txid];
    XCTAssertEqualObjects(input[@"txid"], funding);
    NSArray *witness = input[@"txinwitness"];
    XCTAssertEqual(witness.count, 5u, @"three key slots, the leaf script and the control block");
    XCTAssertEqualObjects(WLWitnessSizes(witness, 3), (@[@0, @128, @128]), @"exactly two 64-byte signatures");
    XCTAssertEqual([witness.lastObject length], 130u, @"a 65-byte control block");
    BOOL paid = NO;
    for (NSDictionary *output in [host transaction:txid][@"vout"])
        if ([output[@"scriptPubKey"][@"hex"] isEqualToString:[host scriptPubKey:destination]])
            paid = llround([output[@"value"] doubleValue] * 1e8) == WLPayment;
    XCTAssertTrue(paid, @"the spend does not pay the destination the reviewed amount");
    WLShot(self, app, @"13-multisig-sent");
    [host mine:1];
    NSInteger spentAt = [[host cliJSON:@[@"getblockcount"]] integerValue];
    XCTAssertTrue([WLElement(app, @"broadcastConfirmed") waitForExistenceWithTimeout:90], @"the receipt did not see it confirm");

    // one Transactions row for the spend, named with the account
    [app.tabBars.buttons[@"Wallet"] tap];
    XCTAssertTrue(WLPoll(90, 1, ^{ return (BOOL)(WLDigits(WLText(balance)) == WLFunding - WLPayment - fee); }),
                  @"the account's change: %@", WLText(balance));
    [self backToWalletList:app];
    XCUIElement *row = WLElement(app, [@"historyPayment-" stringByAppendingString:txid]);
    XCTAssertTrue([row waitForExistenceWithTimeout:30] && WLScrollTo(app, row), @"the spend is missing from Transactions");
    XCTAssertTrue(WLElement(app, [@"paymentAccount-" stringByAppendingString:txid]).exists, @"the row does not name the account");
    WLShot(self, app, @"13b-multisig-transactions");
    XCUIElement *accountButton = WLElement(app, [@"multisigAccount-" stringByAppendingString:accountID]);
    XCTAssertTrue(WLScrollTo(app, accountButton));
    [accountButton tap];

    // past the delay, the phone alone spends the change on the recovery path
    NSInteger height = [[host cliJSON:@[@"getblockcount"]] integerValue];
    if (height < spentAt + WLRecoveryBlocks - 1) [host mine:spentAt + WLRecoveryBlocks - 1 - height];
    // the account page: no payment form of its own, Send from this account, Paste a PSBT, Share with co-signers
    XCTAssertTrue(WLScrollTo(app, WLElement(app, @"multisigPastePSBTButton")), @"the account page has no Paste a PSBT");
    XCTAssertFalse(WLElement(app, @"multisigAddressField").exists, @"the account page still has a payment form");
    WLShot(self, app, @"13a-account-page");
    XCTAssertTrue(WLScrollTo(app, WLElement(app, @"multisigShareButton")), @"the account page has no Share with co-signers");
    WLShot(self, app, @"13a-account-page-share");
    WLTap(self, app, @"multisigSendButton");
    XCTAssertTrue([WLElement(app, @"sendSourceNote") waitForExistenceWithTimeout:10], @"Send does not start from the account");
    WLTap(self, app, @"multisigPathPicker");
    XCUIElement *recovery = app.buttons[@"Recovery path"];
    XCTAssertTrue([recovery waitForExistenceWithTimeout:10], @"Send offers no recovery path for the account");
    [recovery tap];
    XCTAssertTrue([WLElement(app, @"sendRecoveryNote") waitForExistenceWithTimeout:10], @"no recovery caption");
    WLShot(self, app, @"13c-send-recovery-path");
    NSString *recoveryDestination = host.bankAddress;
    [self setClipboard:recoveryDestination];
    WLTap(self, app, @"pasteDestinationButton");
    WLType(self, app, @"amountField", [NSString stringWithFormat:@"%lld", WLRecoveryPayment]);
    // the phone may not have seen the last blocks yet: review until the coin unlocks
    XCUIElement *signRecovery = WLElement(app, @"sendButton");
    XCTAssertTrue(WLPoll(120, 3, ^{
        if (signRecovery.exists) return YES;
        XCUIElement *review = WLElement(app, @"reviewButton");
        if (review.exists && review.isEnabled && WLScrollTo(app, review)) [review tap];
        return [signRecovery waitForExistenceWithTimeout:2];
    }), @"the recovery spend was not reviewed");
    XCTAssertEqualObjects(WLText(WLElement(app, @"reviewSpendPath")), @"Recovery path");
    XCTAssertTrue(WLScrollTo(app, signRecovery));
    XCTAssertEqualObjects(signRecovery.label, @"Sign and continue");
    [signRecovery tap];
    // Sign and continue signed every leaf this phone is on: the recovery leaf's one signature is in
    XCUIElement *recoveryCount = WLElement(app, @"multisigRecoverySignatureCount");
    XCTAssertTrue([recoveryCount waitForExistenceWithTimeout:90], @"the collection step shows no recovery count");
    XCTAssertTrue(WLPoll(30, 0.3, ^{ return [WLText(recoveryCount) isEqualToString:@"1 of 1"]; }),
                  @"after the phone's recovery signature: %@", WLText(recoveryCount));
    before = host.mempool;
    WLTap(self, app, @"multisigBroadcastButton");
    XCTAssertTrue([WLElement(app, @"broadcastPending") waitForExistenceWithTimeout:30], @"the recovery receipt did not open");
    NSString *recovered = [self newMempoolTransaction:before within:30];
    XCTAssertNotNil(recovered, @"Core did not accept the recovery spend");
    input = [self spendingInput:recovered];
    XCTAssertEqualObjects(input[@"txid"], txid, @"the recovery spend does not spend the change");
    XCTAssertEqual([input[@"sequence"] integerValue], WLRecoveryBlocks);
    witness = input[@"txinwitness"];
    XCTAssertEqual(witness.count, 5u, @"one signature, two empty slots, the recovery leaf and its control block");
    XCTAssertEqualObjects(WLWitnessSizes(witness, 3), (@[@0, @0, @128]));
    XCTAssertEqual([witness.lastObject length], 130u);
    WLShot(self, app, @"14-multisig-recovered");
    [host mine:1];
    NSDictionary *tip = [host cliJSON:@[@"getblock", [host cli:@[@"getbestblockhash"]]]];
    XCTAssertTrue([tip[@"tx"] containsObject:recovered], @"the recovery spend was not mined");
}

/// A 2-of-2 between the phone and a Ledger, with test mode's simulated Ledger (`WINNOW_E2E_LEDGER`, the
/// Lean device behind the app's real APDU program): pair it under Settings → Signers (its key filed,
/// nothing registered), build the account with it as a member (the Ledger registers it), have it derive
/// the receive address, which must also be Core's, fund the account from the wallet (one Transactions row,
/// a transfer), pay from it on the Send tab (Sign and continue, then the Ledger in the collection step),
/// and Core must accept a witness carrying both signatures; the receipt sees it confirm and Transactions
/// shows it once, named with the account.
- (void)testLedgerPairVerifySpend {
    WLHost *host = WLHost.shared;
    NSString *ledgerSeed = [[NSUUID.UUID.UUIDString stringByReplacingOccurrencesOfString:@"-" withString:@""] lowercaseString];
    XCUIApplication *app = [self launch:@"ledger" extra:@{@"WINNOW_E2E_LEDGER": ledgerSeed}];
    [self createWallet:app];
    NSString *walletAddress = [self receiveAddress:app];
    WLTap(self, app, @"closeReceiveButton");
    [host fund:walletAddress sats:2 * WLFunding];
    XCTAssertTrue(WLPoll(90, 1, ^{ return (BOOL)([self balance:app] == 2 * WLFunding); }), @"wallet balance %lld", [self balance:app]);
    [self turnOnAdvanced:app];

    // Settings → Signers → Pair a Ledger
    [app.tabBars.buttons[@"Settings"] tap];
    WLTap(self, app, @"signersButton");
    WLTap(self, app, @"signersPairLedgerButton");
    WLType(self, app, @"ledgerNameField", @"Nano X");
    WLTap(self, app, @"ledgerPairButton");
    XCUIElement *paired = app.buttons[@"Nano X"];
    XCTAssertTrue([paired waitForExistenceWithTimeout:60], @"pairing did not file the Ledger");
    WLShot(self, app, @"19-signers-paired");

    // the builder: this phone and the Ledger, any 2 of 2; the Ledger approves it
    [app.tabBars.buttons[@"Wallet"] tap];
    WLTap(self, app, @"multisigBuildButton");
    WLType(self, app, @"multisigBuildNameField", @"Ledger savings");
    WLTap(self, app, @"multisigBuildAddMemberButton");
    XCUIElement *pick = app.buttons[@"Nano X"];
    XCTAssertTrue([pick waitForExistenceWithTimeout:10], @"the picker does not offer the Ledger");
    [pick tap];
    XCTAssertTrue([[self text:app beginningWith:@"Members · 2"] waitForExistenceWithTimeout:10]);
    WLTap(self, app, @"multisigBuildCreateButton");
    XCTAssertTrue([WLElement(app, @"multisigBuildLedgerRegistered") waitForExistenceWithTimeout:60], @"the Ledger did not register the account");
    XCUIElement *created = WLElement(app, @"multisigCreatedDescriptor");
    XCTAssertTrue(WLScrollTo(app, created));
    NSString *descriptor = WLText(created);
    NSString *accountID = WLAccountID(descriptor);
    WLTap(self, app, @"multisigOpenAccountButton");
    XCUIElement *policy = WLElement(app, @"multisigPolicy");
    XCTAssertTrue([policy waitForExistenceWithTimeout:20]);
    XCTAssertEqualObjects(WLText(policy), @"2 of 2");

    // the Ledger derives the address the phone shows, and so does Core from the account's descriptor
    XCUIElement *shown = WLElement(app, @"multisigReceiveAddress");
    XCTAssertTrue([shown waitForExistenceWithTimeout:20]);
    NSString *address = WLText(shown);
    WLTap(self, app, @"ledgerVerifyButton");
    XCUIElement *verified = WLElement(app, @"ledgerVerifyResult");
    XCTAssertTrue([verified waitForExistenceWithTimeout:60], @"the Ledger did not answer");
    XCTAssertTrue([WLText(verified) hasPrefix:@"The Ledger derived this same address."], @"%@", WLText(verified));
    // the page shares its descriptor rather than printing it; the builder showed the same one
    XCTAssertTrue(WLScrollTo(app, WLElement(app, @"multisigShareButton")), @"the account page has no Share with co-signers");
    XCTAssertEqualObjects(WLDeriveAddress(descriptor, 0), address, @"the account's first address is not Core's");
    WLShot(self, app, @"20-ledger-verified");

    // the wallet pays the account: Send, From the wallet
    [app.tabBars.buttons[@"Send"] tap];
    WLTap(self, app, @"sendFromWallet");
    [self setClipboard:address];
    WLTap(self, app, @"pasteDestinationButton");
    WLType(self, app, @"amountField", [NSString stringWithFormat:@"%lld", WLFunding]);
    WLTap(self, app, @"reviewButton");
    XCUIElement *sendButton = WLElement(app, @"sendButton");
    XCTAssertTrue([sendButton waitForExistenceWithTimeout:30], @"the wallet's review did not open");
    NSSet *beforeFunding = host.mempool;
    [sendButton tap];
    NSString *funding = [self newMempoolTransaction:beforeFunding within:60];
    XCTAssertNotNil(funding, @"the wallet's payment to the account never reached the node");
    [host mine:1];
    XCTAssertTrue([WLElement(app, @"broadcastConfirmed") waitForExistenceWithTimeout:90], @"the transfer did not confirm");
    WLTap(self, app, @"newPaymentButton");
    [app.tabBars.buttons[@"Wallet"] tap];
    XCUIElement *balance = WLElement(app, @"multisigBalance");
    XCTAssertTrue(WLPoll(90, 1, ^{ return (BOOL)(WLDigits(WLText(balance)) == WLFunding); }),
                  @"the account did not find %@ (balance %@)", funding, WLText(balance));
    [self backToWalletList:app];
    XCUIElement *transfer = WLElement(app, [@"historyPayment-" stringByAppendingString:funding]);
    XCTAssertTrue([transfer waitForExistenceWithTimeout:30] && WLScrollTo(app, transfer), @"no Transactions row for the transfer");
    XCTAssertEqualObjects(transfer.label, @"Moved to Ledger savings", @"the transfer is not one row: %@", transfer.label);
    WLShot(self, app, @"20b-ledger-transfer-row");

    NSString *destination = host.bankAddress;
    [self sendFromAccount:app account:accountID to:destination sats:WLPayment needs:@"needs 2 of 2"];
    XCUIElement *count = WLElement(app, @"multisigSignatureCount");
    XCTAssertTrue(WLPoll(60, 0.3, ^{ return [WLText(count) isEqualToString:@"1 of 2"]; }), @"after the phone: %@", WLText(count));
    WLTap(self, app, @"ledgerSignButton");
    XCTAssertTrue(WLPoll(60, 0.3, ^{ return [WLText(count) isEqualToString:@"2 of 2"]; }), @"after the Ledger: %@", WLText(count));
    WLShot(self, app, @"21-ledger-signed");

    NSSet *before = host.mempool;
    WLTap(self, app, @"multisigBroadcastButton");
    XCTAssertTrue([WLElement(app, @"broadcastPending") waitForExistenceWithTimeout:30], @"the receipt did not open");
    NSString *txid = [self newMempoolTransaction:before within:30];
    XCTAssertNotNil(txid, @"Core did not accept the Ledger-signed payment");
    NSDictionary *input = [self spendingInput:txid];
    XCTAssertEqualObjects(input[@"txid"], funding);
    NSArray *witness = input[@"txinwitness"];
    XCTAssertEqual(witness.count, 4u, @"two signatures, the leaf script and the control block");
    XCTAssertEqualObjects(WLWitnessSizes(witness, 2), (@[@128, @128]), @"the phone's and the Ledger's signatures");
    [host mine:1];
    XCTAssertTrue([WLElement(app, @"broadcastConfirmed") waitForExistenceWithTimeout:90], @"the receipt did not see it confirm");
    NSDictionary *tip = [host cliJSON:@[@"getblock", [host cli:@[@"getbestblockhash"]]]];
    XCTAssertTrue([tip[@"tx"] containsObject:txid], @"the payment was not mined");
    WLShot(self, app, @"22-ledger-confirmed");
    // one confirmed row, named with the account
    [app.tabBars.buttons[@"Wallet"] tap];
    XCUIElement *row = WLElement(app, [@"historyPayment-" stringByAppendingString:txid]);
    XCTAssertTrue([row waitForExistenceWithTimeout:60] && WLScrollTo(app, row), @"the spend is missing from Transactions");
    XCTAssertTrue(WLElement(app, [@"paymentAccount-" stringByAppendingString:txid]).exists, @"the row does not name the account");
    WLShot(self, app, @"23-ledger-transactions");
}

/// The census list the build ships (project.yml bundles build/census/peers.json; CensusCatalog.bundled
/// reads it beside the executable): Advanced mode's Settings on mainnet show its date and count, not the
/// sentence for a build without one.
- (void)testShippedCensus {
    XCUIApplication *app = [self launch:@"census" extra:@{@"WINNOW_E2E_NETWORK": @"mainnet", @"WINNOW_E2E_ADVANCED": @"1"}];
    [self createWallet:app];
    XCUIElement *settings = app.tabBars.buttons[@"Settings"];
    XCTAssertTrue([settings waitForExistenceWithTimeout:15]);
    [settings tap];
    XCUIElement *census = WLElement(app, @"censusCatalogText");
    XCTAssertTrue([census waitForExistenceWithTimeout:20] && WLScrollTo(app, census), @"Settings show no census line");
    NSString *line = WLText(census);
    NSRegularExpression *shipped = [NSRegularExpression regularExpressionWithPattern:@"^Observed \\d{4}-\\d{2}-\\d{2}: \\d+ candidates\\.$" options:0 error:nil];
    XCTAssertNotNil([shipped firstMatchInString:line options:0 range:NSMakeRange(0, line.length)], @"census line: %@", line);
    XCTAssertGreaterThan(WLDigits([line substringFromIndex:[line rangeOfString:@": "].location]), 100);
    WLShot(self, app, @"30-settings-census");

    // the plain texts (PORT.md, deliberate departures, user 2026-10-28): Settings' Backup section, the
    // backup file sheet, the iCloud sheet, the Wallet tab's multisig section and Join
    XCUIElement *backupFile = WLElement(app, @"exportBundleButton");
    XCTAssertTrue([backupFile waitForExistenceWithTimeout:10] && WLScrollTo(app, backupFile));
    XCTAssertEqualObjects(backupFile.label, @"Save a backup file");
    XCTAssertTrue(WLElement(app, @"cloudBackupRowStatus").exists, @"the iCloud row shows no status");
    WLShot(self, app, @"31-settings-backup");
    [backupFile tap];
    XCUIElement *explanation = WLElement(app, @"exportExplanation");
    XCTAssertTrue([explanation waitForExistenceWithTimeout:10], @"the backup file sheet did not open");
    XCTAssertTrue(app.navigationBars[@"Backup file"].exists, @"the sheet is not titled Backup file");
    WLShot(self, app, @"32-backup-file-sheet");
    [app.buttons[@"Close"] tap];
    XCTAssertTrue([backupFile waitForExistenceWithTimeout:10]);
    XCUIElement *cloud = app.buttons[@"iCloud backup"];
    XCTAssertTrue(WLScrollTo(app, cloud));
    [cloud tap];
    XCTAssertTrue([WLElement(app, @"automaticCloudBackupToggle") waitForExistenceWithTimeout:10], @"the iCloud sheet did not open");
    WLShot(self, app, @"33-icloud-sheet");
    [app.buttons[@"Close"] tap];
    [app.tabBars.buttons[@"Wallet"] tap];
    XCUIElement *join = WLElement(app, @"multisigAddButton");
    XCTAssertTrue([join waitForExistenceWithTimeout:10] && WLScrollTo(app, join));
    XCTAssertEqualObjects(join.label, @"Join an account");
    XCTAssertEqualObjects(WLElement(app, @"multisigBuildButton").label, @"Create an account");
    WLShot(self, app, @"34-wallet-multisig");
    [join tap];
    XCTAssertTrue([app.navigationBars[@"Join an account"] waitForExistenceWithTimeout:10], @"Join is not titled Join an account");
    WLShot(self, app, @"35-join");
}

/// Pays a BIP352 silent payment code (upstream's silentPaymentJourney). Core has no BIP352, so the receiver
/// is backend-test's, written from the BIP's receiving side: the transaction the node accepts must pay the
/// one output that receiver finds, the review must say the address is derived, and the receipt must show
/// that output's address.
- (void)testSilentPaymentSend {
    WLHost *host = WLHost.shared;
    NSString *code = host.silentPaymentCode;
    XCTAssertTrue([code hasPrefix:@"tsp1"], @"not a test-network code: %@", code);
    XCUIApplication *app = [self launch:@"silent" extra:@{}];
    [self createWallet:app];
    NSString *address = [self receiveAddress:app];
    WLTap(self, app, @"closeReceiveButton");
    [host fund:address sats:WLFunding];
    XCTAssertTrue(WLPoll(90, 1, ^{ return (BOOL)([self balance:app] == WLFunding); }), @"balance %lld", [self balance:app]);

    [self setClipboard:code];
    WLTap(self, app, @"openSendButton");
    WLTap(self, app, @"pasteDestinationButton");
    WLType(self, app, @"amountField", [NSString stringWithFormat:@"%lld", WLSilentPayment]);
    WLTap(self, app, @"reviewButton");
    XCUIElement *send = WLElement(app, @"sendButton");
    XCTAssertTrue([send waitForExistenceWithTimeout:30], @"the silent payment review did not open");
    XCTAssertEqualObjects(WLText(WLElement(app, @"reviewDestination")), code);
    XCTAssertTrue(WLElement(app, @"silentPaymentNote").exists, @"the review does not say the address is derived");
    XCTAssertEqual(WLDigits(WLText(WLElement(app, @"reviewAmount"))), WLSilentPayment);
    WLShot(self, app, @"40-silent-review");

    NSSet *before = host.mempool;
    WLTap(self, app, @"sendButton");
    NSString *txid = [self newMempoolTransaction:before within:60];
    XCTAssertNotNil(txid, @"the node never received the silent payment");
    NSString *expected = [host silentPaymentExpectedScript:txid];
    NSString *paidAddress = nil;
    for (NSDictionary *output in [host transaction:txid][@"vout"])
        if ([output[@"scriptPubKey"][@"hex"] isEqualToString:expected] && llround([output[@"value"] doubleValue] * 1e8) == WLSilentPayment)
            paidAddress = output[@"scriptPubKey"][@"address"];
    XCTAssertNotNil(paidAddress, @"the transaction pays no output the code's holder would find (%@)", expected);
    XCUIElement *derived = WLElement(app, @"derivedOutputAddress");
    XCTAssertTrue([derived waitForExistenceWithTimeout:20] && WLScrollTo(app, derived), @"the receipt does not show where the code was paid");
    XCTAssertEqualObjects(WLText(derived), paidAddress);
    [host mine:1];
    XCTAssertTrue([WLElement(app, @"broadcastConfirmed") waitForExistenceWithTimeout:90], @"the receipt did not see it confirm");
    WLShot(self, app, @"41-silent-confirmed");
}

@end
