#import "WLCoreSigner.h"
#import "WLHost.h"

NSString *WLWithChecksum(NSString *descriptor) {
    NSString *body = [descriptor componentsSeparatedByString:@"#"].firstObject;
    NSDictionary *info = [WLHost.shared cliJSON:@[@"getdescriptorinfo", body]];
    return [NSString stringWithFormat:@"%@#%@", body, info[@"checksum"]];
}

NSString *WLDeriveAddress(NSString *descriptor, NSInteger index) {
    NSString *body = [descriptor componentsSeparatedByString:@"#"].firstObject;
    NSRegularExpression *multipath = [NSRegularExpression regularExpressionWithPattern:@"<(\\d+);\\d+>" options:0 error:nil];
    body = [multipath stringByReplacingMatchesInString:body options:0 range:NSMakeRange(0, body.length) withTemplate:@"$1"];
    NSString *range = [NSString stringWithFormat:@"[%ld,%ld]", (long)index, (long)index];
    NSArray *addresses = [WLHost.shared cliJSON:@[@"deriveaddresses", WLWithChecksum(body), range]];
    return addresses.firstObject;
}

@implementation WLCoreSigner {
    NSString *_fingerprint;
    NSString *_tpub;
    NSString *_tprv;
}

/// The Taproot (BIP86) descriptor of the wallet's receive branch, public or private.
- (NSString *)taprootDescriptor:(BOOL)private {
    NSDictionary *list = [WLHost.shared wallet:_wallet cliJSON:@[@"listdescriptors", private ? @"true" : @"false"]];
    for (NSDictionary *d in list[@"descriptors"]) {
        NSString *desc = d[@"desc"];
        if ([desc hasPrefix:@"tr("] && ![d[@"internal"] boolValue]) return desc;
    }
    [NSException raise:@"WLCoreSigner" format:@"%@ has no Taproot descriptor", _wallet];
    return @"";
}

- (instancetype)initWithWallet:(NSString *)name {
    if (!(self = [super init])) return nil;
    _wallet = [name copy];
    [WLHost.shared cli:@[@"-named", @"createwallet", [@"wallet_name=" stringByAppendingString:name]]];
    // tr([fp/86h/1h/0h]tpub…/0/*)#… and tr(tprv…/86h/1h/0h/0/*)#…
    NSRegularExpression *pub = [NSRegularExpression regularExpressionWithPattern:@"^tr\\(\\[([0-9a-f]{8})/86h/1h/0h\\](tpub[1-9A-HJ-NP-Za-km-z]+)/0/\\*\\)" options:0 error:nil];
    NSString *publicDesc = [self taprootDescriptor:NO];
    NSTextCheckingResult *m = [pub firstMatchInString:publicDesc options:0 range:NSMakeRange(0, publicDesc.length)];
    if (!m) [NSException raise:@"WLCoreSigner" format:@"unexpected descriptor %@", publicDesc];
    _fingerprint = [publicDesc substringWithRange:[m rangeAtIndex:1]];
    _tpub = [publicDesc substringWithRange:[m rangeAtIndex:2]];
    NSRegularExpression *prv = [NSRegularExpression regularExpressionWithPattern:@"^tr\\((tprv[1-9A-HJ-NP-Za-km-z]+)/86h/1h/0h/0/\\*\\)" options:0 error:nil];
    NSString *privateDesc = [self taprootDescriptor:YES];
    NSTextCheckingResult *p = [prv firstMatchInString:privateDesc options:0 range:NSMakeRange(0, privateDesc.length)];
    if (!p) [NSException raise:@"WLCoreSigner" format:@"unexpected private descriptor for %@", name];
    _tprv = [privateDesc substringWithRange:[p rangeAtIndex:1]];
    _keyExpression = [NSString stringWithFormat:@"[%@/86'/1'/0']%@/<0;1>/*", _fingerprint, _tpub];
    return self;
}

- (void)importAccount:(NSString *)descriptor {
    // [fp/86'/1'/0']tpub… (or with h) becomes the master tprv and the same path
    NSString *pattern = [NSString stringWithFormat:@"\\[%@/86['h]/1['h]/0['h]\\]%@", _fingerprint, _tpub];
    NSRegularExpression *key = [NSRegularExpression regularExpressionWithPattern:pattern options:0 error:nil];
    NSString *body = [descriptor componentsSeparatedByString:@"#"].firstObject;
    NSString *template = [NSRegularExpression escapedTemplateForString:[_tprv stringByAppendingString:@"/86h/1h/0h"]];
    NSString *mine = [key stringByReplacingMatchesInString:body options:0 range:NSMakeRange(0, body.length) withTemplate:template];
    if ([mine isEqualToString:body]) [NSException raise:@"WLCoreSigner" format:@"%@'s key is not in %@", _wallet, descriptor];
    NSArray *request = @[@{@"desc": WLWithChecksum(mine), @"timestamp": @"now", @"range": @[@0, @50]}];
    NSString *json = [[NSString alloc] initWithData:[NSJSONSerialization dataWithJSONObject:request options:0 error:nil]
                                           encoding:NSUTF8StringEncoding];
    NSArray *result = [WLHost.shared wallet:_wallet cliJSON:@[@"importdescriptors", json]];
    for (NSDictionary *r in result)
        if (![r[@"success"] boolValue]) [NSException raise:@"WLCoreSigner" format:@"importdescriptors: %@", r];
}

- (NSString *)sign:(NSString *)psbt {
    NSDictionary *r = [WLHost.shared wallet:_wallet cliJSON:@[@"walletprocesspsbt", psbt, @"true", @"DEFAULT", @"true", @"false"]];
    return r[@"psbt"];
}

@end
