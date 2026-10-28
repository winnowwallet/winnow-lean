#import "WLHost.h"
#import <spawn.h>
#import <sys/wait.h>

@implementation WLHost

+ (instancetype)shared {
    static WLHost *host;
    static dispatch_once_t once;
    dispatch_once(&once, ^{ host = [[WLHost alloc] initFromConfiguration]; });
    return host;
}

static NSDictionary *WLReadJSON(NSString *path) {
    NSData *data = [NSData dataWithContentsOfFile:path];
    if (!data) [NSException raise:@"WLHost" format:@"cannot read %@", path];
    id json = [NSJSONSerialization JSONObjectWithData:data options:0 error:nil];
    if (![json isKindOfClass:NSDictionary.class]) [NSException raise:@"WLHost" format:@"%@ is not a JSON object", path];
    return json;
}

- (instancetype)initFromConfiguration {
    if (!(self = [super init])) return nil;
    NSDictionary *env = NSProcessInfo.processInfo.environment;
    NSString *home = env[@"SIMULATOR_HOST_HOME"] ?: NSHomeDirectory();
    NSString *configured = env[@"WINNOW_UI_CONFIG"];
    NSString *path = configured.length ? configured : [home stringByAppendingPathComponent:@".winnow-lean-ui.json"];
    NSDictionary *config = WLReadJSON(path);
    _fixtureDir = config[@"fixture"];
    _bitcoinCli = config[@"bitcoinCli"];
    if (!_bitcoinCli.length) [NSException raise:@"WLHost" format:@"%@ names no bitcoinCli", path];
    _backendTest = config[@"backendTest"] ?: @"";
    _screenshotDir = config[@"screenshots"];
    NSDictionary *fixture = WLReadJSON([_fixtureDir stringByAppendingPathComponent:@"fixture.json"]);
    _p2p = [fixture[@"p2p"] integerValue];
    _rpc = [fixture[@"rpc"] integerValue];
    _datadir = fixture[@"datadir"];
    return self;
}

static NSData *WLDrain(int fd) {
    NSMutableData *out = [NSMutableData data];
    char buffer[65536];
    for (;;) {
        ssize_t n = read(fd, buffer, sizeof buffer);
        if (n > 0) [out appendBytes:buffer length:(NSUInteger)n];
        else if (n == 0 || errno != EINTR) break;
    }
    close(fd);
    return out;
}

- (NSString *)run:(NSString *)path arguments:(NSArray<NSString *> *)arguments {
    int outPipe[2], errPipe[2];
    pipe(outPipe);
    pipe(errPipe);
    posix_spawn_file_actions_t actions;
    posix_spawn_file_actions_init(&actions);
    posix_spawn_file_actions_adddup2(&actions, outPipe[1], STDOUT_FILENO);
    posix_spawn_file_actions_adddup2(&actions, errPipe[1], STDERR_FILENO);
    posix_spawn_file_actions_addopen(&actions, STDIN_FILENO, "/dev/null", O_RDONLY, 0);
    posix_spawnattr_t attributes;
    posix_spawnattr_init(&attributes);
    // only the descriptors set up above survive into the child
    posix_spawnattr_setflags(&attributes, POSIX_SPAWN_CLOEXEC_DEFAULT);
    NSMutableArray<NSString *> *all = [NSMutableArray arrayWithObject:path];
    [all addObjectsFromArray:arguments];
    char **argv = calloc(all.count + 1, sizeof(char *));
    for (NSUInteger i = 0; i < all.count; i++) argv[i] = strdup(all[i].UTF8String);
    // the child's whole environment: the bitcoin-cli of ui.json, so backend-test talks to the node through
    // the same pinned Core as the tests
    char *envp[] = { strdup([@"WINNOW_BITCOIN_CLI=" stringByAppendingString:self.bitcoinCli].UTF8String), NULL };
    pid_t pid = 0;
    int rc = posix_spawn(&pid, path.UTF8String, &actions, &attributes, argv, envp);
    for (NSUInteger i = 0; i < all.count; i++) free(argv[i]);
    free(argv);
    free(envp[0]);
    posix_spawn_file_actions_destroy(&actions);
    posix_spawnattr_destroy(&attributes);
    close(outPipe[1]);
    close(errPipe[1]);
    if (rc != 0) {
        close(outPipe[0]);
        close(errPipe[0]);
        [NSException raise:@"WLHost" format:@"posix_spawn %@: errno %d", path, rc];
    }
    // drain both pipes at once: Core's JSON can be larger than a pipe's buffer
    __block NSData *errors;
    dispatch_group_t group = dispatch_group_create();
    int errFD = errPipe[0];
    dispatch_group_async(group, dispatch_get_global_queue(QOS_CLASS_USER_INITIATED, 0), ^{ errors = WLDrain(errFD); });
    NSData *output = WLDrain(outPipe[0]);
    dispatch_group_wait(group, DISPATCH_TIME_FOREVER);
    int status = 0;
    while (waitpid(pid, &status, 0) < 0 && errno == EINTR) {}
    NSString *text = [[[NSString alloc] initWithData:output encoding:NSUTF8StringEncoding]
        stringByTrimmingCharactersInSet:NSCharacterSet.whitespaceAndNewlineCharacterSet];
    if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) {
        NSString *err = [[NSString alloc] initWithData:errors encoding:NSUTF8StringEncoding];
        [NSException raise:@"WLHost" format:@"%@ %@ exited %d: %@", path.lastPathComponent,
            [arguments componentsJoinedByString:@" "], WIFEXITED(status) ? WEXITSTATUS(status) : -1, err];
    }
    return text ?: @"";
}

- (NSArray<NSString *> *)nodeArguments {
    return @[@"-regtest", [@"-datadir=" stringByAppendingString:self.datadir],
             [NSString stringWithFormat:@"-rpcport=%ld", (long)self.rpc]];
}

- (NSString *)cli:(NSArray<NSString *> *)arguments {
    return [self run:self.bitcoinCli arguments:[self.nodeArguments arrayByAddingObjectsFromArray:arguments]];
}

- (NSString *)wallet:(NSString *)wallet cli:(NSArray<NSString *> *)arguments {
    return [self cli:[@[[@"-rpcwallet=" stringByAppendingString:wallet]] arrayByAddingObjectsFromArray:arguments]];
}

static id WLParse(NSString *text, NSArray *arguments) {
    id json = [NSJSONSerialization JSONObjectWithData:[text dataUsingEncoding:NSUTF8StringEncoding]
                                              options:NSJSONReadingFragmentsAllowed error:nil];
    if (!json) [NSException raise:@"WLHost" format:@"bitcoin-cli %@: not JSON: %@", arguments, text];
    return json;
}

- (id)cliJSON:(NSArray<NSString *> *)arguments { return WLParse([self cli:arguments], arguments); }

- (id)wallet:(NSString *)wallet cliJSON:(NSArray<NSString *> *)arguments {
    return WLParse([self wallet:wallet cli:arguments], arguments);
}

- (NSSet<NSString *> *)mempool { return [NSSet setWithArray:[self cliJSON:@[@"getrawmempool"]]]; }

- (NSString *)bankAddress { return [self wallet:@"w" cli:@[@"getnewaddress"]]; }

- (void)mine:(NSInteger)blocks {
    [self cli:@[@"generatetoaddress", [NSString stringWithFormat:@"%ld", (long)blocks], self.bankAddress]];
}

- (NSString *)fund:(NSString *)address sats:(int64_t)sats {
    NSString *btc = [NSString stringWithFormat:@"%lld.%08lld", sats / 100000000, sats % 100000000];
    NSString *txid = [self wallet:@"w" cli:@[@"sendtoaddress", address, btc]];
    [self mine:1];
    return txid;
}

- (NSDictionary *)transaction:(NSString *)txid { return [self cliJSON:@[@"getrawtransaction", txid, @"true"]]; }

- (NSString *)scriptPubKey:(NSString *)address {
    return [self cliJSON:@[@"validateaddress", address]][@"scriptPubKey"];
}

- (NSString *)silentPaymentCode { return [self run:self.backendTest arguments:@[@"--sp-code"]]; }

- (NSString *)silentPaymentExpectedScript:(NSString *)txid {
    return [self run:self.backendTest arguments:@[@"--sp-expected", self.datadir,
                                                  [NSString stringWithFormat:@"%ld", (long)self.rpc], txid]];
}

@end
