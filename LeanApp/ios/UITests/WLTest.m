#import "WLTest.h"
#import "WLHost.h"

int64_t WLDigits(NSString *text) {
    NSString *digits = [[text componentsSeparatedByCharactersInSet:NSCharacterSet.decimalDigitCharacterSet.invertedSet]
        componentsJoinedByString:@""];
    return digits.length ? digits.longLongValue : -1;
}

void WLShotAt(XCTestCase *test, XCUIApplication *app, NSString *name, NSString *file, NSUInteger line) {
    NSString *dir = WLHost.shared.screenshotDir;
    ELShotAt(test, app, name, dir.length ? [ELScreenshots inDirectory:dir] : [ELScreenshots attachmentsOnly], file, line);
}
