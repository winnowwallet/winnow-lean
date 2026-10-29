#import "WLTest.h"
#import "WLHost.h"

XCUIElement *WLElement(XCUIApplication *app, NSString *identifier) {
    return [[app descendantsMatchingType:XCUIElementTypeAny] matchingIdentifier:identifier].firstMatch;
}

BOOL WLPoll(NSTimeInterval timeout, NSTimeInterval interval, BOOL (^condition)(void)) {
    NSDate *end = [NSDate dateWithTimeIntervalSinceNow:timeout];
    do {
        if (condition()) return YES;
        [NSRunLoop.currentRunLoop runUntilDate:[NSDate dateWithTimeIntervalSinceNow:interval]];
    } while (end.timeIntervalSinceNow > 0);
    return condition();
}

NSString *WLText(XCUIElement *element) {
    NSString *text = element.label.length ? element.label : ([element.value isKindOfClass:NSString.class] ? element.value : @"");
    return [text stringByReplacingOccurrencesOfString:@"\u200B" withString:@""];
}

int64_t WLDigits(NSString *text) {
    NSString *digits = [[text componentsSeparatedByCharactersInSet:NSCharacterSet.decimalDigitCharacterSet.invertedSet]
        componentsJoinedByString:@""];
    return digits.length ? digits.longLongValue : -1;
}

BOOL WLScrollTo(XCUIApplication *app, XCUIElement *element) {
    // down the screen first, then back up past where it started: the element may be above or below
    for (int swipe = 0; swipe < 24; swipe++) {
        if (element.exists && element.hittable) return YES;
        BOOL down = swipe < 8;
        // drag in the middle of the screen: the bottom edge belongs to the home indicator
        XCUICoordinate *from = [app coordinateWithNormalizedOffset:CGVectorMake(0.5, down ? 0.7 : 0.35)];
        [from pressForDuration:0.05 thenDragToCoordinate:[app coordinateWithNormalizedOffset:CGVectorMake(0.5, down ? 0.35 : 0.7)]];
    }
    return element.exists && element.hittable;
}

void WLTap(XCTestCase *test, XCUIApplication *app, NSString *identifier) {
    XCUIElement *e = WLElement(app, identifier);
    XCTAssertTrue([e waitForExistenceWithTimeout:20], @"%@ does not appear", identifier);
    XCTAssertTrue(WLScrollTo(app, e), @"%@ cannot be scrolled into view", identifier);
    XCTAssertTrue(WLPoll(15, 0.2, ^{ return e.isEnabled; }), @"%@ stays disabled", identifier);
    [e tap];
}

void WLType(XCTestCase *test, XCUIApplication *app, NSString *identifier, NSString *text) {
    XCUIElement *field = WLElement(app, identifier);
    XCTAssertTrue([field waitForExistenceWithTimeout:20], @"%@ does not appear", identifier);
    XCTAssertTrue(WLScrollTo(app, field), @"%@ cannot be scrolled into view", identifier);
    [field tap];
    NSString *current = [field.value isKindOfClass:NSString.class] ? field.value : @"";
    if (current.length && ![current isEqualToString:field.placeholderValue]) {
        NSMutableString *delete = [NSMutableString string];
        for (NSUInteger i = 0; i < current.length; i++) [delete appendString:XCUIKeyboardKeyDelete];
        [field typeText:delete];
    }
    [field typeText:text];
    XCUIElement *done = WLElement(app, @"keyboardDone");
    if (done.exists && done.hittable) [done tap];
    else if (app.keyboards.count > 0) [app.keyboards.buttons[@"return"] tap];
}

void WLShot(XCTestCase *test, XCUIApplication *app, NSString *name) {
    XCUIScreenshot *shot = app.screenshot;
    XCTAttachment *attachment = [XCTAttachment attachmentWithScreenshot:shot];
    attachment.name = name;
    attachment.lifetime = XCTAttachmentLifetimeKeepAlways;
    [test addAttachment:attachment];
    NSString *dir = WLHost.shared.screenshotDir;
    if (dir.length) {
        [NSFileManager.defaultManager createDirectoryAtPath:dir withIntermediateDirectories:YES attributes:nil error:nil];
        [shot.PNGRepresentation writeToFile:[dir stringByAppendingPathComponent:[name stringByAppendingString:@".png"]] atomically:YES];
    }
}
