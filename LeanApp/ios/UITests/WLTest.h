// What the journeys share: finding a node by its `Html.identified` id, waiting, typing, scrolling and
// screenshots (upstream's TestHelpers.swift, for the Objective-C shell).
#import <XCTest/XCTest.h>

NS_ASSUME_NONNULL_BEGIN

/// The element with this accessibility identifier, of any type (a node's control, label or image).
XCUIElement *WLElement(XCUIApplication *app, NSString *identifier);

/// Polls `condition` every `interval` seconds until it holds or `timeout` passes.
BOOL WLPoll(NSTimeInterval timeout, NSTimeInterval interval, BOOL (^condition)(void));

/// A label's text without the zero-width spaces the shell puts into long words so they can wrap.
NSString *WLText(XCUIElement *element);

/// The digits of a text as a number ("1,000,000 sats" is 1000000); -1 when there are none.
int64_t WLDigits(NSString *text);

/// Scrolls the screen (down, then up) until the element is hittable; NO if it never is.
BOOL WLScrollTo(XCUIApplication *app, XCUIElement *element);

/// Waits for, scrolls to and taps the element with this identifier, which must be enabled.
void WLTap(XCTestCase *test, XCUIApplication *app, NSString *identifier);

/// Replaces the text of the input with this identifier and closes the keyboard.
void WLType(XCTestCase *test, XCUIApplication *app, NSString *identifier, NSString *text);

/// A screenshot attached to the test and, when the run names a directory, written there as <name>.png.
void WLShot(XCTestCase *test, XCUIApplication *app, NSString *name);

NS_ASSUME_NONNULL_END
