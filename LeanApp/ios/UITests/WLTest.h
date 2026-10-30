// What the journeys share, over LeanNative's XCTest kit (framework/native/testkit, ELTest.h): finding a node
// by its `Html.identified` id, waiting, typing, scrolling and screenshots. The kit checks each action's
// preconditions and records a failure at the caller's line instead of acting; with continueAfterFailure off
// that ends the journey there. What is Winnow's stays here: amounts as digits, and the screenshot directory
// WLHost reads from the fixture.
#import <XCTest/XCTest.h>
#import "ELTest.h"

NS_ASSUME_NONNULL_BEGIN

static inline XCUIElement *WLElement(XCUIApplication *app, NSString *identifier) { return ELElement(app, identifier); }
static inline BOOL WLPoll(NSTimeInterval timeout, NSTimeInterval interval, BOOL (^condition)(void)) {
    return ELPoll(timeout, interval, condition);
}
static inline NSString *WLText(XCUIElement *element) { return ELText(element); }
static inline BOOL WLScrollTo(XCUIApplication *app, XCUIElement *element) { return ELScrollTo(app, element); }
// Macros, so a failure is reported at the journey's line; the last argument may hold commas (a format).
/// Waits for, scrolls to and taps the element with this identifier, which must be enabled.
#define WLTap(test, app, ...) ((void)(test), (void)ELTapAt((app), (__VA_ARGS__), @__FILE__, __LINE__))
/// Replaces the text of the input with this identifier and closes the keyboard.
#define WLType(test, app, identifier, ...) ((void)(test), (void)ELTypeAt((app), (identifier), (__VA_ARGS__), @__FILE__, __LINE__))

/// The digits of a text as a number ("1,000,000 sats" is 1000000); -1 when there are none.
int64_t WLDigits(NSString *text);

/// A screenshot attached to the test and, when the fixture names a directory (WLHost), written there as <name>.png.
#define WLShot(test, app, ...) WLShotAt((test), (app), (__VA_ARGS__), @__FILE__, __LINE__)
void WLShotAt(XCTestCase *test, XCUIApplication *app, NSString *name, NSString *file, NSUInteger line);

NS_ASSUME_NONNULL_END
