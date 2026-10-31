import WinnowApp.Project

/-! `ios-project`: the Xcode project's XcodeGen spec, from `WinnowApp.manifest` (WinnowApp/Project.lean).
LeanNative's framework/native/ci/build-ios runs it. -/

def main := WinnowApp.manifest.main
