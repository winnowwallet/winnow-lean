"""Unit tests for scripts/prepare-journey-media: python3 -m unittest discover -s scripts/tests

The evidence is LeanNative's export-evidence (the pinned package's, as the script loads it), faked at its
xcresulttool boundary; these tests hold the website's layout and manifest, and what is published."""
import argparse
import hashlib
import importlib.machinery
import importlib.util
import json
from pathlib import Path
import shutil
import struct
import subprocess
import tempfile
import unittest
from unittest import mock
import zlib

loader = importlib.machinery.SourceFileLoader(
    "prepare_journey_media", str(Path(__file__).resolve().parents[1] / "prepare-journey-media"))
spec = importlib.util.spec_from_loader(loader.name, loader)
media = importlib.util.module_from_spec(spec)
loader.exec_module(media)
exporter = media.load_exporter()

SHA = "0123456789abcdef0123456789abcdef01234567"
RUN = "https://github.com/winnowwallet/winnow-lean/actions/runs/42"
TESTS = [("testCreateReceiveSendConfirm", "passed", "47.100"), ("testSilentPaymentSend", "passed", "40.789")]


def png(width, height, salt=b""):
    def chunk(kind, data):
        return struct.pack(">I", len(data)) + kind + data + struct.pack(">I", zlib.crc32(kind + data))
    raw = b"".join(b"\x00" + bytes(width * 3) for _ in range(height))
    return (exporter.PNG_SIGNATURE + chunk(b"IHDR", struct.pack(">IIBBBBB", width, height, 8, 2, 0, 0, 0))
            + chunk(b"tEXt", b"salt\x00" + salt) + chunk(b"IDAT", zlib.compress(raw)) + chunk(b"IEND", b""))


def box(kind, payload):
    return struct.pack(">I4s", 8 + len(payload), kind) + payload


def mp4(width, height, seconds, padding=0):
    """A minimal MP4: ftyp, a moov with mvhd and one video track's tkhd, and an mdat of `padding` bytes."""
    mvhd = box(b"mvhd", bytes(4) + bytes(8) + struct.pack(">II", 1000, int(seconds * 1000)) + bytes(80))
    tkhd = box(b"tkhd", bytes(4) + bytes(72) + struct.pack(">II", width << 16, height << 16))
    return (box(b"ftyp", b"isom" + bytes(4)) + box(b"moov", mvhd + box(b"trak", tkhd))
            + box(b"mdat", bytes(padding)))


def log(tests, succeeded=True):
    lines = ["Test Suite 'WinnowLeanUITests' started"]
    for name, result, seconds in tests:
        lines += [f"Test Case '-[WinnowLeanUITests {name}]' started.",
                  f"Test Case '-[WinnowLeanUITests {name}]' {result} ({seconds} seconds)."]
    total = sum(float(s) for _, _, s in tests)
    failures = sum(1 for _, r, _ in tests if r == "failed")
    lines.append(f"\t Executed {len(tests)} tests, with {failures} failures (0 unexpected) in {total:.3f} "
                 f"({total + 0.02:.3f}) seconds")
    lines.append("** TEST SUCCEEDED **" if succeeded else "** TEST FAILED **")
    return "\n".join(lines) + "\n"


class PrepareTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.base = Path(temporary.name)
        self.journey = self.base / "journey"
        (self.journey / "screenshots").mkdir(parents=True)
        (self.journey / "journey.xcresult").mkdir()
        self.out = self.base / "media"
        self.shots = {"01-onboarding": png(4, 8, b"silent"), "03-receive": png(4, 8), "40-silent-review": png(4, 8, b"r")}
        for name, data in self.shots.items():
            (self.journey / "screenshots" / f"{name}.png").write_bytes(data)
        (self.journey / "xcodebuild.log").write_text(log(TESTS))
        (self.journey / "device.json").write_text(json.dumps({
            "name": "iPhone 17 Pro", "type": "com.apple.CoreSimulator.SimDeviceType.iPhone-17-Pro",
            "runtime": "com.apple.CoreSimulator.SimRuntime.iOS-26-5", "os": "iOS 26.5"}))
        (self.journey / "run.json").write_text(json.dumps({
            "schema": 1, "name": "journey", "scheme": "WinnowLean", "platform": "iOS Simulator",
            "source": {"revision": SHA, "recorded_by": "git", "dirty": False},
            "ci": {"server": "https://github.com", "repository": "winnowwallet/winnow-lean", "run_id": "42",
                   "run_attempt": "1", "ref": "refs/heads/main"}}))
        # no ffmpeg unless a test asks for it; xcresulttool is the fake below
        self.tools = set()
        real_which = shutil.which
        self.patch(exporter.shutil, "which",
                   lambda name: "/usr/bin/xcrun" if name == "xcrun" else (real_which(name) if name in self.tools else None))
        self.bundle(TESTS)
        self.attachments([("testCreateReceiveSendConfirm", n, 1.0 + i, d) for i, (n, d) in enumerate(self.shots.items())])
        self.patch(exporter, "xcresulttool", self.xcresulttool)
        # what the script reads from the environment, as outside Actions
        environment = mock.patch.dict(media.os.environ)
        environment.start()
        self.addCleanup(environment.stop)
        for key in ("GITHUB_HEAD_REF", "LEANNATIVE_EXPORT_EVIDENCE"):
            media.os.environ.pop(key, None)

    def patch(self, target, name, value):
        patcher = mock.patch.object(target, name, value)
        patcher.start()
        self.addCleanup(patcher.stop)

    def bundle(self, tests, device="iPhone 17 Pro"):
        self.results = {"devices": [{"modelName": device, "osVersion": "26.5", "platform": "iOS Simulator"}],
                        "testNodes": [{"nodeType": "Test Plan", "children": [{"nodeType": "Test Suite",
                                       "name": "WinnowLeanUITests", "children": [
                                           {"nodeType": "Test Case", "name": name, "result": result.capitalize(),
                                            "nodeIdentifier": f"WinnowLeanUITests/{name}",
                                            "durationInSeconds": float(seconds)} for name, result, seconds in tests]}]}]}

    def attachments(self, captures):
        """captures: [(test, name, timestamp, bytes)] as the result bundle would export them."""
        self.captures = captures

    def xcresulttool(self, *arguments):
        if arguments[:3] == ("get", "test-results", "tests"):
            return json.dumps(self.results) if self.results is not None else None
        if arguments[:2] == ("export", "attachments"):
            if self.captures is None:
                return None
            into = Path(arguments[arguments.index("--output-path") + 1])
            entries = {}
            for index, (test, name, timestamp, data) in enumerate(self.captures):
                file = f"{index:08X}-0000-0000-0000-000000000000.png"
                (into / file).write_bytes(data)
                entries.setdefault(test, []).append({
                    "exportedFileName": file, "timestamp": timestamp,
                    "suggestedHumanReadableName": f"{name}_0_{index:08X}-AAAA-BBBB-CCCC-DDDDDDDDDDDD.png"})
            (into / "manifest.json").write_text(json.dumps(
                [{"testIdentifier": f"WinnowLeanUITests/{t}()", "attachments": a} for t, a in entries.items()]))
            return ""
        raise AssertionError(arguments)

    def run_prepare(self, **overrides):
        values = dict(sha=None, run_url=None, branch=None, network="regtest")
        values.update(overrides)
        return media.prepare(self.journey, self.out, argparse.Namespace(**values), exporter=exporter)

    def manifest(self):
        return json.loads((self.out / media.MANIFEST).read_text())

    def test_a_run_writes_a_version_2_manifest(self):
        (self.journey / "journey.mp4").write_bytes(mp4(1206, 2622, 12.5, padding=1000))
        self.run_prepare()
        evidence = self.manifest()
        self.assertEqual(evidence["version"], 2)
        self.assertEqual((evidence["source_sha"], evidence["run_url"], evidence["branch"], evidence["network"]),
                         (SHA, RUN, "main", "regtest"))
        self.assertEqual(evidence["test"], "WinnowLeanUITests")
        self.assertEqual(evidence["result"], "passed")
        self.assertAlmostEqual(evidence["test_seconds"], 87.889)
        self.assertEqual(evidence["tests"], [{"name": n, "result": r, "seconds": float(s)} for n, r, s in TESTS])
        self.assertEqual(evidence["device"], {"name": "iPhone 17 Pro", "os": "iOS 26.5",
                                              "type": "com.apple.CoreSimulator.SimDeviceType.iPhone-17-Pro"})
        self.assertEqual([s["name"] for s in evidence["screenshots"]], sorted(self.shots))
        for shot in evidence["screenshots"]:
            data = (self.out / "screenshots" / f"{shot['name']}.png").read_bytes()
            self.assertEqual(data, self.shots[shot["name"]])
            self.assertEqual(shot["sha256"], hashlib.sha256(data).hexdigest())
            self.assertEqual((shot["width"], shot["height"]), (4, 8))
            self.assertEqual(shot["test"], "testCreateReceiveSendConfirm")
        # no ffmpeg: a recording under 25 MiB is copied, its size and duration read from the MP4 itself
        video = evidence["video"]
        self.assertEqual((video["width"], video["height"], video["duration_seconds"]), (1206, 2622, 12.5))
        self.assertEqual(video["sha256"], hashlib.sha256((self.out / media.VIDEO).read_bytes()).hexdigest())
        self.assertEqual(video["bytes"], (self.out / media.VIDEO).stat().st_size)
        self.assertNotIn("video_omitted", evidence)
        # the website's layout, nothing else
        self.assertEqual(sorted(p.relative_to(self.out).as_posix() for p in self.out.rglob("*") if p.is_file()),
                         sorted([media.MANIFEST, media.VIDEO] + [f"screenshots/{n}.png" for n in self.shots]))

    def test_a_failed_test_fails_the_run(self):
        failed = TESTS + [("testShippedCensus", "failed", "3.0")]
        (self.journey / "xcodebuild.log").write_text(log(failed, False))
        self.bundle(failed)
        with self.assertRaisesRegex(media.Failure, r"not every test passed \(failed\): failed: testShippedCensus"):
            self.run_prepare()
        self.assertFalse((self.out / media.MANIFEST).exists())

    def test_a_log_without_success_is_not_published(self):
        (self.journey / "xcodebuild.log").write_text(log(TESTS).replace("** TEST SUCCEEDED **", ""))
        with self.assertRaisesRegex(media.Failure, r"\(incomplete\).*TEST SUCCEEDED"):
            self.run_prepare()

    def test_a_skipped_test_is_not_published(self):
        skipped = TESTS + [("testLedger", "skipped", "0.0")]
        (self.journey / "xcodebuild.log").write_text(log(skipped))
        self.bundle(skipped)
        with self.assertRaisesRegex(media.Failure, r"\(skipped\)"):
            self.run_prepare()

    def test_an_invalid_screenshot_fails(self):
        self.attachments([("testCreateReceiveSendConfirm", "03-receive", 1.0, b"not a png")])
        (self.journey / "screenshots/03-receive.png").write_bytes(b"not a png")
        for name in ("01-onboarding", "40-silent-review"):
            (self.journey / "screenshots" / f"{name}.png").unlink()
        with self.assertRaisesRegex(media.Failure, "03-receive.png: not a PNG"):
            self.run_prepare()

    def test_a_run_without_its_result_bundle_results_fails(self):
        self.results = None
        with self.assertRaisesRegex(media.Failure, "could not be read"):
            self.run_prepare()

    def test_a_run_whose_attachments_cannot_be_exported_fails(self):
        self.captures = None
        with self.assertRaisesRegex(media.Failure, "attachments could not be exported"):
            self.run_prepare()

    def test_media_output_must_be_empty(self):
        self.out.mkdir()
        (self.out / "old").write_text("x")
        with self.assertRaisesRegex(media.Failure, "not empty"):
            self.run_prepare()

    def test_an_oversized_recording_without_ffmpeg_is_omitted_and_said_so(self):
        recording = self.journey / "journey.mp4"
        recording.write_bytes(mp4(1206, 2622, 600))
        with recording.open("ab") as tail:
            tail.truncate(media.MAX_BYTES + 1)
        self.run_prepare()
        evidence = self.manifest()
        self.assertIsNone(evidence["video"])
        self.assertIn("exceeds", evidence["video_omitted"])
        self.assertEqual(evidence["original_video"]["bytes"], media.MAX_BYTES + 1)
        self.assertFalse((self.out / media.VIDEO).exists())

    def test_a_missing_recording_is_omitted_and_said_so(self):
        self.run_prepare()
        self.assertIn("no screen recording", self.manifest()["video_omitted"])

    def test_each_screenshot_is_the_first_capture_and_attributed_to_its_test(self):
        first = png(4, 8, b"create")
        self.attachments([
            ("testCreateReceiveSendConfirm", "01-onboarding", 10.0, first),
            ("testCreateReceiveSendConfirm", "03-receive", 11.0, self.shots["03-receive"]),
            ("testSilentPaymentSend", "01-onboarding", 50.0, self.shots["01-onboarding"]),
            ("testSilentPaymentSend", "40-silent-review", 51.0, self.shots["40-silent-review"]),
        ])
        self.run_prepare()
        owners = {s["name"]: s["test"] for s in self.manifest()["screenshots"]}
        self.assertEqual(owners, {"01-onboarding": "testCreateReceiveSendConfirm",
                                  "03-receive": "testCreateReceiveSendConfirm",
                                  "40-silent-review": "testSilentPaymentSend"})
        # the earlier capture is published, not the later test's file left on disk
        self.assertEqual((self.out / "screenshots/01-onboarding.png").read_bytes(), first)

    def test_a_screenshot_no_test_attached_fails(self):
        self.attachments([("testCreateReceiveSendConfirm", "01-onboarding", 1.0, self.shots["01-onboarding"])])
        with self.assertRaisesRegex(media.Failure, "no test attached: 03-receive, 40-silent-review"):
            self.run_prepare()

    def test_a_screenshot_differing_from_every_capture_fails(self):
        self.attachments([("testCreateReceiveSendConfirm", n, 1.0, png(4, 8, b"other")) for n in self.shots])
        with self.assertRaisesRegex(media.Failure, "matches none"):
            self.run_prepare()

    def test_a_screenshot_name_the_website_cannot_take_fails(self):
        self.attachments([("testCreateReceiveSendConfirm", "Receive_Screen", 1.0, png(4, 8))])
        shutil.rmtree(self.journey / "screenshots")
        with self.assertRaisesRegex(media.Failure, "lowercase letters, digits and hyphens: Receive_Screen"):
            self.run_prepare()

    def test_the_log_and_the_bundle_must_agree(self):
        self.bundle([TESTS[0]])
        with self.assertRaisesRegex(media.Failure, r"\(contradictory\).*disagree"):
            self.run_prepare()

    def test_the_bundle_can_fail_a_test_the_log_lost(self):
        (self.journey / "xcodebuild.log").write_text("** TEST SUCCEEDED **\n")
        self.bundle([TESTS[0], ("testSilentPaymentSend", "failed", "1.0")])
        with self.assertRaisesRegex(media.Failure, "testSilentPaymentSend"):
            self.run_prepare()

    def test_the_simulator_must_be_the_one_ui_tests_chose(self):
        self.bundle(TESTS, device="iPhone 18 Pro")
        with self.assertRaisesRegex(media.Failure, "chose iPhone 17 Pro but the tests ran on iPhone 18 Pro"):
            self.run_prepare()

    def test_the_tested_commit_is_the_one_recorded_never_this_checkout(self):
        self.run_prepare(sha=SHA)
        self.assertEqual(self.manifest()["source_sha"], SHA)
        self.out = self.base / "media2"
        with self.assertRaisesRegex(media.Failure, "is not the commit the journeys ran at"):
            self.run_prepare(sha="fedcba9876543210fedcba9876543210fedcba98")
        run = json.loads((self.journey / "run.json").read_text())
        run["source"] = {"revision": None}
        (self.journey / "run.json").write_text(json.dumps(run))
        with self.assertRaisesRegex(media.Failure, "recorded no tested commit"):
            self.run_prepare(sha=SHA)

    def test_identity_needs_a_full_sha_and_a_run_url(self):
        run = json.loads((self.journey / "run.json").read_text())
        with self.assertRaisesRegex(media.Failure, "full SHA"):
            media.identity(argparse.Namespace(sha="abc", run_url=None, branch=None), run)
        with self.assertRaisesRegex(media.Failure, "run URL"):
            media.identity(argparse.Namespace(sha=SHA, run_url="https://example.com/x", branch="main"), run)

    @unittest.skipUnless(shutil.which("ffmpeg") and shutil.which("ffprobe"), "needs ffmpeg")
    def test_ffmpeg_transcodes_to_at_most_720_wide(self):
        self.tools.update({"ffmpeg", "ffprobe"})
        subprocess.run(["ffmpeg", "-loglevel", "error", "-f", "lavfi", "-i", "testsrc=size=1206x2622:rate=30",
                        "-t", "2", "-c:v", "libx264", "-pix_fmt", "yuv420p", str(self.journey / "journey.mp4")],
                       check=True)
        self.run_prepare()
        video = self.manifest()["video"]
        self.assertEqual((video["width"], video["codec"]), (720, "h264"))
        self.assertAlmostEqual(video["duration_seconds"], 2.0, delta=0.5)
        self.assertEqual(self.manifest()["original_video"]["width"], 1206)


if __name__ == "__main__":
    unittest.main()
