"""Unit tests for scripts/prepare-journey-media: python3 -m unittest discover -s scripts/tests"""
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

SHA = "0123456789abcdef0123456789abcdef01234567"
RUN = "https://github.com/winnowwallet/winnow/actions/runs/42"
TESTS = [("testCreateReceiveSendConfirm", "passed", "47.100"), ("testSilentPaymentSend", "passed", "40.789")]


def png(width, height, salt=b""):
    def chunk(kind, data):
        return struct.pack(">I", len(data)) + kind + data + struct.pack(">I", zlib.crc32(kind + data))
    raw = b"".join(b"\x00" + bytes(width * 3) for _ in range(height))
    return (media.PNG_SIGNATURE + chunk(b"IHDR", struct.pack(">IIBBBBB", width, height, 8, 2, 0, 0, 0))
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
        self.out = self.base / "media"
        self.shots = {"01-onboarding": png(4, 8, b"silent"), "03-receive": png(4, 8), "40-silent-review": png(4, 8)}
        for name, data in self.shots.items():
            (self.journey / "screenshots" / f"{name}.png").write_bytes(data)
        (self.journey / "xcodebuild.log").write_text(log(TESTS))
        (self.journey / "ui.json").write_text(json.dumps({"device": {
            "name": "iPhone 17 Pro", "type": "com.apple.CoreSimulator.SimDeviceType.iPhone-17-Pro",
            "os": "iOS 26.5"}}))
        # no xcresulttool unless a test provides one; no ffmpeg unless a test asks for it
        self.patch("xcresulttool", lambda *arguments: None)
        self.real_which = shutil.which
        self.tools = set()
        patcher = mock.patch.object(media.shutil, "which",
                                    lambda name: self.real_which(name) if name in self.tools else None)
        patcher.start()
        self.addCleanup(patcher.stop)

    def patch(self, name, value):
        patcher = mock.patch.object(media, name, value)
        patcher.start()
        self.addCleanup(patcher.stop)

    def run_prepare(self):
        return media.prepare(self.journey, self.out,
                             argparse.Namespace(sha=SHA, run_url=RUN, branch="main", network="regtest"))

    def manifest(self):
        return json.loads((self.out / media.MANIFEST).read_text())

    def test_log_only_run_writes_a_version_2_manifest(self):
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
        self.assertEqual(evidence["device"]["name"], "iPhone 17 Pro")
        self.assertEqual([s["name"] for s in evidence["screenshots"]], sorted(self.shots))
        for shot in evidence["screenshots"]:
            data = (self.out / "screenshots" / f"{shot['name']}.png").read_bytes()
            self.assertEqual(shot["sha256"], hashlib.sha256(data).hexdigest())
            self.assertEqual((shot["width"], shot["height"]), (4, 8))
            self.assertIsNone(shot["test"])
        # no ffmpeg: a recording under 25 MiB is copied, its size and duration read from the MP4 itself
        video = evidence["video"]
        self.assertEqual((video["width"], video["height"], video["duration_seconds"]), (1206, 2622, 12.5))
        self.assertEqual(video["sha256"], hashlib.sha256((self.out / media.VIDEO).read_bytes()).hexdigest())
        self.assertEqual(video["bytes"], (self.out / media.VIDEO).stat().st_size)
        self.assertNotIn("video_omitted", evidence)

    def test_a_failed_test_fails_the_run(self):
        (self.journey / "xcodebuild.log").write_text(log(TESTS + [("testShippedCensus", "failed", "3.0")], False))
        with self.assertRaisesRegex(media.Failure, "not every test passed: testShippedCensus failed"):
            self.run_prepare()

    def test_a_log_without_success_fails(self):
        (self.journey / "xcodebuild.log").write_text(log(TESTS).replace("** TEST SUCCEEDED **", ""))
        with self.assertRaisesRegex(media.Failure, "TEST SUCCEEDED"):
            self.run_prepare()

    def test_an_invalid_screenshot_fails(self):
        (self.journey / "screenshots/03-receive.png").write_bytes(b"not a png")
        with self.assertRaisesRegex(media.Failure, "03-receive.png: not a PNG"):
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
        self.assertIn("exceeds 25 MiB", evidence["video_omitted"])
        self.assertEqual(evidence["original_video"]["bytes"], media.MAX_BYTES + 1)
        self.assertFalse((self.out / media.VIDEO).exists())

    def test_a_missing_recording_is_omitted_and_said_so(self):
        self.run_prepare()
        self.assertIn("no screen recording", self.manifest()["video_omitted"])

    def bundle(self, tests, device="iPhone 17 Pro"):
        (self.journey / "journey.xcresult").mkdir(exist_ok=True)
        data = {"devices": [{"modelName": device, "osVersion": "26.5", "platform": "iOS Simulator"}],
                "testNodes": [{"nodeType": "Test Plan", "children": [{"nodeType": "Test Suite",
                               "name": "WinnowLeanUITests", "children": [
                                   {"nodeType": "Test Case", "name": name, "result": result.capitalize(),
                                    "nodeIdentifier": f"WinnowLeanUITests/{name}",
                                    "durationInSeconds": float(seconds)} for name, result, seconds in tests]}]}]}
        self.patch("bundle_results", lambda path: media.parse_bundle_results(data))

    def attachments(self, captures):
        """captures: [(test, name, timestamp, bytes)] as the result bundle would export them."""
        def export(bundle, into):
            entries = {}
            for index, (test, name, timestamp, data) in enumerate(captures):
                file = f"{index:08X}-0000-0000-0000-000000000000.png"
                (Path(into) / file).write_bytes(data)
                entries.setdefault(test, []).append({
                    "exportedFileName": file, "timestamp": timestamp,
                    "suggestedHumanReadableName": f"{name}_0_{index:08X}-AAAA-BBBB-CCCC-DDDDDDDDDDDD.png"})
            return [{"testIdentifier": f"WinnowLeanUITests/{test}", "attachments": a} for test, a in entries.items()]
        self.patch("bundle_attachments", export)

    def test_the_result_bundle_attributes_each_screenshot_to_its_first_capture(self):
        self.bundle(TESTS)
        first = png(4, 8, b"create")
        self.attachments([
            ("testCreateReceiveSendConfirm", "01-onboarding", 10.0, first),
            ("testCreateReceiveSendConfirm", "03-receive", 11.0, self.shots["03-receive"]),
            ("testSilentPaymentSend", "01-onboarding", 50.0, self.shots["01-onboarding"]),
            ("testSilentPaymentSend", "40-silent-review", 51.0, self.shots["40-silent-review"]),
        ])
        self.run_prepare()
        evidence = self.manifest()
        owners = {s["name"]: s["test"] for s in evidence["screenshots"]}
        self.assertEqual(owners, {"01-onboarding": "testCreateReceiveSendConfirm",
                                  "03-receive": "testCreateReceiveSendConfirm",
                                  "40-silent-review": "testSilentPaymentSend"})
        # the earlier capture is published, not the later test's file left on disk
        self.assertEqual((self.out / "screenshots/01-onboarding.png").read_bytes(), first)
        self.assertEqual(evidence["device"], {"name": "iPhone 17 Pro", "os": "iOS 26.5",
                                              "type": "com.apple.CoreSimulator.SimDeviceType.iPhone-17-Pro"})

    def test_a_screenshot_no_test_attached_fails(self):
        self.bundle(TESTS)
        self.attachments([("testCreateReceiveSendConfirm", "01-onboarding", 1.0, self.shots["01-onboarding"])])
        with self.assertRaisesRegex(media.Failure, "03-receive.png is not an attachment"):
            self.run_prepare()

    def test_a_screenshot_differing_from_every_capture_fails(self):
        self.bundle(TESTS)
        self.attachments([("testCreateReceiveSendConfirm", n, 1.0, png(4, 8, b"other")) for n in self.shots])
        with self.assertRaisesRegex(media.Failure, "matches none"):
            self.run_prepare()

    def test_the_log_and_the_bundle_must_agree(self):
        self.bundle([TESTS[0]])
        with self.assertRaisesRegex(media.Failure, "disagree"):
            self.run_prepare()

    def test_the_bundle_can_fail_a_test_the_log_lost(self):
        (self.journey / "xcodebuild.log").write_text("** TEST SUCCEEDED **\n")
        self.bundle([TESTS[0], ("testSilentPaymentSend", "failed", "1.0")])
        with self.assertRaisesRegex(media.Failure, "testSilentPaymentSend failed"):
            self.run_prepare()

    def test_the_simulator_must_be_the_one_ui_json_chose(self):
        self.bundle(TESTS, device="iPhone 18 Pro")
        self.attachments([("testCreateReceiveSendConfirm", n, 1.0, d) for n, d in self.shots.items()])
        with self.assertRaisesRegex(media.Failure, "chose iPhone 17 Pro but the tests ran on iPhone 18 Pro"):
            self.run_prepare()

    def test_identity_needs_a_full_sha_and_a_run_url(self):
        with self.assertRaisesRegex(media.Failure, "full SHA"):
            media.identity(argparse.Namespace(sha="abc", run_url=None, branch=None))
        with self.assertRaisesRegex(media.Failure, "run URL"):
            media.identity(argparse.Namespace(sha=SHA, run_url="https://example.com/x", branch="main"))

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
