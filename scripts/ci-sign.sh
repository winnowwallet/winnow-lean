#!/bin/bash
# CI signing setup: write the App Store Connect API key used by xcodebuild.
#
# Xcode 13 and newer can use Apple's cloud-managed distribution certificate
# when an archive is exported with App Store Connect credentials. Do not mint
# a disposable IOS_DISTRIBUTION certificate here: those certificates persist
# after the ephemeral runner disappears and eventually exhaust the account's
# certificate limit.
# Needs env: ASC_KEY_ID, ASC_ISSUER_ID, ASC_PRIVATE_KEY (PEM contents).
set -euo pipefail
umask 077

WORK="${RUNNER_TEMP:-/tmp}/winnow-signing"
install -d -m 700 "$WORK"

printf '%s\n' "$ASC_PRIVATE_KEY" > "$WORK/AuthKey.p8"
chmod 600 "$WORK/AuthKey.p8"
echo "App Store Connect credentials prepared for cloud-managed signing"
