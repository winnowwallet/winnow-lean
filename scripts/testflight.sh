#!/bin/bash
# Winnow → TestFlight pipeline (App Store Connect API).
# Prefer the hosted release/recovery/submission workflows; see scripts/README.md.
# `all` is the default and uploads a build; it is not a status or help command.
# Prereqs for `upload`/`all`: exported IPA at build/export/WinnowLean.ipa,
# API key at ~/.appstoreconnect/private_keys/AuthKey_<KEY_ID>.p8.
#
#   export ASC_KEY_ID=<key id>
#   export ASC_ISSUER_ID=<issuer uuid>   # ASC → Users and Access → Integrations
#   scripts/testflight.sh all
#
# Steps (also runnable individually): register-bundle-id, create-app, upload,
# wait-processing, notes, internal, external, status, all.
#
# App Store (never part of `all`; run by .github/workflows/appstore-submit.yml
# on a manual dispatch): appstore-status, appstore-attach, appstore-notes,
# appstore-submit. They act on one App Store version, APPSTORE_VERSION_ID
# (an explicitly selected editable record) or the version whose string
# is APPSTORE_VERSION_STRING; attach a processed build to it, set its What's
# New, and create a review submission. appstore-submit refuses to run unless
# APPSTORE_CONFIRM_SUBMIT=yes.
set -euo pipefail
cd "$(dirname "$0")/.."

KEY_ID="${ASC_KEY_ID:?set ASC_KEY_ID}"
ISSUER="${ASC_ISSUER_ID:?set ASC_ISSUER_ID}"
KEY_PATH="${ASC_KEY_PATH:-$HOME/.appstoreconnect/private_keys/AuthKey_${KEY_ID}.p8}"
BUNDLE_ID="com.btcswift.app"
APP_NAME="Winnow"
API="https://api.appstoreconnect.apple.com/v1"
PUBLIC_LINK_ID="${TESTFLIGHT_PUBLIC_LINK_ID:-83djpNE7}"
WHATS_NEW_FILE="${TESTFLIGHT_WHATS_NEW_FILE:-docs/testflight-what-to-test.txt}"
EXPECTED_BUILD_NUMBER="${TESTFLIGHT_BUILD_NUMBER:-}"
EXPECTED_MARKETING_VERSION="${TESTFLIGHT_MARKETING_VERSION:-}"
# How long to wait for an uploaded build to become visible in App Store
# Connect. This is Apple's ingest queue, not our processing wait, and it is
# routinely slower than the five minutes this used to allow — v0.2.0's upload
# succeeded and the release still failed here. Default: 30 minutes.
BUILD_WAIT_ATTEMPTS="${TESTFLIGHT_BUILD_WAIT_ATTEMPTS:-90}"
BUILD_WAIT_SECONDS="${TESTFLIGHT_BUILD_WAIT_SECONDS:-20}"
# Never default to a historical record: it may already be released.
APPSTORE_VERSION_ID="${APPSTORE_VERSION_ID:-}"
APPSTORE_VERSION_STRING="${APPSTORE_VERSION_STRING:-$EXPECTED_MARKETING_VERSION}"
APPSTORE_WHATS_NEW_FILE="${APPSTORE_WHATS_NEW_FILE:-docs/appstore-whats-new.txt}"
APPSTORE_CONFIRM_SUBMIT="${APPSTORE_CONFIRM_SUBMIT:-}"

jwt() { scripts/asc-jwt "$KEY_PATH" "$KEY_ID" "$ISSUER"; }
asc() { # asc <METHOD> <path> [json-body]
  local method="$1" path="$2" body="${3:-}"
  local args=(--fail-with-body -sS -g -X "$method" -H "Authorization: Bearer $(jwt)" -H "Content-Type: application/json")
  # App Store Connect answers 500 in bursts: 0.8.6's upload succeeded and its
  # release died on three of them in twelve minutes while the build was being
  # ingested. A read is retried (curl retries 408, 429 and 5xx on its own),
  # five tries fifteen seconds apart, inside the token's life; a write is
  # never repeated, since a 500 does not say whether it was applied.
  [ "$method" = GET ] && args+=(--retry 5 --retry-delay 15)
  [ -n "$body" ] && args+=(-d "$body")
  curl "${args[@]}" "$API$path"
}

step_register_bundle_id() {
  asc GET "/bundleIds?filter[identifier]=$BUNDLE_ID" | tee /tmp/asc-bundleids.json
  if ! grep -q "$BUNDLE_ID" /tmp/asc-bundleids.json; then
    asc POST /bundleIds '{"data":{"type":"bundleIds","attributes":{"identifier":"'$BUNDLE_ID'","name":"Winnow","platform":"IOS"}}}'
  fi
}

step_create_app() {
  local bid
  bid=$(asc GET "/bundleIds?filter[identifier]=$BUNDLE_ID" | python3 -c 'import json,sys; print(json.load(sys.stdin)["data"][0]["id"])')
  if asc GET "/apps?filter[bundleId]=$BUNDLE_ID" | grep -q "$BUNDLE_ID"; then
    echo "app record exists"; return
  fi
  asc POST /apps '{"data":{"type":"apps","attributes":{"name":"'$APP_NAME'","bundleId":"'$BUNDLE_ID'","sku":"btc-swift-ios","primaryLocale":"en-US"},"relationships":{"bundleId":{"data":{"type":"bundleIds","id":"'$bid'"}}}}}'
}

step_upload() {
  DEVELOPER_DIR=/Applications/Xcode.app/Contents/Developer xcrun altool --upload-app \
    -f build/export/WinnowLean.ipa -t ios --apiKey "$KEY_ID" --apiIssuer "$ISSUER"
}

app_id() {
  # The app record's id anchors every later query. When this read fails, the
  # answer must not be an empty string: 0.8.6's recovery run looked up the
  # app during a burst of 500s, got nothing, and then asked for
  # `/builds?filter[app]=` forty times, a 400 each, until the job's deadline.
  local attempt body id
  for attempt in 1 2 3 4 5; do
    body=$(asc GET "/apps?filter[bundleId]=$BUNDLE_ID") || body=""
    id=$(printf '%s' "$body" | python3 -c '
import json, sys
try:
    print(json.load(sys.stdin)["data"][0]["id"])
except Exception:
    pass
')
    if [ -n "$id" ]; then
      printf '%s\n' "$id"
      return 0
    fi
    echo "app lookup for $BUNDLE_ID returned no usable answer (attempt $attempt/5)" >&2
    sleep 15
  done
  echo "app lookup for $BUNDLE_ID failed" >&2
  return 1
}
build_id() {
  if [ -n "${TESTFLIGHT_BUILD_ID:-}" ]; then
    printf '%s\n' "$TESTFLIGHT_BUILD_ID"
    return
  fi

  if [ -n "$EXPECTED_BUILD_NUMBER" ] && [ -n "$EXPECTED_MARKETING_VERSION" ]; then
    local aid response id
    aid=$(app_id) || return 1
    for attempt in $(seq 1 "$BUILD_WAIT_ATTEMPTS"); do
      response=$(asc GET "/builds?filter[app]=$aid&filter[version]=$EXPECTED_BUILD_NUMBER&filter[preReleaseVersion.version]=$EXPECTED_MARKETING_VERSION&limit=2")
      id=$(printf '%s' "$response" | python3 -c '
import json, sys
rows = json.load(sys.stdin)["data"]
if len(rows) > 1:
    raise SystemExit(f"expected one matching build; found {len(rows)}")
print(rows[0]["id"] if rows else "")
')
      if [ -n "$id" ]; then
        printf '%s\n' "$id"
        return
      fi
      echo "waiting for uploaded version $EXPECTED_MARKETING_VERSION build $EXPECTED_BUILD_NUMBER to appear (attempt $attempt/$BUILD_WAIT_ATTEMPTS)" >&2
      sleep "$BUILD_WAIT_SECONDS"
    done
    echo "uploaded version $EXPECTED_MARKETING_VERSION build $EXPECTED_BUILD_NUMBER never appeared" >&2
    return 1
  fi

  local aid
  aid=$(app_id) || return 1
  asc GET "/builds?filter[app]=$aid&sort=-uploadedDate&limit=1" | python3 -c 'import json,sys; print(json.load(sys.stdin)["data"][0]["id"])'
}

step_wait_processing() {
  local id state
  id=$(build_id)
  for i in $(seq 1 60); do
    state=$(asc GET "/builds/$id" | python3 -c 'import json,sys; d=json.load(sys.stdin)["data"]["attributes"]; print(d["processingState"])')
    echo "build $id: $state"
    [ "$state" = "VALID" ] && return 0
    [ "$state" = "FAILED" ] && return 1
    sleep 30
  done
  return 1
}

# App Store Connect takes at most this many characters of What to Test and
# answers ENTITY_ERROR.ATTRIBUTE.INVALID.TOO_LONG (a 409) above it, which
# releases 0.8.16 and 0.8.17 found only after uploading. The release
# workflow's policy job checks the file first (scripts/check-release-policy).
WHATS_NEW_LIMIT=4000

step_check_notes() {
  if [ ! -s "$WHATS_NEW_FILE" ]; then
    echo "TestFlight What to Test file is missing or empty: $WHATS_NEW_FILE" >&2
    return 1
  fi
  local length
  length=$(python3 -c 'import pathlib, sys; print(len(pathlib.Path(sys.argv[1]).read_text().rstrip()))' "$WHATS_NEW_FILE")
  if [ "$length" -gt "$WHATS_NEW_LIMIT" ]; then
    echo "TestFlight What to Test is $length characters; App Store Connect takes at most $WHATS_NEW_LIMIT: $WHATS_NEW_FILE" >&2
    return 1
  fi
  echo "notes: $length of $WHATS_NEW_LIMIT characters"
}

step_notes() {
  # A write can be refused for a moment after the build turns VALID, or
  # for good, as an over-long text is. Each attempt looks the en-US
  # localization up again, since Apple may create it itself in between, and
  # prints the API's answer when it refuses, so the reason is in the log.
  local bid attempt
  bid=$(build_id)
  step_check_notes || return 1
  for attempt in $(seq 1 8); do
    write_notes "$bid" && return 0
    echo "notes: not accepted yet (attempt $attempt/8); retrying" >&2
    sleep 15
  done
  echo "notes: App Store Connect did not accept What to Test for build $bid" >&2
  return 1
}

write_notes() { # write_notes <build id>
  local bid="$1" localizations localization_id payload response expected actual
  if ! localizations=$(asc GET "/builds/$bid/betaBuildLocalizations?limit=200"); then
    printf '%s\n' "$localizations" >&2
    return 1
  fi
  localization_id=$(printf '%s' "$localizations" | python3 -c '
import json, sys
rows = json.load(sys.stdin)["data"]
matches = [row for row in rows if row.get("attributes", {}).get("locale") == "en-US"]
if len(matches) > 1:
    raise SystemExit(f"expected at most one en-US localization; found {len(matches)}")
print(matches[0]["id"] if matches else "")
')

  if [ -n "$localization_id" ]; then
    payload=$(python3 -c '
import json, pathlib, sys
path, resource_id = sys.argv[1:]
print(json.dumps({"data": {"type": "betaBuildLocalizations", "id": resource_id,
                           "attributes": {"whatsNew": pathlib.Path(path).read_text().rstrip()}}}))
' "$WHATS_NEW_FILE" "$localization_id")
    if ! response=$(asc PATCH "/betaBuildLocalizations/$localization_id" "$payload"); then
      printf '%s\n' "$response" >&2
      return 1
    fi
    echo "notes: updated en-US What to Test for build $bid"
  else
    payload=$(python3 -c '
import json, pathlib, sys
path, build_id = sys.argv[1:]
print(json.dumps({"data": {"type": "betaBuildLocalizations",
                           "attributes": {"locale": "en-US", "whatsNew": pathlib.Path(path).read_text().rstrip()},
                           "relationships": {"build": {"data": {"type": "builds", "id": build_id}}}}}))
' "$WHATS_NEW_FILE" "$bid")
    if ! response=$(asc POST /betaBuildLocalizations "$payload"); then
      printf '%s\n' "$response" >&2
      return 1
    fi
    echo "notes: created en-US What to Test for build $bid"
  fi

  expected=$(python3 -c 'import pathlib,sys; print(pathlib.Path(sys.argv[1]).read_text().rstrip())' "$WHATS_NEW_FILE")
  actual=$(printf '%s' "$response" | python3 -c 'import json,sys; print(json.load(sys.stdin)["data"]["attributes"]["whatsNew"])')
  if [ "$actual" != "$expected" ]; then
    echo "notes: App Store Connect did not return the requested What to Test text" >&2
    return 1
  fi
}

step_internal() {
  # Internal testing: the default "App Store Connect Users" group picks up the
  # processed build automatically. Export compliance is declared in Info.plist;
  # verify Apple's state instead of issuing a PATCH that returns 409 once set.
  local id detail state
  id=$(build_id)
  detail=$(asc GET "/builds/$id/buildBetaDetail")
  state=$(printf '%s' "$detail" | python3 -c 'import json,sys; print(json.load(sys.stdin)["data"]["attributes"]["internalBuildState"])')
  case "$state" in
    READY_FOR_BETA_TESTING|IN_BETA_TESTING)
      echo "internal: build $id is $state"
      ;;
    *)
      echo "internal: build $id is not testable ($state)" >&2
      return 1
      ;;
  esac
}

public_group_id() {
  local aid groups
  aid=$(app_id)
  groups=$(asc GET "/betaGroups?filter[app]=$aid&filter[publicLinkEnabled]=true&limit=200&fields[betaGroups]=name,publicLink,publicLinkId,isInternalGroup,publicLinkEnabled,createdDate")
  printf '%s' "$groups" | python3 -c '
import json, sys
expected = sys.argv[1]
groups = json.load(sys.stdin)["data"]
matches = [g for g in groups if (
    g.get("attributes", {}).get("publicLinkId") == expected
    or g.get("attributes", {}).get("publicLink", "").rstrip("/").endswith("/" + expected)
)]
if len(matches) != 1:
    raise SystemExit(f"expected exactly one public beta group for link {expected}; found {len(matches)}")
print(matches[0]["id"])
' "$PUBLIC_LINK_ID"
}

review_state() {
  local bid="$1"
  asc GET "/betaAppReviewSubmissions?filter[build]=$bid&limit=1" | python3 -c '
import json, sys
rows = json.load(sys.stdin)["data"]
print(rows[0]["attributes"]["betaReviewState"] if rows else "NOT_SUBMITTED")
'
}

build_in_group() {
  local bid="$1" gid="$2"
  asc GET "/builds?filter[app]=$(app_id)&filter[betaGroups]=$gid&filter[id]=$bid&limit=1" | python3 -c '
import json, sys
raise SystemExit(0 if json.load(sys.stdin)["data"] else 1)
'
}

step_external() {
  local bid gid state response
  bid=$(build_id)
  gid=$(public_group_id)

  if build_in_group "$bid" "$gid"; then
    echo "external: build $bid already belongs to public link $PUBLIC_LINK_ID"
  else
    asc POST "/betaGroups/$gid/relationships/builds" \
      '{"data":[{"type":"builds","id":"'$bid'"}]}' >/dev/null
    echo "external: added build $bid to public link $PUBLIC_LINK_ID"
  fi

  state=$(review_state "$bid")
  case "$state" in
    WAITING_FOR_REVIEW|IN_REVIEW|APPROVED)
      echo "external: build $bid review state is $state"
      return 0
      ;;
    REJECTED)
      echo "external: build $bid was rejected by beta review" >&2
      return 1
      ;;
  esac

  # App Store Connect can report a build VALID a few seconds before its beta
  # quality-control state accepts a review submission. Retry that short race,
  # but surface any lasting API error instead of printing a false success.
  for attempt in $(seq 1 12); do
    if response=$(asc POST /betaAppReviewSubmissions \
      '{"data":{"type":"betaAppReviewSubmissions","relationships":{"build":{"data":{"type":"builds","id":"'$bid'"}}}}}'); then
      state=$(review_state "$bid")
      echo "external: build $bid review state is $state"
      [ "$state" != "NOT_SUBMITTED" ]
      return
    fi
    printf '%s\n' "$response" >&2
    echo "external: review submission not ready (attempt $attempt/12); retrying" >&2
    sleep 15
  done

  echo "external: Apple did not accept beta review submission for build $bid" >&2
  return 1
}

step_status() {
  local bid gid processing internal external review grouped
  bid=$(build_id)
  gid=$(public_group_id)
  processing=$(asc GET "/builds/$bid" | python3 -c 'import json,sys; print(json.load(sys.stdin)["data"]["attributes"]["processingState"])')
  read -r internal external < <(asc GET "/builds/$bid/buildBetaDetail" | python3 -c '
import json, sys
a = json.load(sys.stdin)["data"]["attributes"]
print(a["internalBuildState"], a["externalBuildState"])
')
  review=$(review_state "$bid")
  grouped=no
  build_in_group "$bid" "$gid" && grouped=yes
  printf 'build=%s processing=%s internal=%s external=%s review=%s public_link=%s grouped=%s\n' \
    "$bid" "$processing" "$internal" "$external" "$review" "$PUBLIC_LINK_ID" "$grouped"

  [ "$processing" = "VALID" ]
  [ "$grouped" = "yes" ]
  case "$internal" in READY_FOR_BETA_TESTING|IN_BETA_TESTING) ;; *) return 1 ;; esac
  case "$review" in WAITING_FOR_REVIEW|IN_REVIEW|APPROVED) ;; *) return 1 ;; esac
}


# MARK: - App Store (issue #7)

version_id() {
  if [ -n "$APPSTORE_VERSION_ID" ]; then
    printf '%s\n' "$APPSTORE_VERSION_ID"
    return
  fi
  [ -n "$APPSTORE_VERSION_STRING" ] || { echo "set APPSTORE_VERSION_ID or APPSTORE_VERSION_STRING" >&2; return 1; }
  asc GET "/apps/$(app_id)/appStoreVersions?filter[platform]=IOS&filter[versionString]=$APPSTORE_VERSION_STRING&limit=2" | python3 -c '
import json, sys
rows = json.load(sys.stdin)["data"]
if len(rows) != 1:
    raise SystemExit(f"expected exactly one App Store version for that string; found {len(rows)}")
print(rows[0]["id"])
'
}

version_json() {
  asc GET "/appStoreVersions/$(version_id)?include=build,appStoreVersionLocalizations&fields[appStoreVersions]=versionString,appVersionState,platform,releaseType,createdDate,build,appStoreVersionLocalizations&fields[builds]=version,processingState,uploadedDate&fields[appStoreVersionLocalizations]=locale,whatsNew,description,keywords,supportUrl,marketingUrl,promotionalText"
}

version_state() {
  version_json | python3 -c 'import json,sys; print(json.load(sys.stdin)["data"]["attributes"]["appVersionState"])'
}

version_build() {
  version_json | python3 -c '
import json, sys
data = json.load(sys.stdin)["data"]
build = (data.get("relationships", {}).get("build", {}) or {}).get("data") or {}
print(build.get("id", ""))
'
}

build_for_appstore() {
  # The bare "latest upload" fallback in build_id is fine for TestFlight,
  # where the worst case is testers seeing a build early. For App Store
  # review the build must be named.
  if [ -z "${TESTFLIGHT_BUILD_ID:-}" ] && { [ -z "$EXPECTED_BUILD_NUMBER" ] || [ -z "$EXPECTED_MARKETING_VERSION" ]; }; then
    echo "appstore: name the build with TESTFLIGHT_BUILD_ID, or TESTFLIGHT_MARKETING_VERSION plus TESTFLIGHT_BUILD_NUMBER" >&2
    return 1
  fi
  build_id
}

step_appstore_attach() {
  local bid vid state attached prerelease payload attributes
  bid=$(build_for_appstore)
  vid=$(version_id)
  TESTFLIGHT_BUILD_ID="$bid" step_wait_processing >/dev/null
  if [ -n "$APPSTORE_VERSION_STRING" ]; then
    prerelease=$(asc GET "/builds/$bid?include=preReleaseVersion&fields[preReleaseVersions]=version" | python3 -c '
import json, sys
included = json.load(sys.stdin).get("included", [])
print(next((row["attributes"]["version"] for row in included if row["type"] == "preReleaseVersions"), ""))
')
    if [ "$prerelease" != "$APPSTORE_VERSION_STRING" ]; then
      echo "appstore: build $bid is version $prerelease, not $APPSTORE_VERSION_STRING" >&2
      return 1
    fi
  fi
  attached=$(version_build)
  if [ "$attached" = "$bid" ]; then
    echo "appstore: build $bid is already attached to version $vid"
    return 0
  fi
  state=$(version_state)
  case "$state" in
    PREPARE_FOR_SUBMISSION|DEVELOPER_REJECTED|METADATA_REJECTED|REJECTED|INVALID_BINARY) ;;
    *)
      echo "appstore: version $vid is $state; a build can only be attached while it is being prepared" >&2
      return 1
      ;;
  esac
  attributes='{}'
  [ -n "$APPSTORE_VERSION_STRING" ] && attributes='{"versionString":"'"$APPSTORE_VERSION_STRING"'"}'
  payload='{"data":{"type":"appStoreVersions","id":"'"$vid"'","attributes":'"$attributes"',"relationships":{"build":{"data":{"type":"builds","id":"'"$bid"'"}}}}}'
  asc PATCH "/appStoreVersions/$vid" "$payload" >/dev/null
  attached=$(asc GET "/appStoreVersions/$vid/build" | python3 -c 'import json,sys; print((json.load(sys.stdin)["data"] or {}).get("id", ""))')
  if [ "$attached" != "$bid" ]; then
    echo "appstore: App Store Connect did not report build $bid on version $vid after the attach" >&2
    return 1
  fi
  echo "appstore: attached build $bid to version $vid${APPSTORE_VERSION_STRING:+ ($APPSTORE_VERSION_STRING)}"
}

step_appstore_notes() {
  local vid localization_id payload response expected actual
  vid=$(version_id)
  if [ ! -s "$APPSTORE_WHATS_NEW_FILE" ]; then
    echo "App Store What's New file is missing or empty: $APPSTORE_WHATS_NEW_FILE" >&2
    return 1
  fi
  localization_id=$(asc GET "/appStoreVersions/$vid/appStoreVersionLocalizations?limit=200" | python3 -c '
import json, sys
rows = json.load(sys.stdin)["data"]
matches = [row for row in rows if row.get("attributes", {}).get("locale") == "en-US"]
if len(matches) > 1:
    raise SystemExit(f"expected at most one en-US localization; found {len(matches)}")
print(matches[0]["id"] if matches else "")
')
  if [ -n "$localization_id" ]; then
    payload=$(python3 -c '
import json, pathlib, sys
path, resource_id = sys.argv[1:]
print(json.dumps({"data": {"type": "appStoreVersionLocalizations", "id": resource_id,
                           "attributes": {"whatsNew": pathlib.Path(path).read_text().rstrip()}}}))
' "$APPSTORE_WHATS_NEW_FILE" "$localization_id")
    response=$(asc PATCH "/appStoreVersionLocalizations/$localization_id" "$payload")
    echo "appstore: updated en-US What's New for version $vid"
  else
    payload=$(python3 -c '
import json, pathlib, sys
path, version_id = sys.argv[1:]
print(json.dumps({"data": {"type": "appStoreVersionLocalizations",
                           "attributes": {"locale": "en-US", "whatsNew": pathlib.Path(path).read_text().rstrip()},
                           "relationships": {"appStoreVersion": {"data": {"type": "appStoreVersions", "id": version_id}}}}}))
' "$APPSTORE_WHATS_NEW_FILE" "$vid")
    response=$(asc POST /appStoreVersionLocalizations "$payload")
    echo "appstore: created en-US What's New for version $vid"
  fi
  expected=$(python3 -c 'import pathlib,sys; print(pathlib.Path(sys.argv[1]).read_text().rstrip())' "$APPSTORE_WHATS_NEW_FILE")
  actual=$(printf '%s' "$response" | python3 -c 'import json,sys; print(json.load(sys.stdin)["data"]["attributes"]["whatsNew"])')
  if [ "$actual" != "$expected" ]; then
    echo "appstore: App Store Connect did not return the requested What's New text" >&2
    return 1
  fi
}

open_review_submissions() {
  asc GET "/reviewSubmissions?filter[app]=$(app_id)&filter[platform]=IOS&filter[state]=READY_FOR_REVIEW,WAITING_FOR_REVIEW,IN_REVIEW,UNRESOLVED_ISSUES&limit=10"
}

# Prints everything first, then fails on whatever is missing, so a CI log is
# the proof that the metadata behind "already set" is actually there.
step_appstore_status() {
  local vid aid tmp
  vid=$(version_id)
  aid=$(app_id)
  tmp=$(mktemp -d)
  version_json > "$tmp/version.json"
  asc GET "/appStoreVersions/$vid/appStoreVersionLocalizations?include=appScreenshotSets&fields[appScreenshotSets]=screenshotDisplayType&limit=200" > "$tmp/localizations.json"
  asc GET "/apps/$aid/appInfos?include=appInfoLocalizations,primaryCategory&fields[appInfos]=state,appStoreAgeRating,appInfoLocalizations,primaryCategory&fields[appInfoLocalizations]=locale,name,subtitle,privacyPolicyUrl&fields[appCategories]=platforms" > "$tmp/appinfos.json"
  open_review_submissions > "$tmp/submissions.json"
  python3 - "$tmp" <<'EOF'
import json, pathlib, sys
tmp = pathlib.Path(sys.argv[1])
version = json.loads((tmp / "version.json").read_text())
localizations = json.loads((tmp / "localizations.json").read_text())
appinfos = json.loads((tmp / "appinfos.json").read_text())
submissions = json.loads((tmp / "submissions.json").read_text())

data = version["data"]
attributes = data["attributes"]
build = (data.get("relationships", {}).get("build", {}) or {}).get("data") or {}
included = {(row["type"], row["id"]): row for row in version.get("included", [])}
build_row = included.get(("builds", build.get("id")))
build_text = "none"
if build_row:
    b = build_row["attributes"]
    build_text = f'{build["id"]} (build {b.get("version")}, {b.get("processingState")})'
print(f'version={data["id"]} string={attributes.get("versionString")} state={attributes.get("appVersionState")} '
      f'release={attributes.get("releaseType")} build={build_text}')

missing = []
if not build_row:
    missing.append("build")

sets = {row["id"]: row["attributes"].get("screenshotDisplayType") for row in localizations.get("included", [])
        if row["type"] == "appScreenshotSets"}
en_us = None
for row in localizations["data"]:
    a = row["attributes"]
    set_ids = [ref["id"] for ref in (row.get("relationships", {}).get("appScreenshotSets", {}).get("data") or [])]
    kinds = sorted({sets.get(sid, "?") for sid in set_ids})
    print(f'  locale={a.get("locale")} whatsNew={"yes" if a.get("whatsNew") else "no"} '
          f'description={len(a.get("description") or "")} chars keywords={"yes" if a.get("keywords") else "no"} '
          f'supportUrl={a.get("supportUrl") or "none"} marketingUrl={a.get("marketingUrl") or "none"} '
          f'screenshotSets={",".join(kinds) or "none"}')
    if a.get("locale") == "en-US":
        en_us = a
if en_us is None:
    missing.append("en-US localization")
else:
    for key in ("whatsNew", "description", "keywords", "supportUrl"):
        if not en_us.get(key):
            missing.append(key)

infos = appinfos["data"]
info_included = {(row["type"], row["id"]): row for row in appinfos.get("included", [])}
active = next((row for row in infos if row.get("attributes", {}).get("state") == attributes.get("appVersionState")), None)
if active is None and len(infos) == 1:
    active = infos[0]
if active:
    a = active["attributes"]
    category = (active.get("relationships", {}).get("primaryCategory", {}) or {}).get("data") or {}
    print(f'  appInfo state={a.get("state")} ageRating={a.get("appStoreAgeRating") or "unset"} '
          f'primaryCategory={category.get("id") or "none"}')
    if not category.get("id"):
        missing.append("primaryCategory")
    if not a.get("appStoreAgeRating"):
        missing.append("appStoreAgeRating")
    name_found = False
    for ref in (active.get("relationships", {}).get("appInfoLocalizations", {}).get("data") or []):
        row = info_included.get(("appInfoLocalizations", ref["id"]))
        if not row:
            continue
        la = row["attributes"]
        print(f'  appInfo locale={la.get("locale")} name={la.get("name") or "none"} subtitle={la.get("subtitle") or "none"} '
              f'privacyPolicyUrl={la.get("privacyPolicyUrl") or "none"}')
        if la.get("locale") == "en-US":
            name_found = bool(la.get("name"))
            if not la.get("privacyPolicyUrl"):
                missing.append("privacyPolicyUrl")
    if not name_found:
        missing.append("name")
else:
    missing.append("appInfo")

rows = submissions["data"]
print(f'  openReviewSubmissions={len(rows)}' + "".join(f' {r["id"]}:{r["attributes"].get("state")}' for r in rows))

if missing:
    print("appstore: missing " + ", ".join(missing), file=sys.stderr)
    raise SystemExit(1)
print("appstore: metadata complete")
EOF
  local result=$?
  rm -rf "$tmp"
  return $result
}

step_appstore_submit() {
  local vid aid attached whats_new rs state payload
  if [ "$APPSTORE_CONFIRM_SUBMIT" != "yes" ]; then
    echo "appstore: refusing to submit without APPSTORE_CONFIRM_SUBMIT=yes" >&2
    return 1
  fi
  vid=$(version_id)
  aid=$(app_id)
  attached=$(version_build)
  if [ -z "$attached" ]; then
    echo "appstore: version $vid has no build attached; run appstore-attach first" >&2
    return 1
  fi
  whats_new=$(asc GET "/appStoreVersions/$vid/appStoreVersionLocalizations?limit=200" | python3 -c '
import json, sys
rows = json.load(sys.stdin)["data"]
print(next((row["attributes"].get("whatsNew") or "" for row in rows if row["attributes"].get("locale") == "en-US"), ""))
')
  if [ -z "$whats_new" ]; then
    echo "appstore: version $vid has no en-US What's New; run appstore-notes first" >&2
    return 1
  fi

  read -r rs state < <(open_review_submissions | python3 -c '
import json, sys
rows = json.load(sys.stdin)["data"]
print((rows[0]["id"] + " " + rows[0]["attributes"]["state"]) if rows else "- NONE")
')
  case "$state" in
    WAITING_FOR_REVIEW|IN_REVIEW)
      echo "appstore: submission $rs is already $state"
      return 0
      ;;
    UNRESOLVED_ISSUES)
      echo "appstore: submission $rs has unresolved issues; resolve them in App Store Connect" >&2
      return 1
      ;;
    READY_FOR_REVIEW)
      echo "appstore: reusing open submission $rs"
      ;;
    *)
      rs=$(asc POST /reviewSubmissions '{"data":{"type":"reviewSubmissions","attributes":{"platform":"IOS"},"relationships":{"app":{"data":{"type":"apps","id":"'"$aid"'"}}}}}' \
        | python3 -c 'import json,sys; print(json.load(sys.stdin)["data"]["id"])')
      echo "appstore: created submission $rs"
      ;;
  esac
  payload='{"data":{"type":"reviewSubmissionItems","relationships":{"reviewSubmission":{"data":{"type":"reviewSubmissions","id":"'"$rs"'"}},"appStoreVersion":{"data":{"type":"appStoreVersions","id":"'"$vid"'"}}}}}'
  if ! asc POST /reviewSubmissionItems "$payload" >/dev/null; then
    echo "appstore: the version could not be added to submission $rs (already there, or not ready)" >&2
  fi
  asc PATCH "/reviewSubmissions/$rs" '{"data":{"type":"reviewSubmissions","id":"'"$rs"'","attributes":{"submitted":true}}}' >/dev/null
  for attempt in $(seq 1 12); do
    state=$(asc GET "/reviewSubmissions/$rs" | python3 -c 'import json,sys; print(json.load(sys.stdin)["data"]["attributes"]["state"])')
    echo "appstore: submission $rs is $state"
    case "$state" in
      WAITING_FOR_REVIEW|IN_REVIEW) return 0 ;;
      UNRESOLVED_ISSUES) return 1 ;;
    esac
    sleep 15
  done
  echo "appstore: submission $rs did not reach WAITING_FOR_REVIEW" >&2
  return 1
}

case "${1:-all}" in
  register-bundle-id) step_register_bundle_id ;;
  create-app) step_create_app ;;
  upload) step_upload ;;
  wait-processing) step_wait_processing ;;
  notes) step_notes ;;
  check-notes) step_check_notes ;;
  internal) step_internal ;;
  external) step_external ;;
  status) step_status ;;
  appstore-status) step_appstore_status ;;
  appstore-attach) step_appstore_attach ;;
  appstore-notes) step_appstore_notes ;;
  appstore-submit) step_appstore_submit ;;
  all) step_register_bundle_id; step_create_app; step_upload; step_wait_processing; step_notes; step_internal; step_external ;;
  *) echo "unknown step $1" >&2; exit 2 ;;
esac
