# App Store screenshot candidates

The former storefront-only sequence and its optional workflow are retired.
The single iPhone journey, test01CreateReceiveSendConfirm in
UITests/WinnowAppUITests.swift, supplies current screenshots of creating a
wallet, receiving, sending and confirmation. It asserts the real app's
behavior against a disposable signet fixture; failures remain failures even
when a screenshot exists. Detailed feature rules are covered by lower-level
tests. iPad UI runs are deferred until this basic journey is manageable.

CI keeps captures under `journey/node-screenshots/` with
`journey/NodeUI.xcresult` in `app-tests-<run-id>-<attempt>`.
Choose screenshots from a successful run of the intended app revision.
Use only images suitable for publication: never a recovery phrase, exported
secret, debugging failure capture, or private node configuration.

The former `store-*.png` candidates were retired; images in old artifacts or
Git history are not evidence of the current app. No screenshot upload is performed by tests or site generation.
scripts/testflight.sh appstore-status reports the sets already uploaded.
