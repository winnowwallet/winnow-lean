# App Store screenshot candidates

The former storefront-only sequence and its optional workflow are retired.
The ten Lean journeys in `LeanApp/Journeys.lean` supply current screenshots:
each takes named captures as it goes, `createReceiveSendConfirm` those of
creating a wallet, receiving, sending and confirmation. They assert the real
app's behavior against a disposable regtest fixture; failures remain failures
even when a screenshot exists. Detailed feature rules are covered by
lower-level tests. CI runs them on an iPhone simulator (`ui-device-type` in
`.github/workflows/ci.yml`); there is no iPad UI run.

CI keeps each part's captures with `journey/journey.xcresult` in
`app-<run-id>-<attempt>-part-<index>`, and publishes the whole run's
`screenshots/` in the `journey-media` artifact once every journey has passed.
Choose screenshots from a successful run of the intended app revision.
Use only images suitable for publication: never a recovery phrase, exported
secret, debugging failure capture, or private node configuration.

The former `store-*.png` candidates were retired; images in old artifacts or
Git history are not evidence of the current app. No screenshot upload is performed by tests or site generation.
`leannative-release testflight appstore-status` reports the sets already uploaded.
