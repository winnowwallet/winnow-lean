import LeanNative.Journey
import WinnowApp.Ids
import Journeys.Screens

/-! # SegWit v0 multisig journey: `wsh(sortedmulti(2, FIXED, phoneKey, otherKey))` -/

namespace WinnowJourneys
open Lean LeanNative LeanNative.Journey WinnowApp.Ids

/-- Joining a SegWit v0 2-of-3 multisig account, receiving bitcoin, reviewing and co-signing Core's PSBT,
and broadcasting so Core's chain confirms. -/
def segwitMultisigJoinSign : Journey := ⟨"segwitMultisigJoinSign", do
  failure "segwitMultisigJoinSign not yet implemented"⟩

end WinnowJourneys
