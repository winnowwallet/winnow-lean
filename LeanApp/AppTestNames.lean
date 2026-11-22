import WinnowApp.Real.RecordsSeal

/-! Test-only case-name tables for `WinnowApp.RecordsReal` errors. Kept out of shipped `WinnowApp`
so `RecordsSeal.lean` carries only user-facing descriptions and typed predicates. -/

namespace WinnowApp.RecordsReal

def SealFailure.name : SealFailure → String
  | .unsealed => "unsealed"
  | .keyMissing => "keyMissing"
  | .malformed => "malformed"
  | .verificationFailed => "verificationFailed"

def SignerStorageError.name : SignerStorageError → String
  | .invalidState _ => "invalidState"
  | .damaged => "damaged"
  | .duplicate _ => "duplicate"
  | .unknownSigner => "unknownSigner"
  | .tooMany => "tooMany"

def RecordsError.name : RecordsError → String
  | .seal f => f.name
  | .keyVault (.alreadyEstablished _) => "alreadyEstablished"
  | .keyVault .malformedKey => "malformedKey"
  | .keyVault (.keychain _) => "keychain"
  | .people (.invalidState _) => "invalidState"
  | .people .damaged => "damaged"
  | .people (.duplicate _) => "duplicate"
  | .people .unknownPerson => "unknownPerson"
  | .people .tooMany => "tooMany"
  | .labels .unavailable => "unavailable"
  | .labels .damaged => "damaged"
  | .labels .invalidLabel => "invalidLabel"
  | .labels .full => "full"
  | .multisig (.invalidState _) => "invalidState"
  | .multisig .damaged => "damaged"
  | .multisig .duplicate => "duplicate"
  | .multisig .tooMany => "tooMany"
  | .multisig .unavailable => "unavailable"
  | .signers e => e.name
  | .app .noWallet => "noWallet"
  | .app .sendReviewChanged => "sendReviewChanged"
  | .app .personCannotBePaid => "personCannotBePaid"
  | .lookup _ => "unavailable"
  | .named n _ => n
  | .io _ => "ioError"

end WinnowApp.RecordsReal
