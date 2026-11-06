import Winnow
import TestKit.Fuzz
open Winnow Winnow.Net Winnow.IO Lean
open TestKit.Fuzz

/-! # `fuzz`: every parser that reads bytes the wallet did not write

`Tools/Fuzz`'s targets on the Lean parsers. A check parses the input and, when that succeeds, holds the result to
what the wallet relies on, which for most targets is that the canonical form parses back to the same thing. The
harness (`TestKit.Fuzz`) has the generator, the replay line and what stands in for Swift's traps.

A check's results must decide something: an unused pure value is compiled away, so a parser whose result nobody
branches on is never run.

Run from `Lean/`. CI runs it in the `lean` job with a seed taken from the commit:

    .lake/build/bin/fuzz --iterations 1000 --seed 0x57494e4e4f575055
    .lake/build/bin/fuzz --target psbt --iterations 200 --save /tmp/fuzz

Every target draws from one generator, so a replay keeps the `--target` the run printed. An input worth keeping
goes in `Vectors/fuzz/<target>/` as a `.bin` (`--save` writes it). -/

/-! Upstream compared the parsed values: comparing only the bytes `serialized` writes would pass a writer that drops
a field, since what it dropped is gone from both sides. The wallet's types have no use for these comparisons. -/
deriving instance BEq for Transaction.Input
deriving instance BEq for Transaction.Output
deriving instance BEq for Transaction
deriving instance BEq for BlockHeader
deriving instance BEq for Block
deriving instance BEq for PSBT.KeyValue
deriving instance BEq for PSBT.Input
deriving instance BEq for PSBT.Output
deriving instance BEq for PSBT
deriving instance BEq for Keys.HDKey
deriving instance BEq for Descriptor.KeyBase
deriving instance BEq for Descriptor.Derivation
deriving instance BEq for Descriptor.SingleKey
deriving instance BEq for Descriptor.TimelockedKeys
deriving instance BEq for Descriptor.Leaf
deriving instance BEq for Descriptor.ScriptTree
deriving instance BEq for Descriptor.ScriptExpression
deriving instance BEq for Descriptor

private def utf8 (s : String) : ByteArray := s.toUTF8
private def lossy := Winnow.Text.decodeUTF8Lossy
private def zeros (n : Nat) : ByteArray := ⟨Array.replicate n 0⟩
private def le32 (n : UInt32) : ByteArray :=
  ⟨#[n.toUInt8, (n >>> 8).toUInt8, (n >>> 16).toUInt8, (n >>> 24).toUInt8]⟩
private def var (b : ByteArray) : ByteArray := compactSize b.size.toUInt64 ++ b

/-- x of the generator, a key every parser takes. -/
private def gx : ByteArray := ofHex! "79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798"
private def gCompressed : ByteArray := ⟨#[0x02]⟩ ++ gx

private def minimalTransaction : ByteArray :=
  ofHex! "0200000001" ++ zeros 32 ++ ofHex! "ffffffff00ffffffff0100000000000000000000000000"

/-- A segwit spend with two outputs; `witness` the input's stack. -/
private def segwitTransaction (witness : List ByteArray) : ByteArray :=
  ofHex! "0200000000010111111111111111111111111111111111111111111111111111111111111111110000000000fdffffff02"
    ++ ofHex! "a086010000000000" ++ var (ofHex! "0014" ++ zeros 20)
    ++ ofHex! "50c3000000000000" ++ var (ofHex! "5120" ++ gx)
    ++ compactSize witness.length.toUInt64 ++ (witness.map var).foldl (· ++ ·) .empty
    ++ le32 0

/-- The inputs a funding-source reader has something to say about: P2WPKH, a Taproot key path, a script path. -/
private def spends : Array ByteArray := #[
  segwitTransaction [zeros 71, gCompressed],
  segwitTransaction [zeros 64],
  segwitTransaction [zeros 64, ofHex! "20" ++ gx ++ ofHex! "ac", ofHex! "c0" ++ gx]]

/-- Key-value pairs, then the map's separator. -/
private def psbtMap (pairs : List (ByteArray × ByteArray)) : ByteArray :=
  (pairs.map fun (k, v) => var k ++ var v).foldl (· ++ ·) .empty ++ ⟨#[0]⟩

/-- A version 0 PSBT over `tx` with what a Taproot input and output carry. -/
private def psbtV0 : ByteArray :=
  let unsigned := ofHex! "02000000011111111111111111111111111111111111111111111111111111111111111111"
    ++ ofHex! "0000000000fdffffff01a086010000000000" ++ var (ofHex! "5120" ++ gx) ++ le32 0
  ofHex! "70736274ff" ++ psbtMap [(⟨#[0]⟩, unsigned)]
    ++ psbtMap [(⟨#[1]⟩, ofHex! "50c3000000000000" ++ var (ofHex! "5120" ++ gx)), (⟨#[3]⟩, le32 0),
        (⟨#[0x17]⟩, gx), (⟨#[0x13]⟩, zeros 64)]
    ++ psbtMap [(⟨#[5]⟩, gx)]

/-- A version 2 PSBT: the fields live in the maps, not in a transaction. -/
private def psbtV2 : ByteArray :=
  ofHex! "70736274ff" ++ psbtMap [(⟨#[0xFB]⟩, le32 2), (⟨#[2]⟩, le32 2), (⟨#[4]⟩, ⟨#[1]⟩), (⟨#[5]⟩, ⟨#[1]⟩)]
    ++ psbtMap [(⟨#[0x0E]⟩, zeros 32), (⟨#[0x0F]⟩, le32 0)]
    ++ psbtMap [(⟨#[3]⟩, ofHex! "a086010000000000"), (⟨#[4]⟩, ofHex! "5120" ++ gx)]

/-- JSON's pieces, and the numbers a store's reader has to bound: `10 ^ exponent` is how `Lean.Json` keeps one. -/
private def jsonTokens : Array ByteArray :=
  #["{", "}", "[", "]", ",", ":", "\"", "null", "true", "false", "0", "-1", "1.5", "1e3", "1e-9", "1e400", "1e-400",
    "18446744073709551616", "1e99999999", "1e-99999999", "\"\"", "\"\\u0000\"", "\"\\ud800\""].map String.toUTF8

/-- CompactSizes written wider than their value, which every reader must refuse. The harness's own length bombs
promise more than follows, so without these a mutation never reaches the minimality rule. -/
private def wideLengths : Array ByteArray :=
  #[⟨#[0xFD, 0, 0]⟩, ⟨#[0xFD, 1, 0]⟩, ⟨#[0xFD, 0xFC, 0]⟩, ⟨#[0xFE, 0, 0, 0, 0]⟩, ⟨#[0xFE, 1, 0, 0, 0]⟩,
    ⟨#[0xFE, 0xFF, 0xFF, 0, 0]⟩, ⟨#[0xFF, 0, 0, 0, 0, 0, 0, 0, 0]⟩, ⟨#[0xFF, 1, 0, 0, 0, 0, 0, 0, 0]⟩,
    ⟨#[0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0, 0, 0, 0]⟩]

private def psbt : Target := {
  name := "psbt"
  tokens := wideLengths
  seeds := #[.empty, ofHex! "70736274ff", ofHex! "70736274ff01fb040200000001020402000000010401000105010000", psbtV0, psbtV2]
  check := fun _ data => do
    let .ok parsed := PSBT.parse data | return false
    let .ok again := PSBT.parse parsed.serialized
      | throw (IO.userError "PSBT's canonical form does not parse")
    require (again == parsed) "PSBT canonical round trip changed it"
    let .ok viaBase64 := PSBT.ofBase64 parsed.base64
      | throw (IO.userError "PSBT's Base64 does not parse")
    require (viaBase64 == parsed) "PSBT Base64 round trip changed it"
    return true }

private def account := "xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL"
private def other := "xpub68NZiKmJWnxxS6aaHmn81bvJeTESw724CRDs6HbuccFQN9Ku14VQrADWgqbhhTHBaohPX4CjNLf9fq9MYo6oDaPPLPxSb7gwQN3ih19Zm4Y"
private def nums := "50929b74c1a04954b78b4b6035e97a5e078a5a0f28ec96d547bfee9ace803ac0"
private def gxHex := "79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798"

private def descriptor : Target := {
  name := "descriptor"
  seeds := #[.empty,
    utf8 s!"tr({gxHex})", utf8 s!"rawtr({gxHex})",
    utf8 s!"tr([deadbeef/86'/0'/0']{account}/<0;1>/*)",
    utf8 s!"tr({other}/0/*)",
    utf8 s!"tr({nums},sortedmulti_a(2,[deadbeef/86'/0'/0']{account}/<0;1>/*,[cafef00d/86'/0'/0']{other}/<0;1>/*))",
    utf8 s!"tr({nums},\{pk({account}/0/*),multi_a(1,{other}/1/*,{account}/1/*)})",
    utf8 s!"tr({nums},\{sortedmulti_a(2,{account}/<0;1>/*,{other}/<0;1>/*),and_v(v:multi_a(1,{account}/<2;3>/*,{other}/<2;3>/*),older(144))})",
    utf8 s!"tr({nums},\{sortedmulti_a(1,{account}/0/*,{other}/0/*),and_v(v:pk({other}/1/*),older(65535))})",
    -- the tree grammar's depth bound
    utf8 (s!"tr({nums}," ++ "".pushn '{' 4000 ++ s!"pk({gxHex})")]
  tokens := #["tr(", "rawtr(", "pk(", "multi_a(", "sortedmulti_a(", "and_v(v:", "older(", ")", "{", "}", ",", "/", "/*",
    "/0", "/1'", "/<0;1>", "/<2;3>", "/<0;1;2>", "[deadbeef/86'/0'/0']", "1", "2", "65535", "4294967295", "#",
    account, other, gxHex, nums].map String.toUTF8
  check := fun _ data => do
    let .ok parsed := Descriptor.parse (lossy data) | return false
    let .ok again := Descriptor.parse parsed.serialized
      | throw (IO.userError s!"a descriptor's canonical form does not parse: {parsed.serialized}")
    require (again == parsed) "descriptor canonical round trip changed it"
    -- upstream's trap: a parseable but malformed multipath at derivation. A refusal here is an answer
    match parsed.derived 0 .mainnet with
    | .ok outputs => require (outputs.all fun o => !o.scriptPubKey.isEmpty) "a derived output with no script"
    | .error _ => pure ()
    return true }

private def transaction : Target := {
  name := "transaction"
  tokens := wideLengths
  seeds := #[.empty, minimalTransaction] ++ spends
  check := fun _ data => do
    let .ok parsed := Transaction.decode data | return false
    let bytes := parsed.serialized true
    require (bytes == data) "a transaction's canonical form is different bytes"
    let .ok again := Transaction.decode bytes
      | throw (IO.userError "a transaction's canonical form does not parse")
    require (again == parsed) "transaction canonical round trip changed it"
    return true }

private def genesisBlock : ByteArray := ofHex! "0100000000000000000000000000000000000000000000000000000000000000000000003ba3edfd7a7b12b27ac72c3e67768f617fc81bc3888a51323a9fb8aa4b1e5e4a29ab5f49ffff001d1dac2b7c0101000000010000000000000000000000000000000000000000000000000000000000000000ffffffff4d04ffff001d0104455468652054696d65732030332f4a616e2f32303039204368616e63656c6c6f72206f6e206272696e6b206f66207365636f6e64206261696c6f757420666f722062616e6b73ffffffff0100f2052a01000000434104678afdb0fe5548271967f1a67130b7105cd6a828e03909a67962e0ea1f61deb649f6bc3f4cef38c4f35504e51ec112de5c384df7ba0b8d578a4c702b6bf11d5fac00000000"

private def block : Target := {
  name := "block"
  tokens := wideLengths
  seeds := #[.empty, zeros 80 ++ ⟨#[0]⟩, zeros 80 ++ ⟨#[1]⟩ ++ minimalTransaction, genesisBlock,
    zeros 80 ++ ⟨#[2]⟩ ++ spends[0]! ++ spends[1]!]
  check := fun _ data => do
    let .ok parsed := Block.decode data | return false
    require (parsed.serialized == data) "a block's canonical form is different bytes"
    let .ok again := Block.decode parsed.serialized
      | throw (IO.userError "a block's canonical form does not parse")
    require (again == parsed) "block canonical round trip changed it"
    return true }

private def commands : Array String :=
  #["version", "verack", "ping", "pong", "sendheaders", "feefilter", "inv", "getdata", "notfound", "tx", "block",
    "getheaders", "headers", "getcfilters", "cfilter", "getcfheaders", "cfheaders", "getcfcheckpt", "cfcheckpt",
    "addr", "getaddr"]

private def networkAddress : ByteArray :=
  zeros 8 ++ ofHex! "00000000000000000000ffff7f000001" ++ ofHex! "208d"

/-- A payload for each message shape, so a mutation lands past the first length. -/
private def payloads : Array ByteArray := #[
  .empty, minimalTransaction, zeros 8,
  -- version
  le32 70016 ++ zeros 4 ++ zeros 8 ++ networkAddress ++ networkAddress ++ zeros 8 ++ var (utf8 "/fuzz:1/") ++ le32 900000 ++ ⟨#[1]⟩,
  -- addr, inv, headers, getheaders
  ⟨#[1]⟩ ++ le32 0 ++ networkAddress,
  ⟨#[1]⟩ ++ le32 2 ++ zeros 32,
  ⟨#[1]⟩ ++ zeros 80 ++ ⟨#[0]⟩,
  le32 70016 ++ ⟨#[1]⟩ ++ zeros 32 ++ zeros 32,
  -- getcfilters, cfilter, cfheaders, cfcheckpt
  ⟨#[0]⟩ ++ le32 0 ++ zeros 32,
  ⟨#[0]⟩ ++ zeros 32 ++ var (ofHex! "019dfca8"),
  ⟨#[0]⟩ ++ zeros 32 ++ zeros 32 ++ ⟨#[1]⟩ ++ zeros 32,
  ⟨#[0]⟩ ++ zeros 32 ++ ⟨#[1]⟩ ++ zeros 32]

private def messages : Target := {
  name := "messages"
  tokens := wideLengths
  seeds := payloads
  check := fun _ data => do
    let mut took := false
    for command in commands do
      let .ok parsed := PeerMessage.decode command data | continue
      took := true
      require (parsed.command == command) s!"{command} decoded as {parsed.command}"
      -- `version` keeps the fields it reads, so its trailing bytes go
      if command != "version" then require (parsed.payload == data) s!"{command}'s canonical form is different bytes"
      let .ok again := PeerMessage.decode parsed.command parsed.payload
        | throw (IO.userError s!"{command}'s canonical form does not parse")
      require (again.command == parsed.command && again.payload == parsed.payload)
        s!"{command} message canonical round trip changed it"
    return took }

private def magic : ByteArray := ofHex! "0a03cf40"

private def framing : Target := {
  name := "framing"
  seeds := #[.empty, MessageFramer.frame "ping" (zeros 8) magic,
    MessageFramer.frame "ping" (zeros 8) magic ++ MessageFramer.frame "tx" minimalTransaction magic]
  check := fun rng data => do
    -- bytes arrive in pieces, as a socket hands them over
    let mut framer : MessageFramer := { magic }
    let mut offset := 0
    while offset < data.size do
      let length := min (data.size - offset) (1 + (← index rng 31))
      framer := framer.append (data.extract offset (offset + length))
      offset := offset + length
    let mut decoded := 0
    while decoded < 32 do
      let .ok (some (command, payload), rest) := framer.nextMessage | break
      framer := rest
      let check : MessageFramer := { magic, buffer := MessageFramer.frame command payload magic }
      let .ok (some (c, p), _) := check.nextMessage
        | throw (IO.userError "a framed message does not parse back")
      require (c == command && p == payload) "framed message did not round trip"
      decoded := decoded + 1
    return decoded > 0 }

private def filter : Target := {
  name := "filter"
  tokens := wideLengths
  seeds := #[.empty, ⟨#[0]⟩, ofHex! "019dfca8", ofHex! "0db414c859a07e8205876354a210a75042d0463404913d61a8e068e58a3ae2aa080026"]
  check := fun _ data => do
    let .ok (count, reader) := ByteReader.readVarInt.run (ByteReader.init data) | return false
    if count > UInt32.size.toUInt64 - 1 then return false
    let .ok f := GCSFilter.decode (key := zeros 16) (n := count.toUInt32) (encoded := data.extract reader.offset data.size)
      | return false
    let hit := f.matchAny #[data.extract 0 32, ⟨#[0]⟩, .empty]
    require (hit || !hit) "unreachable"
    require (f.serialized == data) "GCS filter canonical round trip changed bytes"
    return true }

/-- An address's rules, whatever made its text. -/
private def checkAddress (text : String) : IO Bool := do
  let mut took := false
  for network in [Tx.BitcoinNetwork.mainnet, .signet] do
    let .ok script := AddressDecoder.scriptPubKey text network | continue
    took := true
    require (script.size ≤ 42) "address produced an oversized standard script"
    if let some canonical := AddressDecoder.address script network then
      let .ok again := AddressDecoder.scriptPubKey canonical network
        | throw (IO.userError s!"an address's canonical form does not parse: {canonical}")
      require (again == script) "address canonical round trip changed the script"
      require (canonical.map Char.toLower == (Keys.Unicode.trimWhitespace text).map Char.toLower)
        s!"an address on this network reads back as another: {canonical}"
  return took

private def address : Target := {
  name := "address"
  seeds := #[.empty, utf8 "bc1p5cyxnuxmeuwuvkwfem96lqzszd02n6xdcjrs20cac6yqjjwudpxqkedrcr",
    utf8 "bc1qw508d6qejxtdg4y5r3zarvary0c5xw7kv8f3t4", utf8 "1A1zP1eP5QGefi2DMPTfTL5SLmv7DivfNa",
    utf8 "3J98t1WpEZ73CNmQviecrnyiWrnqRhWNLy", utf8 "tb1qw508d6qejxtdg4y5r3zarvary0c5xdxz4jw"]
  check := fun _ data => checkAddress (lossy data) }

/-- The same rules past the checksum, which `address` never gets by: the input is `version ‖ program` (or, for
base58, `prefix ‖ payload`), encoded here. -/
private def addressProgram : Target := {
  name := "address-program"
  seeds := #[⟨#[1]⟩ ++ gx, ⟨#[0]⟩ ++ zeros 20, ⟨#[0]⟩ ++ zeros 32, ⟨#[2]⟩ ++ zeros 40, ⟨#[16]⟩ ++ zeros 2,
    ⟨#[0xC0]⟩ ++ zeros 20, ⟨#[0xC5]⟩ ++ zeros 20]
  check := fun _ data => do
    let some first := data[0]? | return false
    let body := data.extract 1 data.size
    if first ≥ 0xC0 then
      let version : UInt8 := if first &&& 1 == 0 then 0 else 5
      return ← checkAddress (Base58Check.encode (⟨#[version]⟩ ++ body))
    let mut took := false
    for hrp in ["bc", "tb"] do
      let .ok text := SegwitAddress.encode hrp first.toNat body | continue
      took := (← checkAddress text) || took
    return took }

private def importBundle : Target := {
  name := "import"
  seeds := #[.empty, utf8 "{\"version\":2,\"network\":\"signet\",\"lastKnownHeight\":0,\"utxos\":[],\"transactions\":[]}",
    utf8 ("".pushn '[' 16000)]
  tokens := jsonTokens
  check := fun _ data => do
    let .ok bundle := ImportBundle.decodeData data | return false
    let .ok again := ImportBundle.decode bundle.serialized
      | throw (IO.userError "an import bundle's canonical form does not parse")
    require (again == bundle) "import bundle canonical round trip changed it"
    match bundle.claimedUTXOs with
    | .ok coins => require (coins.size ≤ bundle.utxos.size + bundle.transactions.size + 1 || !coins.isEmpty) "unreachable"
    | .error _ => pure ()
    return true }

/-- `CensusCatalog`'s JSON: the app only reads it, so the encoder is here. -/
private def censusJson (c : CensusCatalog) : Json :=
  let entry (e : CensusEntry) : Json := Json.mkObj [("host", e.host), ("port", e.port.toNat), ("userAgent", e.userAgent),
    ("startHeight", toJson e.startHeight.toInt)]
  Json.mkObj [("schemaVersion", toJson c.schemaVersion), ("date", c.date), ("tip", toJson c.tip.toInt),
    ("networks", Json.mkObj (c.networks.toList.map fun (k, es) => (k, Json.arr (es.map entry))))]

private def census : Target := {
  name := "census"
  seeds := #[.empty, utf8 ("{\"schemaVersion\":1,\"date\":\"2026-09-13\",\"tip\":900000,\"networks\":{\"clearnet\":"
      ++ "[{\"host\":\"8.8.8.8\",\"port\":8333,\"userAgent\":\"/Satoshi:30/\",\"startHeight\":900000}],"
      ++ "\"tor\":[],\"i2p\":[]}}"),
    utf8 ("".pushn '[' 16000)]
  tokens := jsonTokens
  check := fun _ data => do
    let .ok catalog := CensusCatalog.decode data | return false
    let .ok again := CensusCatalog.decode (censusJson catalog).compress.toUTF8
      | throw (IO.userError "a census list's canonical form does not parse")
    let sorted (c : CensusCatalog) := c.networks.qsort (·.1 < ·.1)
    require (sorted again == sorted catalog && again.date == catalog.date && again.tip == catalog.tip)
      "census canonical round trip changed it"
    return true }

private def dnsJSON : Target := {
  name := "dns-json"
  seeds := #[.empty, utf8 "{\"Status\":0,\"Answer\":[{\"name\":\"seed.example.\",\"type\":1,\"TTL\":60,\"data\":\"8.8.8.8\"}]}",
    utf8 ("".pushn '[' 16000)]
  tokens := jsonTokens
  check := fun _ data => do
    let .ok hosts := DNSJSON.hosts data | return false
    require (hosts.all (!·.isEmpty)) "an empty host from a DNS answer"
    return true }

private def fundingSources : Target := {
  name := "funding-sources"
  tokens := wideLengths
  seeds := #[.empty, minimalTransaction] ++ spends
  check := fun _ data => do
    let .ok parsed := Transaction.decode data | return false
    let sources := FundingSources.sources parsed
    let scripts := FundingSources.fundingScripts parsed
    require (sources.size ≤ parsed.inputs.size) "more funding sources than inputs"
    require (scripts.size ≤ parsed.inputs.size) "more funding scripts than inputs"
    return true }

private def controlBlock : Target := {
  name := "control-block"
  seeds := #[.empty, ⟨#[0xC0]⟩ ++ gx, ⟨#[0xC1]⟩ ++ gx ++ zeros 32]
  check := fun _ data => do
    let .ok parsed := Keys.Taproot.ControlBlock.parse data | return false
    require (parsed.serialized == data) "control block canonical round trip changed bytes"
    return true }

private def personPaste : Target := {
  name := "person-paste"
  seeds := #[.empty, utf8 s!"tr({gxHex})", utf8 s!"tr({account}/<0;1>/*)",
    utf8 "bc1p5cyxnuxmeuwuvkwfem96lqzszd02n6xdcjrs20cac6yqjjwudpxqkedrcr",
    utf8 "{\"winnow\":\"person-card\",\"version\":1,\"network\":\"signet\",\"name\":\"Alice\"}",
    utf8 "{\"winnow\":\"person-card\",\"version\":1,\"network\":\"mainnet\",\"name\":\"Alice\",\"payTo\":\"bc1p5cyxnuxmeuwuvkwfem96lqzszd02n6xdcjrs20cac6yqjjwudpxqkedrcr\"}",
    utf8 ("".pushn '[' 16000)]
  tokens := jsonTokens
  check := fun _ data => do
    let text := lossy data
    let mut took := false
    for network in [Tx.BitcoinNetwork.mainnet, .signet] do
      if (PersonPaste.parse text network).toBool then took := true
    if let .ok card := PersonCard.decode text then
      took := true
      let .ok again := PersonCard.decode card.serialized
        | throw (IO.userError "a person card's canonical form does not parse")
      require (again == card) "person card canonical round trip changed it"
    return took }

/-- A code's rules, whatever made its text. -/
private def checkCode (text : String) : IO Bool := do
  let .ok parsed := SilentPaymentAddress.decode text | return false
  require (parsed.scanKey.size == 33 && parsed.spendKey.size == 33) "silent payment code with malformed keys"
  require (text.length ≤ SilentPaymentAddress.maxAddressLength) "silent payment code over the length bound"
  let .ok encoded := parsed.encoded | throw (IO.userError "a silent payment code does not encode")
  require (encoded == (Keys.Unicode.trimWhitespace text).map Char.toLower) "silent payment code did not round trip"
  return true

private def silentPaymentAddress : Target := {
  name := "silent-payment-address"
  seeds := #[.empty, utf8 "tsp1q",
    -- the first official BIP352 sending vector's recipient
    utf8 "sp1qqgste7k9hx0qftg6qmwlkqtwuy6cycyavzmzj85c6qdfhjdpdjtdgqjuexzk6murw56suy3e0rd2cgqvycxttddwsvgxe2usfpxumr70xc9pkqwv"]
  check := fun _ data => checkCode (lossy data) }

/-- Past the checksum: the input is `scan ‖ spend`, encoded here, any length. -/
private def silentPaymentKeys : Target := {
  name := "silent-payment-keys"
  seeds := #[gCompressed ++ gCompressed, gCompressed ++ (⟨#[0x03]⟩ ++ gx)]
  check := fun _ data => do
    let code : SilentPaymentAddress :=
      { scanKey := data.extract 0 33, spendKey := data.extract 33 data.size, hrp := "sp" }
    let .ok text := code.encoded | return false
    checkCode text }

/-! ## What upstream's harness could not reach

These lived in the app target or were internal to WalletCore, so upstream fed them hand-written hostile inputs.
A file on the phone is not hostile the way a peer is, but a backup comes back from iCloud and a file can be
damaged, and each of these has to refuse rather than crash at launch. -/

private def persistedPeers : Target := {
  name := "persisted-peers"
  seeds := #[.empty, utf8 "[{\"host\":\"8.8.8.8\",\"port\":8333}]",
    utf8 "{\"version\":2,\"peers\":[{\"host\":\"8.8.8.8\",\"port\":8333,\"source\":\"persisted\"}]}"]
  tokens := jsonTokens
  check := fun _ data => do
    let some peers := PersistedPeers.decode data | return false
    let bytes := PersistedPeers.encode peers
    let some again := PersistedPeers.decode bytes
      | throw (IO.userError "persisted peers' canonical form does not parse")
    require (PersistedPeers.encode again == bytes) "persisted peers canonical round trip changed bytes"
    return true }

private def rangeScan : Target := {
  name := "range-scan"
  seeds := #[.empty, utf8 "{\"record\":\"range\",\"from\":1,\"to\":5,\"nextScanHeight\":2,\"watchFingerprint\":\"ab\",\"iteration\":0,\"filterHeaders\":{}}"]
  tokens := jsonTokens
  check := fun _ data => do
    let .ok progress := RangeScanProgress.decode (lossy data) | return false
    let .ok again := RangeScanProgress.decode progress.toJson.compress
      | throw (IO.userError "a range-scan record's canonical form does not parse")
    require (again == progress) "range-scan canonical round trip changed it"
    return true }

private def broadcastStore : Target := {
  name := "broadcast-store"
  seeds := #[.empty, utf8 "{\"version\":1,\"transactions\":{}}"]
  tokens := jsonTokens
  check := fun _ data => do
    let .ok pending := TxBroadcaster.decodeStore data 0 | return false
    let bytes := TxBroadcaster.encodeStore pending
    let .ok again := TxBroadcaster.decodeStore bytes 0
      | throw (IO.userError "the relay store's canonical form does not parse")
    require (TxBroadcaster.encodeStore again == bytes) "relay store canonical round trip changed bytes"
    return true }

/-- Every simple field away from its default, or a writer that drops one writes what the reader assumes. Written
out, not made with `WalletState.encode`: a seed from the code under test carries that code's bugs. -/
private def fullWalletState : ByteArray :=
  utf8 ("{\"creationHeight\":7,\"descriptor\":\"tr(79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798)\","
    ++ "\"history\":[],\"network\":\"signet\",\"nextChangeIndex\":5,\"nextReceiveIndex\":3,\"nextScanHeight\":11,"
    ++ "\"observedFeeRates\":[1.5,2],\"pendingSends\":[],"
    ++ "\"scannedThroughHash\":\"0000000000000000000000000000000000000000000000000000000000000000\",\"utxos\":[]}")

private def walletState : Target := {
  name := "wallet-state"
  seeds := #[.empty,
    fullWalletState]
  tokens := jsonTokens
  check := fun _ data => do
    let .ok state := WalletState.decode (lossy data) | return false
    let .ok text := state.encode | return true
    let .ok again := WalletState.decode text
      | throw (IO.userError "the wallet file's canonical form does not parse")
    require (again == state) "wallet file canonical round trip changed it"
    return true }

private def ledgerFrames : Target := {
  name := "ledger-frames"
  seeds := #[.empty, ofHex! "0500000004deadbeef", ofHex! "0500000003aabb" ++ ofHex! "05" ++ ofHex! "0001cc"]
  check := fun rng data => do
    let mut r : Ledger.BluetoothFraming.Reassembler := {}
    let mut offset := 0
    let mut took := false
    let mut promised := 0
    while offset < data.size do
      let length := min (data.size - offset) (3 + (← index rng 20))
      let frame := data.extract offset (offset + length)
      offset := offset + length
      match r.receive frame with
      | .ok (next, reply) =>
        if r.nextSequence == 0 then promised := (frame[3]!.toNat <<< 8) ||| frame[4]!.toNat
        r := next
        if let some bytes := reply then
          took := true
          require (bytes.size == promised) "a Ledger reply that is not the length its first frame gave"
          if bytes.size ≥ 2 then require (Ledger.Response.parse bytes).toBool "a complete reply does not parse"
      | .error _ => pure ()
    return took }

private def ledgerCommands : Target := {
  name := "ledger-commands"
  seeds := #[⟨#[Ledger.Interpreter.yieldCode]⟩, ⟨#[Ledger.Interpreter.getPreimage, 0]⟩ ++ zeros 32,
    ⟨#[Ledger.Interpreter.getMerkleLeafProof]⟩ ++ zeros 32 ++ ⟨#[2, 0, 0]⟩,
    ⟨#[Ledger.Interpreter.getMerkleLeafIndex]⟩ ++ zeros 32 ++ zeros 32, ⟨#[Ledger.Interpreter.getMoreElements]⟩]
  check := fun _ data => do
    let leaf := zeros 32
    let i : Ledger.Interpreter :=
      { preimages := #[(zeros 32, gx)], trees := #[(zeros 32, #[leaf, gx])], queue := #[gx, leaf] }
    let .ok (_, reply) := i.execute data | return false
    require (reply.size ≤ 16777216) "an oversized answer to a Ledger command"
    return true }

private def targets : Array Target :=
  #[psbt, descriptor, transaction, block, messages, framing, filter, address, importBundle, census, dnsJSON,
    fundingSources, controlBlock, personPaste, silentPaymentAddress, addressProgram, silentPaymentKeys,
    persistedPeers, rangeScan, broadcastStore, walletState, ledgerFrames, ledgerCommands]

def main (args : List String) : IO UInt32 := TestKit.Fuzz.main targets "Vectors/fuzz" args
