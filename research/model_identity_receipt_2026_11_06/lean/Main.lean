/-
mir-verify: the receipt verifier CLI. Its verdict is `Mir.verify` / `Mir.accepts` (Mir/Receipt.lean) evaluated on the
parsed receipt with SHA-256 and Ed25519 from Mir.Crypto; nothing here decides acceptance on its own.

  mir-verify check RECEIPT.json --cid HEX --trust PK[,PK..] [--strict] [--recomputer PK[,PK..]] [--fp-verdict yes|no]
  mir-verify fields RECEIPT.json OUT.bin          the bytes the evaluator signs (Ed25519 over these, raw)
  mir-verify edge-fields RECEIPT.json N OUT.bin   the bytes a recomputer signs for edge N (from 0)
  mir-verify graph-digest RECEIPT.json
-/
import Lean.Data.Json
import Mir.Crypto
import Mir.Receipt

open Lean (Json)
open Mir

def hashHex (s : String) : String := Mir.Crypto.toHex (Mir.Crypto.sha256 s.toUTF8)

def fieldTag : ByteArray := "mir13/fields/v1\n".toUTF8

/-- The encoding the keys sign: tag, the field count (one byte), each field's 32 raw bytes. -/
def encodeFields (fields : List String) : Option ByteArray := do
  let raw ← fields.mapM Mir.Crypto.ofHex?
  if raw.any (fun b => b.size != 32) || fields.length > 255 then none
  pure (raw.foldl (· ++ ·) (fieldTag.push fields.length.toUInt8))

def sigOkImpl (pk : String) (fields : List String) (sig : String) : Bool :=
  match Mir.Crypto.ofHex? pk, Mir.Crypto.ofHex? sig, encodeFields fields with
  | some p, some s, some m => Mir.Crypto.ed25519Verify p m s
  | _, _, _ => false

def crypto : Crypto := { hash := hashHex, sigOk := sigOkImpl }

def getStr (j : Json) (k : String) : Except String String := do
  match j.getObjVal? k with
  | .ok (.str s) => pure s
  | _ => throw s!"missing string field {k}"

def parseBasis (j : Json) : Except String Basis := do
  match ← getStr j "kind" with
  | "rerunnable" => return .rerunnable (← getStr j "how")
  | "recomputed" => return .recomputed (← getStr j "signer") (← getStr j "signature")
  | "published" => return .published (← getStr j "source")
  | k => throw s!"unknown basis {k}"

def parseReceipt (j : Json) : Except String Receipt := do
  if (← getStr j "format") != "mir13/receipt/v1" then throw "format is not mir13/receipt/v1"
  let g ← j.getObjVal? "graph"
  let nodes ← (← (← g.getObjVal? "nodes").getArr?).toList.mapM fun n => do
    return ({ id := ← getStr n "id", kind := ← getStr n "kind", digest := ← getStr n "digest" } : Node)
  let edges ← (← (← g.getObjVal? "edges").getArr?).toList.mapM fun e => do
    let rel ← match ← getStr e "rel" with
      | "converts" => pure Rel.converts | "commits" => pure Rel.commits
      | "quantizes" => pure Rel.quantizes | "digest-of" => pure Rel.digestOf
      | x => throw s!"unknown relation {x}"
    return ({ src := ← getStr e "src", dst := ← getStr e "dst", rel, rule := ← getStr e "rule",
              basis := ← parseBasis (← e.getObjVal? "basis") } : Edge)
  let ev ← j.getObjVal? "eval"
  return {
    commitmentId := ← getStr j "commitment_id", rootset := ← getStr j "rootset",
    wsums := ← getStr j "wsums_sha256", filesDigest := ← getStr j "files_digest",
    graph := { nodes, edges },
    eval := { evaluator := ← getStr ev "evaluator", publicKey := ← getStr ev "public_key",
              node := ← getStr ev "node", benchmark := ← getStr ev "benchmark",
              scores := ← getStr ev "scores", signature := ← getStr ev "signature" } }

def load (path : String) : IO Receipt := do
  let txt ← IO.FS.readFile path
  match Json.parse txt >>= parseReceipt with
  | .ok r => pure r
  | .error e => throw (IO.userError s!"{path}: {e}")

def opt (args : List String) (k : String) : Option String :=
  match args.dropWhile (· != k) with
  | _ :: v :: _ => some v
  | _ => none

def splitKeys (s : Option String) : List String :=
  match s with
  | some v => (v.splitOn ",").filter (· != "")
  | none => []

def line (ok : Bool) (what : String) : IO Unit :=
  IO.println s!"  {if ok then "yes" else "NO "}  {what}"

def check (path : String) (args : List String) : IO UInt32 := do
  let r ← load path
  let some cid := opt args "--cid" | throw (IO.userError "--cid HEX is required: the ID you gave cp_verify")
  let trusted := splitKeys (opt args "--trust")
  let recs := splitKeys (opt args "--recomputer")
  let strict := args.contains "--strict"
  let fpYes := opt args "--fp-verdict" == some "yes"
  let c := crypto
  IO.println s!"receipt {path}"
  IO.println s!"  commitment ID {r.commitmentId}"
  IO.println s!"  root set      {r.rootset}"
  IO.println s!"  graph digest  {graphDigest c r.graph}"
  line (wellFormed r) "well formed: unique node ids, one node per role, edges between existing nodes, 64-hex digests"
  line (graphNames c r) "the roles carry the receipt's digests; the deployment digest is its components'; the evaluation names it"
  line (requiredEdge c strict recs r.graph .converts "gguf-files" "integers")
    s!"edge E2 present (files -> integers, section 11){if strict then ", recomputed and signed by a trusted recomputer" else ""}"
  line (requiredEdge c strict recs r.graph .commits "gguf-files" "flashprove-commitment")
    s!"edge E3 present (files -> commitment, cp_commit){if strict then ", recomputed and signed by a trusted recomputer" else ""}"
  line (trusted.contains r.eval.publicKey) s!"the evaluator key is one you trust ({r.eval.evaluator})"
  line (c.sigOk r.eval.publicKey (evalFields c r) r.eval.signature) "the evaluation record's signature verifies over the signed fields"
  line (cid == r.commitmentId) "the ID you checked the proof against is the receipt's"
  let v := verify c trusted strict recs r
  let a := accepts c trusted strict recs r (fun (_ : String) (_ : Unit) => fpYes) cid ()
  IO.println ""
  IO.println "edges and who vouches for them:"
  for e in r.graph.edges do
    IO.println s!"  {e.src} -{e.rel.tag}-> {e.dst} [{e.rule}]: {basisText e.basis}"
  IO.println ""
  if v && cid == r.commitmentId then
    if fpYes then
      IO.println "ACCEPT. By Mir.identity_sound: the claim of a proof that cp_verify accepted against this ID holds for"
      IO.println "the integers converted from the files named here, whose registry v2 root set is the receipt's, inside the"
      IO.println "deployment the evaluation record signs; or FlashProve's verifier or binding failed, or SHA-256 collided"
      IO.println "on the file list. It rests on FlashProve's soundness and on edges E2 and E3 as vouched for above"
      IO.println (if strict then "(strict: both recomputed and signed by keys you trust; Mir.identity_sound_strict)."
                  else "(not strict: whatever their basis says; --strict demands trusted recomputers).")
    else
      IO.println "RECEIPT VERIFIED for this ID. No proof verdict given (--fp-verdict yes after cp_verify says YES)."
    pure (if a || !fpYes then 0 else 1)
  else
    IO.println "REFUSE"
    pure 1

def main (args : List String) : IO UInt32 := do
  match args with
  | "check" :: path :: rest => check path rest
  | ["fields", path, out] => do
    let r ← load path
    match encodeFields (evalFields crypto r) with
    | some b => IO.FS.writeBinFile out b; pure 0
    | none => IO.eprintln "a signed field is not 64 hex digits"; pure 1
  | ["edge-fields", path, n, out] => do
    let r ← load path
    let some e := r.graph.edges[n.toNat!]? | IO.eprintln "no such edge"; pure 1
    let some sn := nodeById r.graph e.src | IO.eprintln "no source node"; pure 1
    let some dn := nodeById r.graph e.dst | IO.eprintln "no destination node"; pure 1
    match encodeFields (edgeFieldsOf crypto e.rel sn.kind sn.digest dn.kind dn.digest e.rule) with
    | some b => IO.FS.writeBinFile out b; pure 0
    | none => IO.eprintln "a field is not 64 hex digits"; pure 1
  | ["graph-digest", path] => do
    let r ← load path
    IO.println (graphDigest crypto r.graph); pure 0
  | _ => IO.eprintln "usage: see the head of Main.lean"; pure 2
