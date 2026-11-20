import FvdepCore.Export
import FvdepCore.Oracle.Wire

/-! The oracle's pure parts (contract `docs/contracts/U5b-oracle.md` V4–V5): the merge of the
supervisor's refusals + the evaluation step's reply lines into the replies, in request order. -/

namespace FvdepCore.Oracle

open FvdepCore.Protocol

/-- V2: a request as the supervisor decoded it: refused by `decodeRequest` (its reason), or valid
(its arguments went to the step, one reply line back). -/
inductive Req where
  | invalid (reason : String)
  | valid
  deriving DecidableEq, Repr

/-- V4: one reply line of the step (its bytes without the LF) read against the result type: UTF-8,
then W's `parseResult`. -/
def parseLine (rt : RTy) (l : ByteArray) : Option Reply :=
  (String.fromUTF8? l).bind (Wire.parseResult rt)

/-- V4 from offset `i` of the step's `replies.txt`, `k` = the next valid request's 1-based rank: a
refused request = its `invalid` reply; a valid one = the LF-terminated line at `i`, parsed; a
missing, unterminated or unparsed line = `.error k`; bytes left after the last valid request =
`.error k` (an extra line). -/
def mergeFrom (rt : RTy) (b : ByteArray) (k : Nat) : Nat → List Req → Except Nat (List Reply)
  | i, [] => if i == b.size then .ok [] else .error k
  | i, .invalid r :: rs => (.invalid r :: ·) <$> mergeFrom rt b k i rs
  | i, .valid :: rs =>
    let e := Export.lineEnd b i
    if e < b.size then
      match parseLine rt (b.extract i e) with
      | some x => (x :: ·) <$> mergeFrom rt b (k + 1) (e + 1) rs
      | none => .error k
    else .error k

/-- V4: the replies in request order, or the 1-based rank of the step's first malformed reply
(`infra io: oracle, evaluate: the driver's reply <k> is malformed`). -/
def merge (rt : RTy) (reqs : List Req) (replies : ByteArray) : Except Nat (List Reply) :=
  mergeFrom rt replies 1 0 reqs

end FvdepCore.Oracle
