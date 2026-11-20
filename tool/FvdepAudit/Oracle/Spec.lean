import FvdepAudit.Oracle.Wire.Spec
import FvdepCore.Oracle

/-! Spec of the oracle's merge (contract `docs/contracts/U5b-oracle.md` V4–V5), written apart from
`FvdepCore.Oracle`: the replies in request order, paired with the step's LF-terminated lines — a
refused request = its `invalid` reply (no line), a valid one = the next line, which must be W2's
result line (UTF-8) of a reply the result type admits. -/

namespace FvdepAudit.Oracle.Spec

open FvdepCore.Protocol FvdepCore.Oracle FvdepAudit.Oracle.Wire.Spec

/-- V4: lines as the step's `replies.txt` holds them: each followed by LF. -/
def framed (ls : List (List UInt8)) : List UInt8 := ls.flatMap fun l => l ++ [0x0A]

-- `resultLayout` rests on core's noncomputable UTF-8 encoder: no spec runs.
noncomputable section

/-- W2's result line of `x` as UTF-8 bytes. -/
def lineBytes (x : Reply) : List UInt8 := (resultLayout x).toUTF8.data.toList

/-- V4–V5: `out` = the replies of `reqs`, in order, the step's lines `ls` consumed one per valid
request: a refused request gives its `invalid` reply + consumes no line; a valid one gives a reply
`x` the result type admits whose line is the next line. -/
inductive Merged (rt : RTy) : List Req → List (List UInt8) → List Reply → Prop
  | nil : Merged rt [] [] []
  |
  invalid {reqs : List Req} {ls : List (List UInt8)} {out : List Reply} (r : String) :
    Merged rt reqs ls out → Merged rt (.invalid r :: reqs) ls (.invalid r :: out)
  |
  valid {reqs : List Req} {ls : List (List UInt8)} {out : List Reply} (x : Reply) :
    Typed rt x → Merged rt reqs ls out → Merged rt (.valid :: reqs) (lineBytes x :: ls) (x :: out)

end

end FvdepAudit.Oracle.Spec
