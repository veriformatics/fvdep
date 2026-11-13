import FvdepAudit.Doc.Proof.Clip
import FvdepAudit.Doc.Proof.Receipt

/-! The `--json` envelope (D6): encoding = the layout, the shipped check decides `WellFormed`, a
well-formed envelope's JSON is J1-valid. -/

namespace FvdepAudit.Doc.Proof

open FvdepCore.Json (Value)
open FvdepCore.Ids FvdepCore.Status FvdepCore.Doc FvdepAudit.Doc.Spec
open FvdepAudit.Json.Spec

theorem maxInt_eq' : FvdepCore.Json.maxInt = FvdepAudit.Json.Spec.maxInt := rfl

theorem maxStringBytes_eq' : FvdepCore.Json.maxStringBytes = FvdepAudit.Json.Spec.maxStringBytes :=
  rfl

theorem keysAscending_iff :
    ∀ ms : List (String × Value), keysAscending ms = true ↔ (ms.map (·.1)).Pairwise (· < ·)
  | [] => by simp [keysAscending]
  | [_] => by simp [keysAscending]
  | a :: b :: rest => by
    have ih := keysAscending_iff (b :: rest)
    simp only [keysAscending, Bool.and_eq_true, decide_eq_true_eq, ih]
    constructor
    · rintro ⟨hab, hrest⟩
      refine List.pairwise_cons.mpr ⟨?_, hrest⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hab
      · exact String.lt_trans hab ((List.pairwise_cons.mp hrest).1 y hy)
    · intro h
      exact ⟨(List.pairwise_cons.mp h).1 _ (by simp), (List.pairwise_cons.mp h).2⟩

mutual
theorem fits_iff (d : Nat) :
    ∀ v : Value,
      fits d v = true ↔ intsFit v = true ∧ stringsFit v = true ∧ depth v ≤ d ∧ keysAscend v = true
  | .null => by simp [fits, intsFit, stringsFit, depth, keysAscend]
  | .bool _ => by simp [fits, intsFit, stringsFit, depth, keysAscend]
  | .int _ => by
    simp only [fits, intsFit, stringsFit, depth, keysAscend, maxInt_eq']
    exact ⟨fun h => ⟨h, trivial, Nat.zero_le _, trivial⟩, fun h => h.1⟩
  | .str _ => by
    simp only [fits, intsFit, stringsFit, depth, keysAscend, maxStringBytes_eq']
    exact ⟨fun h => ⟨trivial, h, Nat.zero_le _, trivial⟩, fun h => h.2.1⟩
  | .arr xs => by
    have ih := fitsList_iff (d - 1) xs
    simp only [fits, intsFit, stringsFit, depth, keysAscend, Bool.and_eq_true, decide_eq_true_eq,
      ih]
    constructor
    · rintro ⟨hd, hi, hs, hp, hk⟩
      exact ⟨hi, hs, by omega, hk⟩
    · rintro ⟨hi, hs, hp, hk⟩
      exact ⟨by omega, hi, hs, by omega, hk⟩
  | .obj ms => by
    have ih := fitsMembers_iff (d - 1) ms
    simp only [fits, intsFit, stringsFit, depth, keysAscend, Bool.and_eq_true, decide_eq_true_eq,
      ih, keysAscending_iff]
    constructor
    · rintro ⟨⟨hd, ha⟩, hi, hs, hp, hk⟩
      exact ⟨hi, hs, by omega, ha, hk⟩
    · rintro ⟨hi, hs, hp, ha, hk⟩
      exact ⟨⟨by omega, ha⟩, hi, hs, by omega, hk⟩
theorem fitsList_iff (d : Nat) :
    ∀ xs : List Value,
      fitsList d xs = true ↔
        intsFitList xs = true ∧
          stringsFitList xs = true ∧ depthList xs ≤ d ∧ keysAscendList xs = true
  | [] => by simp [fitsList, intsFitList, stringsFitList, depthList, keysAscendList]
  | v :: vs => by
    have h1 := fits_iff d v
    have h2 := fitsList_iff d vs
    simp only [fitsList, intsFitList, stringsFitList, depthList, keysAscendList, Bool.and_eq_true,
      h1, h2, Nat.max_le]
    constructor
    · rintro ⟨⟨a1, a2, a3, a4⟩, b1, b2, b3, b4⟩
      exact ⟨⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, a4, b4⟩
    · rintro ⟨⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, a4, b4⟩
      exact ⟨⟨a1, a2, a3, a4⟩, b1, b2, b3, b4⟩
theorem fitsMembers_iff (d : Nat) :
    ∀ ms : List (String × Value),
      fitsMembers d ms = true ↔
        intsFitMembers ms = true ∧
          stringsFitMembers ms = true ∧ depthMembers ms ≤ d ∧ keysAscendMembers ms = true
  | [] => by simp [fitsMembers, intsFitMembers, stringsFitMembers, depthMembers, keysAscendMembers]
  | (k, v) :: ms => by
    have h1 := fits_iff d v
    have h2 := fitsMembers_iff d ms
    simp only [fitsMembers, intsFitMembers, stringsFitMembers, depthMembers, keysAscendMembers,
      Bool.and_eq_true, decide_eq_true_eq, h1, h2, Nat.max_le, maxStringBytes_eq']
    constructor
    · rintro ⟨⟨hk, a1, a2, a3, a4⟩, b1, b2, b3, b4⟩
      exact ⟨⟨a1, b1⟩, ⟨⟨of_decide_eq_true hk, a2⟩, b2⟩, ⟨a3, b3⟩, a4, b4⟩
    · rintro ⟨⟨a1, b1⟩, ⟨⟨hk, a2⟩, b2⟩, ⟨a3, b3⟩, a4, b4⟩
      exact ⟨⟨decide_eq_true hk, a1, a2, a3, a4⟩, b1, b2, b3, b4⟩
end

theorem command_text (c : Command) : c.spelling = commandText c := by cases c <;> rfl

theorem code_text (c : PublicCode) : c.spelling = codeText c := by cases c <;> rfl

/-- D7 `EnvelopeEncodeExact`. -/
theorem envelope_encode (e : Envelope) : e.toJson = envelopeLayout e := by
  rcases e with ⟨cmd, ex, err, res, ⟨com, fet, ferr⟩, tr⟩
  cases ex <;> rcases err with _ | ⟨code, det⟩ <;> rcases com with _ | c <;>
    rcases ferr with _ | fe <;>
    simp [Envelope.toJson, envelopeLayout, clip_exact, optStr_eq, nullOr, Exit.code, command_text,
      code_text]

/-- D8 `EnvelopeCheck`. -/
theorem envelope_check (e : Envelope) : e.wellFormed = true ↔ EnvelopeWF e := by
  unfold Envelope.wellFormed EnvelopeWF
  have hfetch : e.status.fetched.all isUtc = true ↔ ∀ f, e.status.fetched = some f → UtcText f := by
    cases e.status.fetched with
    | none => simp
    | some f => simp [isUtc_iff]
  have herr :
    (e.error.isSome == (e.exit == .failure)) = true ↔ (e.error ≠ none ↔ e.exit = .failure) := by
    cases e.error <;> cases e.exit <;> simp
  rw [Bool.and_eq_true, Bool.and_eq_true, herr, hfetch, fits_iff]
  constructor
  · rintro ⟨⟨h1, hi, hs, hd, hk⟩, hf⟩
    exact
      ⟨h1,
        ⟨hi, hs, by
          simp only [maxDepth]; omega, hk⟩,
        hd, hf⟩
  · rintro ⟨h1, ⟨hi, hs, -, hk⟩, hd, hf⟩
    exact ⟨⟨h1, hi, hs, hd, hk⟩, hf⟩

theorem command_size (c : Command) : (commandText c).utf8ByteSize ≤ maxStringBytes := by
  cases c <;> decide

theorem code_size (c : PublicCode) : (codeText c).utf8ByteSize ≤ maxStringBytes := by
  cases c <;> decide

theorem clip_size (s : String) : (clipSpec s).utf8ByteSize ≤ maxStringBytes := by
  rw [← clip_exact]
  exact clip_bound s

theorem clips_fit (xs : List String) :
    stringsFitList (xs.map fun s => .str (clipSpec s)) = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [stringsFitList, stringsFit, clip_size, ih]

theorem clips_ints (xs : List String) : intsFitList (xs.map fun s => .str (clipSpec s)) = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [intsFitList, intsFit, ih]

theorem clips_depth (xs : List String) : depthList (xs.map fun s => .str (clipSpec s)) = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [depthList, depth, ih]

theorem clips_keys (xs : List String) :
    keysAscendList (xs.map fun s => .str (clipSpec s)) = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [keysAscendList, keysAscend, ih]

/-- D7 `EnvelopeValid`. -/
theorem envelope_valid (e : Envelope) (h : EnvelopeWF e) : Valid e.toJson := by
  rw [envelope_encode]
  obtain ⟨-, ⟨hi, hs, -, hk⟩, hd, hf⟩ := h
  rcases e with ⟨cmd, ex, err, res, ⟨com, fet, ferr⟩, tr⟩
  simp only [intsFit, stringsFit, keysAscend, Bool.and_eq_true, decide_eq_true_eq] at hi hs hk
  simp only [depth] at hd
  have k1 :
    ["command", "error", "exit", "result", "schema", "status", "trusted"].Pairwise (· < ·) := by
    decide
  have k2 : ["code", "detail"].Pairwise (· < ·) := by decide
  have k3 : ["commit", "fetch_error", "fetched"].Pairwise (· < ·) := by decide
  have hfet : ∀ f, fet = some f → f.utf8ByteSize ≤ maxStringBytes := fun f hf' =>
    utc_size (hf f hf')
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases ex <;> rcases err with _ | ⟨code, det⟩ <;> rcases com with _ | c <;>
      rcases ferr with _ | fe <;>
      rcases fet with _ | ft <;>
      simp [envelopeLayout, intsFit, intsFitMembers, nullOr, clips_ints, hi, maxInt]
  · cases ex <;> rcases err with _ | ⟨code, det⟩ <;> rcases com with _ | c <;>
      rcases ferr with _ | fe <;>
      rcases fet with _ | ft <;>
      simp [envelopeLayout, stringsFit, stringsFitMembers, nullOr, clips_fit, hs, command_size,
        code_size, clip_size, commit_size, hfet] <;>
      decide
  · cases ex <;> rcases err with _ | ⟨code, det⟩ <;> rcases com with _ | c <;>
      rcases ferr with _ | fe <;>
      rcases fet with _ | ft <;>
      simp [envelopeLayout, depth, depthMembers, nullOr, clips_depth, maxDepth] <;>
      omega
  · cases ex <;> rcases err with _ | ⟨code, det⟩ <;> rcases com with _ | c <;>
      rcases ferr with _ | fe <;>
      rcases fet with _ | ft <;>
      simp [envelopeLayout, keysAscend, keysAscendMembers, nullOr, clips_keys, hk, k1, k2, k3]

end FvdepAudit.Doc.Proof
