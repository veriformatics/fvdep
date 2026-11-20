import FvdepAudit.Export.Proof.Line
import FvdepAudit.Protocol.Proof.Lines

/-! Proofs: the export reader's claims (contract `docs/contracts/U5b-oracle.md` X6): `read` = the
spec's run over X1's lines (`linesSpec`: LF-separated, a final LF ends the last line); a refusal
= the run's first violation + its class. -/

namespace FvdepAudit.Export.Proof

open FvdepCore.Json FvdepCore.Export FvdepAudit.Export.Spec FvdepAudit.Protocol.Spec

/-! ## Lines: `lineEnd`'s offsets = `linesSpec`'s segments -/

theorem linesSpec_append_lf {x : List UInt8} (rest : List UInt8) (hx : 0x0A ∉ x) :
    linesSpec (x ++ 0x0A :: rest) = x :: linesSpec rest := by
  simp only [linesSpec, FvdepAudit.Protocol.Proof.segments_append_lf hx]
  have hne := FvdepAudit.Protocol.Proof.segments_ne_nil rest
  cases hs : segments rest with
  | nil => exact absurd hs hne
  | cons s ss =>
    simp only [List.getLast?_cons_cons, List.dropLast_cons_cons]
    by_cases hc : (s :: ss).getLast? = some [] <;> simp [hc]

theorem linesSpec_single {x : List UInt8} (hx : 0x0A ∉ x) (hne : x ≠ []) : linesSpec x = [x] := by
  simp [linesSpec, FvdepAudit.Protocol.Proof.segments_of_no_lf hx, hne]

theorem drop_cons (b : ByteArray) (i : Nat) (h : i < b.size) :
    b.data.toList.drop i = b[i] :: b.data.toList.drop (i + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using h)]
  rfl

theorem lineEnd_eq (b : ByteArray) (i : Nat) (hi : i ≤ b.size) :
    lineEnd b i = i + ((b.data.toList.drop i).takeWhile (· != 0x0A)).length := by
  unfold lineEnd
  split
  · rename_i h
    rw [drop_cons b i h]
    split
    · rename_i hl
      have hl' : b[i] = 0x0A := by simpa using hl
      simp [hl']
    · rename_i hl
      have hl' : b[i] ≠ 0x0A := by simpa using hl
      rw [lineEnd_eq b (i + 1) h]
      simp [hl']
      omega
  · rename_i h
    have : i = b.size := by omega
    subst this
    simp [List.drop_eq_nil_of_le (show b.data.toList.length ≤ b.size by simp)]
termination_by b.size - i

theorem extract_eq (b : ByteArray) (i e : Nat) :
    (b.extract i e).data.toList = (b.data.toList.drop i).take (e - i) := by
  simp [ByteArray.data_extract, Array.toList_extract, List.extract]

/-- X1: the lines from a line's start = its segment, then the lines after its LF. -/
theorem lines_drop (b : ByteArray) (i : Nat) (hi : i < b.size) :
    linesSpec (b.data.toList.drop i) =
      (b.extract i (lineEnd b i)).data.toList ::
        linesSpec (b.data.toList.drop (lineEnd b i + 1)) := by
  have he := lineEnd_eq b i (Nat.le_of_lt hi)
  have hsplit :=
    List.takeWhile_append_dropWhile (p := fun x : UInt8 => x != 0x0A) (l := b.data.toList.drop i)
  generalize hl : b.data.toList.drop i = l at hsplit he
  generalize hs : l.takeWhile (fun x : UInt8 => x != 0x0A) = s at hsplit he
  generalize hr : l.dropWhile (fun x : UInt8 => x != 0x0A) = r at hsplit
  have hseg : (b.extract i (lineEnd b i)).data.toList = s := by
    rw [extract_eq, he, Nat.add_sub_cancel_left, hl, ← hsplit]
    exact List.take_left' rfl
  have hnolf : 0x0A ∉ s := fun hm => by
    rw [← hs] at hm
    have := List.all_eq_true.1 (List.all_takeWhile (p := fun x : UInt8 => x != 0x0A) (l := l)) _ hm
    simp at this
  have hrest : b.data.toList.drop (lineEnd b i) = r := by
    rw [he, ← List.drop_drop, hl, ← hsplit]
    exact List.drop_left' rfl
  rw [hseg]
  cases r with
  | nil =>
    have hne : s ≠ [] := by
      rintro rfl
      have : b.data.toList.drop i ≠ [] := by simpa using hi
      rw [hl, ← hsplit] at this
      exact this rfl
    rw [← hsplit, List.append_nil, linesSpec_single hnolf hne]
    have hend : b.data.toList.drop (lineEnd b i + 1) = [] := by
      rw [← List.drop_drop, hrest]
      rfl
    rw [hend]
    rfl
  | cons c
    rest =>
    have hc : c = 0x0A := by
      have h1 :=
        List.head_dropWhile_not (fun x : UInt8 => x != 0x0A) (l := l)
          (by
            rw [hr]; exact List.cons_ne_nil _ _)
      simp only [hr, List.head_cons] at h1
      simpa using h1
    subst hc
    have hend : b.data.toList.drop (lineEnd b i + 1) = rest := by
      rw [← List.drop_drop, hrest]
      rfl
    rw [← hsplit, linesSpec_append_lf rest hnolf, hend]

theorem lines_end (b : ByteArray) (i : Nat) (hi : ¬i < b.size) :
    linesSpec (b.data.toList.drop i) = [] := by
  have : b.data.toList.drop i = [] := List.drop_eq_nil_of_le (by simpa using hi)
  rw [this]
  rfl

/-! ## One line -/

theorem jsonStep_eq (x : ByteArray) :
    jsonStep x.data.toList =
      match decode x with
      | .ok v => .ok v
      | .error .tooLarge => .error .profile
      | .error _ => .error .malformed := by
  cases x
  simp only [jsonStep, Array.toArray_toList]
  rfl

theorem applySpec_dense {t : Tables} {r : Raw} {t' : Tables} (h : ApplySpec t r t') :
    Dense t r := by cases r <;> simp_all [ApplySpec, Dense]

theorem recordStep_ok (t : Tables) (v : Value) (t' : Tables) :
    (parseLine v >>= apply t) = .ok t' ↔ RecordStep t v (.ok t') := by
  rw [bind_ok]
  constructor
  · rintro ⟨r, hr, ha⟩
    exact .ok r t' ((parseLine_ok v r).1 hr) ((apply_ok t r t').1 ha)
  · intro h
    cases h with
    | ok r _ hv ha => exact ⟨r, (parseLine_ok v r).2 hv, (apply_ok t r t').2 ha⟩

theorem recordStep_error (t : Tables) (v : Value) (c : Class) :
    (∃ w, (parseLine v >>= apply t) = .error (c, w)) ↔ RecordStep t v (.error c) := by
  constructor
  · rintro ⟨w, h⟩
    rcases (bind_error _ _ _).1 h with h | ⟨r, hr, h⟩
    · have hcls := parseLine_class v c w h
      have hno : ∀ r, v ≠ rawLayout r := fun r hv => by
        rw [(parseLine_ok v r).2 hv] at h
        cases h
      cases c with
      | profile => exact .mdata (hcls.1 rfl)
      | malformed => exact .shape hno fun hm => absurd (hcls.2 hm) (by decide)
    · have hv := (parseLine_ok v r).1 hr
      have hcls := apply_class t r c w h
      have hno : ∀ t', ¬ApplySpec t r t' := fun t' ha => by
        rw [(apply_ok t r t').2 ha] at h
        cases h
      cases c with
      | profile => exact .sparse r hv (hcls.1 rfl)
      | malformed =>
        exact .unbound r hv (Classical.byContradiction fun hd => absurd (hcls.2 hd) (by decide)) hno
  · intro h
    cases h with
    | mdata hm =>
      cases hp : parseLine v with
      | ok r =>
        exact
          absurd
            (by
              rw [(parseLine_ok v r).1 hp] at hm; exact hm)
            (rawLayout_not_mdata r)
      | error e =>
        obtain ⟨c', w⟩ := e
        have := (parseLine_class v c' w hp).2 hm
        subst this
        exact ⟨w, rfl⟩
    | shape hno hm =>
      cases hp : parseLine v with
      | ok r => exact absurd ((parseLine_ok v r).1 hp) (hno r)
      | error e =>
        obtain ⟨c', w⟩ := e
        have hcls := parseLine_class v c' w hp
        cases c' with
        | profile => exact absurd (hcls.1 rfl) hm
        | malformed => exact ⟨w, rfl⟩
    | sparse r hv hd =>
      have hp := (parseLine_ok v r).2 hv
      cases ha : apply t r with
      | ok t' => exact absurd (applySpec_dense ((apply_ok t r t').1 ha)) hd
      | error e =>
        obtain ⟨c', w⟩ := e
        have := (apply_class t r c' w ha).2 hd
        subst this
        exact
          ⟨w, by
            rw [hp]; exact ha⟩
    | unbound r hv hd hno =>
      have hp := (parseLine_ok v r).2 hv
      cases ha : apply t r with
      | ok t' => exact absurd ((apply_ok t r t').1 ha) (hno t')
      | error e =>
        obtain ⟨c', w⟩ := e
        have hcls := apply_class t r c' w ha
        cases c' with
        | profile => exact absurd (hcls.1 rfl) (fun h => h hd)
        | malformed =>
          exact
            ⟨w, by
              rw [hp]; exact ha⟩

theorem headerShape_layout (g v : String) : HeaderShape (headerLayout g v) := ⟨_, _, _, _, _, rfl⟩

theorem headerStep_ok (githash version : String) (v : Value) :
    header githash version v = .ok () ↔ HeaderStep githash version v (.ok ()) := by
  rw [header_ok]
  constructor
  · exact .ok
  · intro h
    cases h with
    | ok hv => exact hv

theorem headerStep_error (githash version : String) (v : Value) (c : Class) :
    (∃ w, header githash version v = .error (c, w)) ↔ HeaderStep githash version v (.error c) := by
  constructor
  · rintro ⟨w, h⟩
    have hcls := header_class githash version v c w h
    have hne : v ≠ headerLayout githash version := fun hv => by
      rw [(header_ok githash version v).2 hv] at h
      cases h
    cases c with
    | profile => exact .other (hcls.1 rfl) hne
    | malformed => exact .shape fun hs => absurd (hcls.2 hs) (by decide)
  · intro h
    cases hh : header githash version v with
    | ok
      u =>
      have hv :=
        (header_ok githash version v).1
          (by
            cases u; exact hh)
      cases h with
      | other _ hne => exact absurd hv hne
      | shape hs => exact absurd (hv ▸ headerShape_layout githash version) hs
    | error e =>
      obtain ⟨c', w⟩ := e
      have hcls := header_class githash version v c' w hh
      refine ⟨w, ?_⟩
      cases h with
      | other hs _ =>
        have := hcls.2 hs
        subst this
        rfl
      | shape hs =>
        cases c' with
        | profile => exact absurd (hcls.1 rfl) hs
        | malformed => rfl

/-! ## The run as a function -/

/-- Line 1's verdict as a value. -/
def headerOut (githash version : String) (v : Value) : Except Class Unit :=
  match header githash version v with
  | .ok () => .ok ()
  | .error e => .error e.1

/-- A record line's verdict as a value. -/
def recordOut (t : Tables) (v : Value) : Except Class Tables :=
  match parseLine v >>= apply t with
  | .ok t' => .ok t'
  | .error e => .error e.1

theorem headerStep_iff (githash version : String) (v : Value) (o : Except Class Unit) :
    HeaderStep githash version v o ↔ o = headerOut githash version v := by
  unfold headerOut
  cases o with
  | ok u =>
    cases u
    rw [← headerStep_ok]
    cases header githash version v <;> simp
  | error c =>
    rw [← headerStep_error]
    cases header githash version v with
    | ok u => simp
    | error e =>
      obtain ⟨c', w⟩ := e
      simp only [Except.error.injEq, Prod.mk.injEq]
      exact ⟨fun ⟨_, h, _⟩ => h.symm, fun h => ⟨w, h.symm, rfl⟩⟩

theorem recordStep_iff (t : Tables) (v : Value) (o : Except Class Tables) :
    RecordStep t v o ↔ o = recordOut t v := by
  unfold recordOut
  cases o with
  | ok t' =>
    rw [← recordStep_ok]
    cases parseLine v >>= apply t <;> simp [eq_comm]
  | error c =>
    rw [← recordStep_error]
    cases parseLine v >>= apply t with
    | ok u => simp
    | error e =>
      obtain ⟨c', w⟩ := e
      simp only [Except.error.injEq, Prod.mk.injEq]
      exact ⟨fun ⟨_, h, _⟩ => h.symm, fun h => ⟨w, h.symm, rfl⟩⟩

/-- One line's verdict as a value: the next tables, or `(line, class)`. -/
def stepOut (githash version : String) (k : Nat) (t : Tables) (l : List UInt8) :
    Except (Nat × Class) Tables :=
  match jsonStep l with
  | .error c => .error (k, c)
  | .ok v =>
    if k = 1 then
      match headerOut githash version v with
      | .error c => .error (1, c)
      | .ok () => .ok t
    else
      match recordOut t v with
      | .error c => .error (k, c)
      | .ok t' => .ok t'

/-- The run over the lines as a function. -/
def runOut (githash version : String) :
    Nat → Tables → List (List UInt8) → Except (Nat × Class) Tables
  | k, t, [] => if k = 1 then .error (1, .malformed) else .ok t
  | k, t, l :: ls =>
    match stepOut githash version k t l with
    | .error e => .error e
    | .ok t' => runOut githash version (k + 1) t' ls

theorem run_iff (githash version : String) :
    ∀ (ls : List (List UInt8)) (k : Nat) (t : Tables) (o : Except (Nat × Class) Tables),
      1 ≤ k → (Run githash version k t ls o ↔ o = runOut githash version k t ls)
  | [], k, t, o, hk => by
    constructor
    · intro h
      cases h with
      | noHeader => simp [runOut]
      | done _ _ h2 =>
        have : k ≠ 1 := by omega
        simp [runOut, this]
    · intro h
      subst h
      by_cases h1 : k = 1
      · subst h1
        simp only [runOut, ↓reduceIte]
        exact .noHeader t
      · simp only [runOut, h1, ↓reduceIte]
        exact .done k t (by omega)
  | l :: ls, k, t, o, hk => by
    constructor
    · intro h
      cases h with
      | json _ _ _ _ c hj => simp [runOut, stepOut, hj]
      | headerBad _ _ _ v c hj hh => simp [runOut, stepOut, hj, ← (headerStep_iff _ _ _ _).1 hh]
      | header _ _ _ v o hj hh
        hr =>
        rw [(run_iff githash version ls 2 t o (by omega)).1 hr]
        simp [runOut, stepOut, hj, ← (headerStep_iff _ _ _ _).1 hh]
      | recordBad _ _ _ _ v c h2 hj hr =>
        have : k ≠ 1 := by omega
        simp [runOut, stepOut, hj, this, ← (recordStep_iff _ _ _).1 hr]
      | record _ _ t' _ _ v o h2 hj hr hrun =>
        have : k ≠ 1 := by omega
        rw [(run_iff githash version ls (k + 1) t' o (by omega)).1 hrun]
        simp [runOut, stepOut, hj, this, ← (recordStep_iff _ _ _).1 hr]
    · intro h
      subst h
      cases hj : jsonStep l with
      | error c =>
        simp only [runOut, stepOut, hj]
        exact .json k t l ls c hj
      | ok v =>
        by_cases h1 : k = 1
        · subst h1
          cases hh : headerOut githash version v with
          | error c =>
            simp only [runOut, stepOut, hj, hh, ↓reduceIte]
            exact .headerBad t l ls v c hj ((headerStep_iff _ _ _ _).2 hh.symm)
          | ok u =>
            cases u
            simp only [runOut, stepOut, hj, hh, ↓reduceIte]
            exact
              .header t l ls v _ hj ((headerStep_iff _ _ _ _).2 hh.symm)
                ((run_iff githash version ls 2 t _ (by omega)).2 rfl)
        · cases hr : recordOut t v with
          | error c =>
            simp only [runOut, stepOut, hj, hr, h1, ↓reduceIte]
            exact .recordBad k t l ls v c (by omega) hj ((recordStep_iff _ _ _).2 hr.symm)
          | ok t' =>
            simp only [runOut, stepOut, hj, hr, h1, ↓reduceIte]
            exact
              .record k t t' l ls v _ (by omega) hj ((recordStep_iff _ _ _).2 hr.symm)
                ((run_iff githash version ls (k + 1) t' _ (by omega)).2 rfl)

/-! ## `readFrom` = the run -/

/-- A refusal's line + class. -/
def strip : Except Refusal Tables → Except (Nat × Class) Tables
  | .ok t => .ok t
  | .error r => .error (r.line, r.cls)

/-- A line's result at line `k`: the next tables, or `(k, class)`. -/
def lineOut (k : Nat) : R Tables → Except (Nat × Class) Tables
  | .ok t => .ok t
  | .error e => .error (k, e.1)

theorem lineStep_eq (githash version : String) (k : Nat) (t : Tables) (x : ByteArray) :
    lineOut k (lineStep githash version k t x) = stepOut githash version k t x.data.toList := by
  rw [stepOut, jsonStep_eq]
  unfold lineStep
  cases hd : decode x with
  | error e => cases e <;> simp [lineOut, outside, bad]
  | ok v =>
    by_cases h1 : k = 1
    · subst h1
      simp only [headerOut, ↓reduceIte, beq_self_eq_true]
      cases header githash version v <;> simp [lineOut, Except.map]
    · simp only [recordOut, h1, ↓reduceIte, beq_iff_eq]
      cases parseLine v >>= apply t <;> simp [lineOut]

/-- `readFrom` from a line's start = the run over the lines from there. -/
theorem readFrom_strip (githash version : String) (b : ByteArray) (i k : Nat) (t : Tables)
    (hk : 1 ≤ k) :
    strip (readFrom githash version b k t i) =
      runOut githash version k t (linesSpec (b.data.toList.drop i)) := by
  rw [readFrom]
  by_cases hi : i < b.size
  · have hle := le_lineEnd b i (Nat.le_of_lt hi)
    have hl := lineStep_eq githash version k t (b.extract i (lineEnd b i))
    simp only [hi, ↓reduceDIte]
    rw [lines_drop b i hi, runOut, ← hl]
    cases lineStep githash version k t (b.extract i (lineEnd b i)) with
    | ok t' =>
      simp only [lineOut]
      exact readFrom_strip githash version b (lineEnd b i + 1) (k + 1) t' (by omega)
    | error e => simp [lineOut, strip]
  · simp only [hi, ↓reduceDIte, lines_end b i hi, runOut]
    by_cases h1 : k = 1
    · simp [h1, strip]
    · simp [h1, strip]
termination_by b.size - i

/-! ## The claims -/

theorem initial_eq : ({} : Tables) = initial := rfl

/-- X6 `readAccepts`: `read` accepts exactly the exports whose run from the initial tables is in
the profile, + returns the final tables' declarations in line order. -/
theorem read_accepts (g v : String) (b : ByteArray) (ds : List Decl) :
    read g v b = .ok ds ↔
      ∃ t, Run g v 1 initial (linesSpec b.data.toList) (.ok t) ∧ ds = t.decls.toList := by
  have h := readFrom_strip g v b 0 1 {} (Nat.le_refl 1)
  rw [List.drop_zero, initial_eq] at h
  unfold FvdepCore.Export.read
  constructor
  · intro hr
    cases hrf : readFrom g v b 1 initial 0 with
    | ok t =>
      rw [initial_eq, hrf] at hr
      simp only [Except.map, Except.ok.injEq] at hr
      refine ⟨t, (run_iff _ _ _ _ _ _ (Nat.le_refl 1)).2 ?_, hr.symm⟩
      rw [← h, hrf]
      rfl
    | error r =>
      rw [initial_eq, hrf] at hr
      cases hr
  · rintro ⟨t, hrun, rfl⟩
    have ho := (run_iff _ _ _ _ _ _ (Nat.le_refl 1)).1 hrun
    rw [← h] at ho
    rw [initial_eq]
    cases hrf : readFrom g v b 1 initial 0 with
    | ok t' =>
      rw [hrf] at ho
      simp only [strip, Except.ok.injEq] at ho
      subst ho
      rfl
    | error r =>
      rw [hrf] at ho
      cases ho

/-- X6 `readFirst`: `read` refuses at line `k` with class `c` exactly when the run's first
violation is line `k`, of class `c`. -/
theorem read_first (g v : String) (b : ByteArray) (k : Nat) (c : Class) :
    (∃ why, read g v b = .error ⟨k, c, why⟩) ↔
      Run g v 1 initial (linesSpec b.data.toList) (.error (k, c)) := by
  have h := readFrom_strip g v b 0 1 {} (Nat.le_refl 1)
  rw [List.drop_zero, initial_eq] at h
  rw [run_iff _ _ _ _ _ _ (Nat.le_refl 1), ← h]
  unfold FvdepCore.Export.read
  rw [initial_eq]
  cases readFrom g v b 1 initial 0 with
  | ok t => simp [Except.map, strip]
  | error r =>
    obtain ⟨line, cls, why⟩ := r
    simp only [Except.map, Except.error.injEq, strip, Refusal.mk.injEq]
    constructor
    · rintro ⟨w, rfl, rfl, rfl⟩
      rfl
    · intro he
      simp only [Prod.mk.injEq] at he
      exact ⟨why, he.1.symm, he.2.symm, rfl⟩

end FvdepAudit.Export.Proof
