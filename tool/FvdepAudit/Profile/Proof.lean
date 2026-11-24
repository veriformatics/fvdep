import FvdepAudit.Build.Proof.Key
import FvdepAudit.Doc.Proof.Rules
import FvdepAudit.Doc.Proof.Valid
import FvdepAudit.Json.Proof.Corollaries
import FvdepAudit.Profile.Spec
import FvdepCore.Profile.Check

/-! U6 P5a + P5b (contract `docs/contracts/U6-profile.md`): the request + the record read back
exactly (canonical texts of well-formed values alone); the intake = the spec's first failing
check. -/

namespace FvdepAudit.Profile.Proof

open FvdepCore.Profile
open FvdepAudit.Json.Spec (Valid intsFit intsFitList intsFitMembers stringsFit stringsFitList
  stringsFitMembers depth depthList depthMembers keysAscend keysAscendList keysAscendMembers
  maxStringBytes maxDepth maxInt)
open FvdepCore.Json (Value print decode)

/-! ## J's bounds from the checks -/

theorem digest_fits {s : String} (h : FvdepCore.Doc.isDigest s = true) :
    s.utf8ByteSize ≤ maxStringBytes :=
  FvdepAudit.Doc.Proof.digest_size ((FvdepAudit.Doc.Proof.isDigest_iff s).mp h)

theorem module_fits {s : String} (h : isModule s = true) : s.utf8ByteSize ≤ maxStringBytes := by
  simp only [isModule, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [maxStringBytes]
  omega

theorem label_fits {s : String} (h : isLabel s = true) : s.utf8ByteSize ≤ maxStringBytes := by
  simp only [isLabel, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [maxStringBytes]
  omega

theorem detail_fits {s : String} (h : isDetail s = true) : s.utf8ByteSize ≤ maxStringBytes := by
  simp only [isDetail, detailMax] at h
  have h' : s.utf8ByteSize ≤ 1024 := of_decide_eq_true h
  simp only [maxStringBytes]
  omega

/-- J's four bounds on `v`, its depth at most `k`. -/
def Bounds (v : Value) (k : Nat) : Prop :=
  intsFit v = true ∧ stringsFit v = true ∧ depth v ≤ k ∧ keysAscend v = true

theorem list_bounds {α : Type} (f : α → Value) (k : Nat) (xs : List α)
    (h : ∀ x ∈ xs, Bounds (f x) k) :
    intsFitList (xs.map f) = true ∧
      stringsFitList (xs.map f) = true ∧
      depthList (xs.map f) ≤ k ∧ keysAscendList (xs.map f) = true :=
  ⟨FvdepAudit.Build.Proof.intsFitList_map f xs fun x hx => (h x hx).1,
    FvdepAudit.Build.Proof.stringsFitList_map f xs fun x hx => (h x hx).2.1,
    FvdepAudit.Build.Proof.depthList_map f k xs fun x hx => (h x hx).2.2.1,
    FvdepAudit.Build.Proof.keysAscendList_map f xs fun x hx => (h x hx).2.2.2⟩

theorem strs_bounds (xs : List String) (h : ∀ x ∈ xs, x.utf8ByteSize ≤ maxStringBytes) :
    intsFitList (xs.map .str) = true ∧
      stringsFitList (xs.map .str) = true ∧
      depthList (xs.map .str) ≤ 0 ∧ keysAscendList (xs.map .str) = true :=
  FvdepAudit.Build.Proof.strs_ok xs h

/-! ## The record -/

theorem moduleRec_bounds (m : ModuleRec) (h : m.ok = true) : Bounds m.toJson 2 := by
  simp only [ModuleRec.ok, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hm, hd⟩, hg⟩ := h
  obtain ⟨g1, g2, g3, g4⟩ := strs_bounds m.grammar fun x hx => module_fits (hg x hx)
  have hm' := module_fits hm
  have hd' := digest_fits hd
  simp only [maxStringBytes] at hm' hd' g2
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [ModuleRec.toJson, strs, intsFit, intsFitMembers, g1]
  · simp (config := { decide := true }) [ModuleRec.toJson, strs, stringsFit, stringsFitMembers,
      maxStringBytes, g2, hm', hd']
  · simp only [ModuleRec.toJson, strs, depth, depthMembers]
    omega
  · simp (config := { decide := true }) [ModuleRec.toJson, strs, keysAscend, keysAscendMembers, g4]

theorem outcome_bounds (o : Outcome) (h : o.ok = true) : Bounds o.toJson 3 := by
  cases o with
  | accepted => refine ⟨?_, ?_, ?_, ?_⟩ <;> decide
  | over => refine ⟨?_, ?_, ?_, ?_⟩ <;> decide
  | refused
    r =>
    simp only [Outcome.ok, Refusal.ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨hm, hl1⟩, hl2⟩, hc⟩, hr⟩, hd⟩, -⟩ := h
    obtain ⟨d1, d2, d3, d4⟩ := strs_bounds r.detail fun x hx => detail_fits (hd x hx)
    have hm' := module_fits hm
    have hr' := label_fits hr
    simp only [maxStringBytes] at hm' hr' d2
    simp only [FvdepCore.Json.maxInt] at hl2 hc
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [Outcome.toJson, strs, intsFit, intsFitMembers, d1, maxInt, hc, hl2]
    · simp (config := { decide := true }) [Outcome.toJson, strs, stringsFit, stringsFitMembers,
        maxStringBytes, d2, hm', hr']
    · simp only [Outcome.toJson, strs, depth, depthMembers]
      omega
    · simp (config := { decide := true }) [Outcome.toJson, strs, keysAscend, keysAscendMembers, d4]

theorem record_valid (r : Record) (h : r.ok = true) : Valid r.toJson := by
  simp only [Record.ok, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hms, ho⟩, hp⟩, hrc⟩, hrq⟩ := h
  obtain ⟨m1, m2, m3, m4⟩ :=
    list_bounds ModuleRec.toJson 2 r.modules fun m hm => moduleRec_bounds m (hms m hm)
  obtain ⟨o1, o2, o3, o4⟩ := outcome_bounds r.outcome ho
  have hp' := label_fits hp
  have hrc' := label_fits hrc
  have hrq' := digest_fits hrq
  simp only [maxStringBytes] at hp' hrc' hrq' m2
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp (config := { decide := true }) [Record.toJson, intsFit, intsFitMembers, m1, o1]
  · simp (config := { decide := true }) [Record.toJson, stringsFit, stringsFitMembers,
      maxStringBytes, m2, o2, hp', hrc', hrq']
  · simp only [Record.toJson, depth, depthMembers, maxDepth]
    omega
  · simp (config := { decide := true }) [Record.toJson, keysAscend, keysAscendMembers, m4, o4]

theorem mapM_map {α : Type} (f : Value → Option α) (g : α → Value) (h : ∀ x, f (g x) = some x) :
    ∀ xs : List α, (xs.map g).mapM f = some xs
  | [] => rfl
  | x :: xs => by simp [List.mapM_cons, h, mapM_map f g h xs]

theorem moduleRec_ofJson (m : ModuleRec) : ModuleRec.ofJson m.toJson = some m := by
  simp [ModuleRec.ofJson, ModuleRec.toJson, strs, FvdepAudit.Doc.Proof.strsOf_map]

theorem outcome_ofJson (o : Outcome) : Outcome.ofJson o.toJson = some o := by
  cases o with
  | accepted => simp [Outcome.ofJson, Outcome.toJson]
  | over => simp [Outcome.ofJson, Outcome.toJson]
  | refused r =>
    obtain ⟨m, l, c, rule, d⟩ := r
    simp [Outcome.ofJson, Outcome.toJson, strs, natOf, FvdepAudit.Doc.Proof.strsOf_map]

theorem record_ofJson (r : Record) (h : r.ok = true) : Record.ofJson r.toJson = some r := by
  obtain ⟨ms, o, p, rc, rq⟩ := r
  simp [Record.ofJson, Record.toJson, mapM_map _ _ moduleRec_ofJson, outcome_ofJson, h]

theorem record_ofJson_ok {v : Value} {r : Record} (h : Record.ofJson v = some r) : r.ok = true := by
  unfold Record.ofJson at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, _, _, h⟩ := h
    split at h
    · rename_i hok
      simp only [Option.some.injEq] at h
      subst h
      exact hok
    · simp at h
  · simp at h

/-- P5b `RecordRead`. -/
theorem record_read (r : Record) (h : r.ok = true) : readRecord (print r.toJson) = some r := by
  simp [readRecord, FvdepAudit.Json.Proof.print_decode _ (record_valid r h), Except.toOption,
    record_ofJson r h]

/-- P5b `RecordExact`. -/
theorem record_exact (b : ByteArray) (r : Record) (h : readRecord b = some r) :
    r.ok = true ∧ print r.toJson = b := by
  simp only [readRecord, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, r', hr', h⟩ := h
  split at h
  · rename_i hb
    simp only [Option.some.injEq] at h
    subst h
    simp only [beq_iff_eq] at hb
    exact ⟨record_ofJson_ok hr', (ByteArray.ext hb).symm⟩
  · simp at h

/-! ## The request -/

theorem libModule_bounds (l : LibModule) (h : l.ok = true) : Bounds l.toJson 2 := by
  simp only [LibModule.ok, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hm, hi⟩ := h
  obtain ⟨i1, i2, i3, i4⟩ := strs_bounds l.imports fun x hx => module_fits (hi x hx)
  have hm' := module_fits hm
  simp only [maxStringBytes] at hm' i2
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [LibModule.toJson, strs, intsFit, intsFitMembers, i1]
  · simp (config := { decide := true }) [LibModule.toJson, strs, stringsFit, stringsFitMembers,
      maxStringBytes, i2, hm']
  · simp only [LibModule.toJson, strs, depth, depthMembers]
    omega
  · simp (config := { decide := true }) [LibModule.toJson, strs, keysAscend, keysAscendMembers, i4]

theorem reqModule_bounds (m : ReqModule) (h : m.ok = true) : Bounds m.toJson 1 := by
  simp only [ReqModule.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hm, -⟩, hp⟩, hd⟩ := h
  have hm' := module_fits hm
  have hd' := digest_fits hd
  have hp' : m.path.utf8ByteSize ≤ 65536 := by omega
  simp only [maxStringBytes] at hm' hd'
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [ReqModule.toJson, intsFit, intsFitMembers]
  · simp (config := { decide := true }) [ReqModule.toJson, stringsFit, stringsFitMembers,
      maxStringBytes, hm', hd', hp']
  · simp [ReqModule.toJson, depth, depthMembers]
  · simp (config := { decide := true }) [ReqModule.toJson, keysAscend, keysAscendMembers]

theorem limits_bounds (l : Limits) (h : l.ok = true) : Bounds l.toJson 1 := by
  simp only [Limits.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨-, hd⟩, -⟩, hn⟩, -⟩, hb⟩ := h
  simp only [FvdepCore.Json.maxInt] at hd hn hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Limits.toJson, intsFit, intsFitMembers, maxInt, hd, hn, hb]
  · simp (config := { decide := true }) [Limits.toJson, stringsFit, stringsFitMembers]
  · simp [Limits.toJson, depth, depthMembers]
  · simp (config := { decide := true }) [Limits.toJson, keysAscend, keysAscendMembers]

theorem role_fits (r : Role) : r.text.utf8ByteSize ≤ maxStringBytes := by cases r <;> decide

theorem request_valid (r : Request) (h : r.ok = true) : Valid r.toJson := by
  simp only [Request.ok, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hls, -⟩, hl⟩, hms⟩, -⟩, hp⟩, hrc⟩, -⟩, ht⟩ := h
  obtain ⟨l1, l2, l3, l4⟩ :=
    list_bounds LibModule.toJson 2 r.library fun l hl => libModule_bounds l (hls l hl)
  obtain ⟨q1, q2, q3, q4⟩ :=
    list_bounds ReqModule.toJson 1 r.modules fun m hm => reqModule_bounds m (hms m hm)
  obtain ⟨b1, b2, b3, b4⟩ := limits_bounds r.limits hl
  have hp' := label_fits hp
  have hrc' := label_fits hrc
  have ht' := digest_fits ht
  have hro := role_fits r.role
  simp only [maxStringBytes] at hp' hrc' ht' hro l2 q2
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp (config := { decide := true }) [Request.toJson, intsFit, intsFitMembers, l1, q1, b1]
  · simp (config := { decide := true }) [Request.toJson, stringsFit, stringsFitMembers,
      maxStringBytes, l2, q2, b2, hp', hrc', ht', hro]
  · simp only [Request.toJson, depth, depthMembers, maxDepth]
    omega
  · simp (config := { decide := true }) [Request.toJson, keysAscend, keysAscendMembers, l4, q4, b4]

theorem libModule_ofJson (l : LibModule) : LibModule.ofJson l.toJson = some l := by
  simp [LibModule.ofJson, LibModule.toJson, strs, FvdepAudit.Doc.Proof.strsOf_map]

theorem reqModule_ofJson (m : ReqModule) : ReqModule.ofJson m.toJson = some m := by
  simp [ReqModule.ofJson, ReqModule.toJson]

theorem limits_ofJson (l : Limits) : Limits.ofJson l.toJson = some l := by
  simp [Limits.ofJson, Limits.toJson, natOf]

theorem role_ofText (r : Role) : Role.ofText r.text = some r := by
  cases r <;> simp [Role.ofText, Role.text]

theorem request_ofJson (r : Request) (h : r.ok = true) : Request.ofJson r.toJson = some r := by
  obtain ⟨ls, l, ms, p, rc, ro, t⟩ := r
  simp [Request.ofJson, Request.toJson, mapM_map _ _ libModule_ofJson,
    mapM_map _ _ reqModule_ofJson, limits_ofJson, role_ofText, h]

theorem request_ofJson_ok {v : Value} {r : Request} (h : Request.ofJson v = some r) :
    r.ok = true := by
  unfold Request.ofJson at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, _, _, _, _, _, _, h⟩ := h
    split at h
    · rename_i hok
      simp only [Option.some.injEq] at h
      subst h
      exact hok
    · simp at h
  · simp at h

/-- P5a `RequestRead`. -/
theorem request_read (r : Request) (h : r.ok = true) : readRequest (print r.toJson) = some r := by
  simp [readRequest, FvdepAudit.Json.Proof.print_decode _ (request_valid r h), Except.toOption,
    request_ofJson r h]

/-- P5a `RequestExact`. -/
theorem request_exact (b : ByteArray) (r : Request) (h : readRequest b = some r) :
    r.ok = true ∧ print r.toJson = b := by
  simp only [readRequest, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, r', hr', h⟩ := h
  split at h
  · rename_i hb
    simp only [Option.some.injEq] at h
    subst h
    simp only [beq_iff_eq] at hb
    exact ⟨request_ofJson_ok hr', (ByteArray.ext hb).symm⟩
  · simp at h

/-! ## The intake -/

theorem firstName_eq :
    ∀ (i : Nat) (ms : List ModuleRec) (qs : List ReqModule),
      firstName i ms qs =
        ((FvdepAudit.Profile.Spec.nameChecks i ms qs).find? fun c => !c.1).map (·.2)
  | _, [], _ => by simp [firstName, FvdepAudit.Profile.Spec.nameChecks]
  | _, _ :: _, [] => by simp [firstName, FvdepAudit.Profile.Spec.nameChecks]
  | i, m :: ms, q :: qs => by
    have ih := firstName_eq (i + 1) ms qs
    simp only [FvdepAudit.Profile.Spec.nameChecks] at ih
    by_cases h : m.module = q.module
    · simp [firstName, FvdepAudit.Profile.Spec.nameChecks, h, ih, List.zipIdx_cons]
    · simp [firstName, FvdepAudit.Profile.Spec.nameChecks, h, List.zipIdx_cons]

theorem firstDigest_eq :
    ∀ (ms : List ModuleRec) (qs : List ReqModule),
      firstDigest ms qs =
        ((FvdepAudit.Profile.Spec.digestChecks ms qs).find? fun c => !c.1).map (·.2)
  | [], _ => by simp [firstDigest, FvdepAudit.Profile.Spec.digestChecks]
  | _ :: _, [] => by simp [firstDigest, FvdepAudit.Profile.Spec.digestChecks]
  | m :: ms, q :: qs => by
    have ih := firstDigest_eq ms qs
    simp only [FvdepAudit.Profile.Spec.digestChecks] at ih
    by_cases h : m.sha256 = q.sha256
    · simp [firstDigest, FvdepAudit.Profile.Spec.digestChecks, h, ih]
    · simp [firstDigest, FvdepAudit.Profile.Spec.digestChecks, h]

theorem find?_head (b : Bool) (e : IntakeError) (cs : List (Bool × IntakeError)) :
    ((b, e) :: cs).find? (fun c => !c.1) = if b then cs.find? (fun c => !c.1) else some (b, e) := by
  cases b <;> simp

/-- P5b `IntakeExact`. -/
theorem intake_exact (profile : String) (req : Request) (digest : String) (b : ByteArray) :
    intake profile req digest b = FvdepAudit.Profile.Spec.intake profile req digest b := by
  rcases hr : readRecord b with _ | r
  · simp [intake, FvdepAudit.Profile.Spec.intake, hr, throw, throwThe, MonadExceptOf.throw]
  · simp only [intake, FvdepAudit.Profile.Spec.intake, hr, FvdepAudit.Profile.Spec.checks,
      List.cons_append, find?_head]
    by_cases h1 : (r.profile == profile) = true
    · by_cases h2 : (r.request == digest) = true
      · by_cases h3 : (r.recipe == req.recipe) = true
        · by_cases h4 : (r.modules.length == req.modules.length) = true
          · simp only [h1, h2, h3, h4, ite_true, List.nil_append, List.find?_append, firstName_eq,
              firstDigest_eq]
            rcases hN :
              (FvdepAudit.Profile.Spec.nameChecks 1 r.modules req.modules).find? fun c => !c.1 with
              _ | ⟨bN, eN⟩
            · rcases hD :
                (FvdepAudit.Profile.Spec.digestChecks r.modules req.modules).find? fun c =>
                  !c.1 with
                _ | ⟨bD, eD⟩
              · rcases ho : r.outcome with _ | f | _
                · simp [FvdepAudit.Profile.Spec.outsideChecks, hN, hD, ho, pure, Except.pure]
                · by_cases ha : (req.modules.any fun x => x.module == f.module) = true
                  · simp [FvdepAudit.Profile.Spec.outsideChecks, hN, hD, ho, ha, pure, Except.pure]
                  · simp [FvdepAudit.Profile.Spec.outsideChecks, hN, hD, ho, ha, throw, throwThe,
                      MonadExceptOf.throw, bind, Except.bind]
                · simp [FvdepAudit.Profile.Spec.outsideChecks, hN, hD, ho, pure, Except.pure]
              · simp [hN, hD, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
            · simp [hN, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
          · simp [h1, h2, h3, h4, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
        · simp [h1, h2, h3, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
      · simp [h1, h2, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
    · simp [h1, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-! ## The walk's small claims (U6-B2; the walk's C2 claims = U6-D) -/

theorem go_head (imports : String → List String) :
    ∀ (n : Nat) (frames : List (List String)) (seen acc : List String),
      acc.head? = some "Init" → (grammar.go imports n frames seen acc).head? = some "Init"
  | 0, _, _, _, h => by simpa [grammar.go] using h
  | n + 1, [], _, _, h => by simpa [grammar.go] using h
  | n + 1, [] :: frames, seen, acc, h => by
    simp only [grammar.go]
    exact go_head imports n frames seen acc h
  | n + 1, (i :: is) :: frames, seen, acc, h => by
    simp only [grammar.go]
    split
    · apply go_head imports n
      split
      · exact h
      · cases acc with
        | nil => simp at h
        | cons a as => simpa using h
    · split
      · exact go_head imports n _ _ _ h
      · exact go_head imports n _ _ _ h

/-- P3 `GrammarInit`. -/
theorem grammar_init (imports : String → List String) (fuel : Nat) (m : String) :
    (grammar imports fuel m).head? = some "Init" := go_head imports fuel _ _ _ rfl

theorem takeBytes_sum : ∀ (n : Nat) (cs : List Char), ((takeBytes n cs).map Char.utf8Size).sum ≤ n
  | _, [] => by simp [takeBytes]
  | n, c :: cs => by
    unfold takeBytes
    split
    · have := takeBytes_sum (n - c.utf8Size) cs
      simp only [List.map_cons, List.sum_cons]
      omega
    · simp

/-- T `DetailBytes`. -/
theorem detail_bytes (s : String) : (cutDetail s).utf8ByteSize ≤ detailMax := by
  unfold cutDetail
  split
  · assumption
  · rw [String.utf8ByteSize_append, FvdepAudit.Doc.Proof.bytes_ofList]
    have := takeBytes_sum (detailMax - 3) s.toList
    have h3 : "...".utf8ByteSize = 3 := by decide
    simp only [detailMax] at this ⊢
    omega

end FvdepAudit.Profile.Proof
