/-!
# base64.encode 1.0.0 — RFC 4648 §4, standard alphabet, padded

Bytes = `List Nat`, each `< 256` (obligations take that as hypothesis).
Output: 4 alphabet chars per 3-byte group; a short last group is padded with `=`.
The alphabet helpers (`chars`, `sym`, `val`) are shared with `base64.decode`.
-/
namespace Fvdep.Base64.Encode.V1_0_0

def chars : List Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList

def sym (i : Nat) : Char := chars.getD i '='
def val (c : Char) : Option Nat := chars.idxOf? c

def encode : List Nat → List Char
  | a :: b :: c :: rest =>
    let n := a * 65536 + b * 256 + c
    sym (n / 262144) :: sym (n / 4096 % 64) :: sym (n / 64 % 64) :: sym (n % 64) :: encode rest
  | [a, b] =>
    let n := a * 65536 + b * 256
    [sym (n / 262144), sym (n / 4096 % 64), sym (n / 64 % 64), '=']
  | [a] =>
    let n := a * 65536
    [sym (n / 262144), sym (n / 4096 % 64), '=', '=']
  | [] => []

def encodeStr (bs : List Nat) : String := String.ofList (encode bs)

/-! ## Alphabet lemmas (used by the decode modules) -/

theorem chars_length : chars.length = 64 := by decide

set_option maxRecDepth 8000 in
theorem val_sym : ∀ i, i < 64 → val (sym i) = some i := by decide

set_option maxRecDepth 8000 in
theorem sym_ne_pad : ∀ i, i < 64 → sym i ≠ '=' := by decide

set_option maxRecDepth 8000 in
theorem sym_mem : ∀ i, i < 64 → sym i ∈ chars := by decide

theorem val_spec {c : Char} {i : Nat} (h : val c = some i) : i < 64 ∧ sym i = c := by
  obtain ⟨hi, hc, -⟩ := List.idxOf?_eq_some_iff.mp h
  refine ⟨chars_length ▸ hi, ?_⟩
  simp [sym, List.getD, hi, hc]

theorem encode_eq_nil {bs : List Nat} : encode bs = [] ↔ bs = [] := by
  constructor
  · intro h
    rcases bs with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩ <;> simp [encode] at h ⊢
  · rintro rfl; rfl

/-! ## Obligations -/

/-- Output length: 4 chars per started 3-byte group. -/
theorem encode_length (bs : List Nat) : (encode bs).length = 4 * ((bs.length + 2) / 3) := by
  induction bs using encode.induct with
  | case1 a b c rest ih => simp only [encode, List.length_cons, ih]; omega
  | case2 | case3 | case4 => simp [encode]

/-- Output uses the standard alphabet + `=` alone. -/
theorem encode_alphabet (bs : List Nat) (h : ∀ b ∈ bs, b < 256) :
    ∀ c ∈ encode bs, c ∈ chars ∨ c = '=' := by
  induction bs using encode.induct with
  | case1 a b c rest ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h
    obtain ⟨ha, hb, hc, hr⟩ := h
    simp only [encode, List.mem_cons]
    rintro x (rfl | rfl | rfl | rfl | hx)
    all_goals first | exact ih hr x hx | exact .inl (sym_mem _ (by omega))
  | case2 a b =>
    simp only [List.mem_cons, forall_eq_or_imp, List.not_mem_nil] at h
    obtain ⟨ha, hb, -⟩ := h
    simp only [encode, List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl | rfl)
    all_goals first | exact .inr rfl | exact .inl (sym_mem _ (by omega))
  | case3 a =>
    simp only [List.mem_cons, forall_eq_or_imp, List.not_mem_nil] at h
    obtain ⟨ha, -⟩ := h
    simp only [encode, List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl | rfl)
    all_goals first | exact .inr rfl | exact .inl (sym_mem _ (by omega))
  | case4 => simp [encode]

end Fvdep.Base64.Encode.V1_0_0
