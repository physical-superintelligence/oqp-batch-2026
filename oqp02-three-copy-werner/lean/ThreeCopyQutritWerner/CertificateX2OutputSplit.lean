module

public import ThreeCopyQutritWerner.CertificateX2OutputBlock

@[expose] public section


/-!
# Output stage: memory-bounded checks of a block's output

`x2OutNum` sums three parts; the kernel caches every intermediate value of one declaration, about `(r + 3) N² W` bits per
part (the largest h block at W = 384: ~28 GB). `x2PartNum` isolates one part, and `x2OutNum_of_ranges` assembles the
numerators from checks of one part on a range of output columns each (separate declarations; the columns `c'` of a
range only force their own `Y` columns, so a declaration holds the part's `X` columns and `len` columns of `Y`).
-/

namespace ThreeCopyQutritWerner
namespace X2

/-! ### Range checks of a two-index identity (one declaration per range of output columns) -/

/-- `P c c'` for all `c < r` and `c' ∈ [a, a + len)`. -/
def X2RangeOK (P : ℕ → ℕ → Prop) (r a len : ℕ) : Prop :=
  ∀ c' : ℕ, a ≤ c' → c' < a + len → ∀ c < r, P c c'

theorem X2RangeOK.join {P : ℕ → ℕ → Prop} {r a l1 l2 : ℕ} (h1 : X2RangeOK P r a l1)
    (h2 : X2RangeOK P r (a + l1) l2) : X2RangeOK P r a (l1 + l2) := by
  intro c' ha hb c hc
  by_cases hl : c' < a + l1
  · exact h1 c' ha hl c hc
  · exact h2 c' (by omega) (by omega) c hc

theorem X2RangeOK.of_bool (f g : ℕ → ℕ → ℤ) (r a len : ℕ)
    (h : (List.range' a len).all (fun c' => (List.range r).all (fun c => decide (f c c' = g c c'))) = true) :
    X2RangeOK (fun c c' => f c c' = g c c') r a len := by
  intro c' ha hb c hc
  have h1 := List.all_eq_true.mp h c' (List.mem_range'_1.mpr ⟨ha, hb⟩)
  have h2 := List.all_eq_true.mp h1 c (List.mem_range.mpr hc)
  exact of_decide_eq_true h2

theorem X2RangeOK.all {P : ℕ → ℕ → Prop} {r : ℕ} (h : X2RangeOK P r 0 r) : ∀ c < r, ∀ c' < r, P c c' :=
  fun c hc c' hc' => h c' (Nat.zero_le _) (by omega) c hc

/-- Numerators of part `P ∈ {0, 1, 2}` of block `b`. -/
noncomputable def x2PartNum (W d : ℕ) (b : x2Key 0) (fibS fibA : ℕ → ℕ → ℕ) (Jcols : List ℕ) :
    ℕ → ℕ → ℕ → ℤ
  | 0, c, c' => ent W (W - 1) ((x2ORows W (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2) (x2KeySize 0 b) Jcols
      (x2Part0Cols W d b fibS fibA)
      (jRows W (x2KeySize 0 b) (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2) Jcols
        (gRot0 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2)))).getD c' 0) c
  | 1, c, c' => ent W (W - 1) ((x2ORows W (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2) (x2KeySize 0 b) Jcols
      (x2Part1Cols W d b fibA)
      (jRows W (x2KeySize 0 b) (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2) Jcols
        (gRot1 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2)))).getD c' 0) c
  | _, c, c' => ent W (W - 1) ((x2ORows W (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2) (x2KeySize 0 b) Jcols
      (x2Part2Cols W d b fibA)
      (jRows W (x2KeySize 0 b) (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2) Jcols
        (fun i => i))).getD c' 0) c

theorem x2OutNum_eq_parts (W d : ℕ) (b : x2Key 0) (fibS fibA : ℕ → ℕ → ℕ) (Jcols : List ℕ) (c c' : ℕ) :
    x2OutNum W d b fibS fibA Jcols c c' = x2PartNum W d b fibS fibA Jcols 0 c c' +
      x2PartNum W d b fibS fibA Jcols 1 c c' + x2PartNum W d b fibS fibA Jcols 2 c c' := rfl

/-- A part checked on the output columns `[a, a + len)`. -/
def x2PartRangeOK (W d : ℕ) (b : x2Key 0) (fibS fibA : ℕ → ℕ → ℕ) (Jcols : List ℕ) (P : ℕ)
    (O : ℕ → ℕ → ℤ) (a len : ℕ) : Prop :=
  ∀ c' : ℕ, a ≤ c' → c' < a + len → ∀ c < x2KeySize 0 b, x2PartNum W d b fibS fibA Jcols P c c' = O c c'

/-- Checks of a part on consecutive column ranges join. -/
theorem x2PartRangeOK_join (W d : ℕ) (b : x2Key 0) (fibS fibA : ℕ → ℕ → ℕ) (Jcols : List ℕ) (P : ℕ)
    (O : ℕ → ℕ → ℤ) (a l1 l2 : ℕ) (h1 : x2PartRangeOK W d b fibS fibA Jcols P O a l1)
    (h2 : x2PartRangeOK W d b fibS fibA Jcols P O (a + l1) l2) :
    x2PartRangeOK W d b fibS fibA Jcols P O a (l1 + l2) := by
  intro c' ha hb c hc
  by_cases hl : c' < a + l1
  · exact h1 c' ha hl c hc
  · exact h2 c' (by omega) (by omega) c hc

/-- The block numerators from the three parts, each checked on all output columns. -/
theorem x2OutNum_of_ranges (W d : ℕ) (b : x2Key 0) (fibS fibA : ℕ → ℕ → ℕ) (Jcols : List ℕ)
    (O0 O1 O2 : ℕ → ℕ → ℤ)
    (h0 : x2PartRangeOK W d b fibS fibA Jcols 0 O0 0 (x2KeySize 0 b))
    (h1 : x2PartRangeOK W d b fibS fibA Jcols 1 O1 0 (x2KeySize 0 b))
    (h2 : x2PartRangeOK W d b fibS fibA Jcols 2 O2 0 (x2KeySize 0 b)) :
    ∀ c < x2KeySize 0 b, ∀ c' < x2KeySize 0 b,
      x2OutNum W d b fibS fibA Jcols c c' = O0 c c' + O1 c c' + O2 c c' := by
  intro c hc c' hc'
  rw [x2OutNum_eq_parts, h0 c' (Nat.zero_le _) (by omega) c hc, h1 c' (Nat.zero_le _) (by omega) c hc,
    h2 c' (Nat.zero_le _) (by omega) c hc]

/-- A range check from a Boolean kernel evaluation (one `decide +kernel` per part and range). -/
theorem x2PartRangeOK_of_bool (W d : ℕ) (b : x2Key 0) (fibS fibA : ℕ → ℕ → ℕ) (Jcols : List ℕ) (P : ℕ)
    (O : ℕ → ℕ → ℤ) (a len : ℕ)
    (h : (List.range' a len).all (fun c' => (List.range (x2KeySize 0 b)).all (fun c =>
      decide (x2PartNum W d b fibS fibA Jcols P c c' = O c c'))) = true) :
    x2PartRangeOK W d b fibS fibA Jcols P O a len := by
  intro c' ha hb c hc
  have h1 := List.all_eq_true.mp h c' (List.mem_range'_1.mpr ⟨ha, hb⟩)
  have h2 := List.all_eq_true.mp h1 c (List.mem_range.mpr hc)
  exact of_decide_eq_true h2

end X2
end ThreeCopyQutritWerner
