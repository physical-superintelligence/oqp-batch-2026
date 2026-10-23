module

public import ThreeCopyQutritWerner.NuclearTraceEquality

@[expose] public section


/-!
# Recovering source kernels from saturated exterior transitions

A nonzero second compound detects the original kernel through its action on
all decomposable wedges. Thus equality of the actual exterior kernels, proved
from transition saturation, gives equality of the original source kernels.
No matrix rank classification or selected numerical minors are assumed.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

/-- The unnormalized decomposable exterior vector in ordered-pair coordinates. -/
def zeroReserveWedge {n : Type*} (v w : n → ℂ) : n × n → ℂ :=
  fun p => v p.1 * w p.2 - v p.2 * w p.1

/-- The half-minor compound sends the literal wedge to the wedge of the images,
with no remaining normalization factor. -/
theorem zeroReserveCompound_mulVec_wedge {m n : Type*} [Fintype n]
    (A : Matrix m n ℂ) (v w : n → ℂ) :
    zeroReserveCompound A *ᵥ zeroReserveWedge v w =
      zeroReserveWedge (A *ᵥ v) (A *ᵥ w) := by
  let W : Matrix n (Fin 2) ℂ := fun i => ![v i, w i]
  have h := zeroReserveCompound_mul A W
  funext p
  have hp := congrFun (congrFun h p) (0, 1)
  change ((∑ k, A p.1 k * v k) * (∑ k, A p.2 k * w k) -
      (∑ k, A p.1 k * w k) * (∑ k, A p.2 k * v k)) / 2 =
    ∑ i : n × n, ((A p.1 i.1 * A p.2 i.2 - A p.1 i.2 * A p.2 i.1) / 2) *
      ((v i.1 * w i.2 - w i.1 * v i.2) / 2) at hp
  have hw (i j : n) : v i * w j - w i * v j = v i * w j - v j * w i := by ring
  simp only [hw, ← mul_div_assoc, ← Finset.sum_div] at hp
  simp only [zeroReserveCompound, zeroReserveWedge, Matrix.mulVec, dotProduct]
  linear_combination -2 * hp

/-- A nonzero second compound exactly detects the original kernel: a vector is
in that kernel iff every wedge through it is in the exterior kernel. -/
theorem zeroReserveCompound_kernel_detects {m n : Type*} [Fintype n]
    (A : Matrix m n ℂ) (hA : zeroReserveCompound A ≠ 0) (v : n → ℂ) :
    A *ᵥ v = 0 ↔ ∀ w : n → ℂ,
      zeroReserveCompound A *ᵥ zeroReserveWedge v w = 0 := by
  classical
  constructor
  · intro hv w
    rw [zeroReserveCompound_mulVec_wedge, hv]
    funext p
    simp [zeroReserveWedge]
  · intro hv
    by_contra hn
    have hex : ∃ i, (A *ᵥ v) i ≠ 0 := by
      by_contra hh
      push_neg at hh
      apply hn
      funext i
      exact hh i
    obtain ⟨i, hi⟩ := hex
    have hcol (j : m) (k : n) :
        (A *ᵥ v) i * A j k - (A *ᵥ v) j * A i k = 0 := by
      have hh := congrFun (hv (Pi.single k 1)) (i, j)
      rw [zeroReserveCompound_mulVec_wedge] at hh
      simpa only [zeroReserveWedge, Matrix.mulVec_single_one, Matrix.col_apply, Pi.zero_apply] using hh
    have hfactor (j : m) (k : n) :
        A j k = ((A *ᵥ v) j * A i k) / (A *ᵥ v) i := by
      apply (eq_div_iff hi).mpr
      linear_combination hcol j k
    apply hA
    ext ⟨j, l⟩ ⟨k, t⟩
    change (A j k * A l t - A j t * A l k) / 2 = 0
    rw [hfactor j k, hfactor l t, hfactor j t, hfactor l k]
    ring

/-- Equal exterior kernels determine equal original kernels when both second
compounds are nonzero. This works in arbitrary finite input dimension. -/
theorem zeroReserve_kernel_eq_of_exterior_kernel_eq
    {m p n : Type*} [Fintype n]
    (A : Matrix m n ℂ) (B : Matrix p n ℂ)
    (hA : zeroReserveCompound A ≠ 0) (hB : zeroReserveCompound B ≠ 0)
    (hker : ∀ z : n × n → ℂ,
      zeroReserveCompound A *ᵥ z = 0 ↔ zeroReserveCompound B *ᵥ z = 0)
    (v : n → ℂ) : A *ᵥ v = 0 ↔ B *ᵥ v = 0 := by
  rw [zeroReserveCompound_kernel_detects A hA, zeroReserveCompound_kernel_detects B hB]
  exact forall_congr' fun w => hker (zeroReserveWedge v w)

/-- Positive-entropy equality in the actual exterior transition estimate gives
equal kernels of the original two cut flattenings. -/
theorem zeroReserve_transition_equality_kernel {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m]
    (A B : Matrix m n ℂ)
    (hA : 0 < frobSq (zeroReserveCompound A))
    (hB : 0 < frobSq (zeroReserveCompound B))
    (heq : nuclearTrace (A * Bᴴ) ^ 2 - frobSq (A * Bᴴ) =
      Real.sqrt ((frobSq A ^ 2 - frobSq (Aᴴ * A)) *
        (frobSq B ^ 2 - frobSq (Bᴴ * B))))
    (v : n → ℂ) : A *ᵥ v = 0 ↔ B *ᵥ v = 0 := by
  have hAn : zeroReserveCompound A ≠ 0 := by
    intro h
    simp [h, frobSq] at hA
  have hBn : zeroReserveCompound B ≠ 0 := by
    intro h
    simp [h, frobSq] at hB
  exact zeroReserve_kernel_eq_of_exterior_kernel_eq A B hAn hBn
    (nuclearTrace_transition_equality_exterior_kernel A B hA hB heq) v

end ThreeCopyQutritWerner
