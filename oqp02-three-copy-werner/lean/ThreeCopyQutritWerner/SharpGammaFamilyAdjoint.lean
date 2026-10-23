module

public import ThreeCopyQutritWerner.SharpFamilyAnchorSupport
public import ThreeCopyQutritWerner.ZeroFamilies

@[expose] public section


/-!
# Swapping the two saturated families

Adjointing the original ket-bra operators conjugates gamma. Thus the
gamma-one condition is unchanged when the two orthonormal families are
swapped, and the rank-two combination support argument also applies to
the original right family.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

theorem sharp_hsInner_conjTranspose {n : Type*} [Fintype n]
    (A B : Matrix n n ℂ) : hsInner Aᴴ Bᴴ = conj (hsInner A B) := by
  simp only [hsInner, Matrix.conjTranspose_apply, starRingEnd_apply,
    star_sum, star_mul, star_star]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem sharp_ptraceL_conjTranspose {L R : Type*} [Fintype L] [Fintype R]
    (A : Matrix (L × R) (L × R) ℂ) : ptraceL Aᴴ = (ptraceL A)ᴴ := by
  ext i j
  simp only [ptraceL, Matrix.conjTranspose_apply, star_sum]

theorem sharp_ptraceR_conjTranspose {L R : Type*} [Fintype L] [Fintype R]
    (A : Matrix (L × R) (L × R) ℂ) : ptraceR Aᴴ = (ptraceR A)ᴴ := by
  ext i j
  simp only [ptraceR, Matrix.conjTranspose_apply, star_sum]

/-- Interchanging the two original vector families conjugates gamma. -/
theorem sharpPartialTraceGamma_swap_families
    {L R : Type*} [Fintype L] [Fintype R] (u v s t : L × R → ℂ) :
    sharpPartialTraceGamma v u t s = conj (sharpPartialTraceGamma u v s t) := by
  unfold sharpPartialTraceGamma ptraceInner
  rw [← conjTranspose_ketBra u v, ← conjTranspose_ketBra s t,
    sharp_ptraceL_conjTranspose, sharp_ptraceL_conjTranspose,
    sharp_ptraceR_conjTranspose, sharp_ptraceR_conjTranspose,
    sharp_hsInner_conjTranspose, sharp_hsInner_conjTranspose,
    Matrix.trace_conjTranspose, Matrix.trace_conjTranspose]
  simp only [map_sub, map_add, map_mul, starRingEnd_apply,
    star_sub, star_add, star_mul, star_star] <;> ring

/-- A rank-two combination in the original right family also gives one
common annihilator for both original complete families. -/
theorem sharpGammaFamily_right_rank_two_combination_common_coordinates
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u v : ι → Fin 3 × Fin 3 → ℂ)
    (hu : ∀ i j, braket (u i) (u j) = if i = j then 1 else 0)
    (hv : ∀ i j, braket (v i) (v j) = if i = j then 1 else 0)
    (hg : ∀ i j, sharpPartialTraceGamma (u i) (v i) (u j) (v j) = 1)
    (i j : ι) (hij : i ≠ j) (z : ι → ℂ)
    (hz : (sharpReshape (fun r => ∑ k, z k * v k r)).rank = 2) :
    ∃ U : Matrix (Fin 3) (Fin 3) ℂ, ∃ a : Fin 3, Uᴴ * U = 1 ∧
      ∀ k c, (U * sharpReshape (u k)) a c = 0 ∧ (U * sharpReshape (v k)) a c = 0 := by
  have hgs (p q : ι) : sharpPartialTraceGamma (v p) (u p) (v q) (u q) = 1 := by
    rw [sharpPartialTraceGamma_swap_families, hg, map_one]
  obtain ⟨U, a, hU, hs⟩ := sharpGammaFamily_rank_two_combination_common_coordinates
    v u hv hu hgs i j hij z hz
  exact ⟨U, a, hU, fun k c => ⟨(hs k c).2, (hs k c).1⟩⟩

end ThreeCopyQutritWerner
