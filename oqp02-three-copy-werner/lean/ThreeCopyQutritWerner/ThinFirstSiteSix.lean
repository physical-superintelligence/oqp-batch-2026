module

public import ThreeCopyQutritWerner.FirstSiteContraction
public import ThreeCopyQutritWerner.TwoCutQuadratic

@[expose] public section


/-!
# Exact positive decomposition at a thin first output site

With output coordinate two missing, the endpoint form is a positive sum of
eight actual two-site contractions. The remaining two registers have arbitrary
finite dimensions. In particular no three-copy endpoint premise is needed.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

variable {b c : Type*} [Fintype b] [Fintype c] [DecidableEq b] [DecidableEq c]

/-- The four unnormalized binary ray contractions, with their exact phases. -/
theorem firstSiteContraction_pauli_coordinates
    (C : Matrix (Fin 3 × b × c) (Fin 3 × b × c) ℂ) :
    firstSiteContraction C ![1, 1, 0] ![1, -1, 0] =
      (firstSiteBlock C 0 0 - firstSiteBlock C 1 1) +
        (firstSiteBlock C 1 0 - firstSiteBlock C 0 1) ∧
    firstSiteContraction C ![1, -1, 0] ![1, 1, 0] =
      (firstSiteBlock C 0 0 - firstSiteBlock C 1 1) -
        (firstSiteBlock C 1 0 - firstSiteBlock C 0 1) ∧
    firstSiteContraction C ![1, -Complex.I, 0] ![1, Complex.I, 0] =
      (firstSiteBlock C 0 0 - firstSiteBlock C 1 1) +
        Complex.I • (firstSiteBlock C 0 1 + firstSiteBlock C 1 0) ∧
    firstSiteContraction C ![1, Complex.I, 0] ![1, -Complex.I, 0] =
      (firstSiteBlock C 0 0 - firstSiteBlock C 1 1) -
        Complex.I • (firstSiteBlock C 0 1 + firstSiteBlock C 1 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    rw [firstSiteContraction_binary_coordinates] <;>
    ext r s <;>
    simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] <;>
    ring

/-- Literal endpoint decomposition, including both off-plane input blocks. -/
theorem endpointEnergy_missing_first_row_two_six
    (C : Matrix (Fin 3 × b × c) (Fin 3 × b × c) ℂ)
    (hrow : ∀ r q, C (2, r) q = 0) :
    endpointEnergy C =
      cutForm (firstSiteBlock C 0 2) + cutForm (firstSiteBlock C 1 2) +
      cutForm (firstSiteBlock C 0 1) / 2 + cutForm (firstSiteBlock C 1 0) / 2 +
      (cutForm (firstSiteContraction C ![1, 1, 0] ![1, -1, 0]) +
        cutForm (firstSiteContraction C ![1, -1, 0] ![1, 1, 0]) +
        cutForm (firstSiteContraction C ![1, -Complex.I, 0] ![1, Complex.I, 0]) +
        cutForm (firstSiteContraction C ![1, Complex.I, 0] ![1, -Complex.I, 0])) / 8 := by
  have hb (j : Fin 3) : firstSiteBlock C 2 j = 0 := by
    ext r s
    exact hrow r (j, s)
  have ht : ptrace₁ C = firstSiteBlock C 0 0 + firstSiteBlock C 1 1 := by
    rw [ptrace₁_eq_sum_firstSiteBlocks, Fin.sum_univ_three, hb, add_zero]
  have hzero : cutForm (0 : Matrix (b × c) (b × c) ℂ) = 0 := by
    simp [cutForm, frobSq, ptraceL, ptraceR, Matrix.trace]
  obtain ⟨h₁, h₂, h₃, h₄⟩ := firstSiteContraction_pauli_coordinates C
  rw [endpointEnergy_eq_sum_firstSiteBlock_cutForm, ht]
  simp only [Fin.sum_univ_three, hb, hzero, add_zero, h₁, h₂, h₃, h₄]
  have h := cutForm_six_contractions (firstSiteBlock C 0 0)
    (firstSiteBlock C 0 1) (firstSiteBlock C 1 0) (firstSiteBlock C 1 1)
  linarith

/-- Unconditional positivity for the original rank-two matrix with this actual
missing output coordinate. The input is not assumed thin. -/
theorem endpointEnergy_nonneg_of_missing_first_row_two
    (C : Matrix (Fin 3 × b × c) (Fin 3 × b × c) ℂ) (hC : C.rank ≤ 2)
    (hrow : ∀ r q, C (2, r) q = 0) :
    0 ≤ endpointEnergy C := by
  have hc (x y : Fin 3 → ℂ) : 0 ≤ cutForm (firstSiteContraction C x y) :=
    cutForm_nonneg_of_rank_le_two _ ((firstSiteContraction_rank_le C x y).trans hC)
  have hb := firstSiteBlock_cutForm_nonneg C hC
  rw [endpointEnergy_missing_first_row_two_six C hrow]
  exact add_nonneg
    (add_nonneg (add_nonneg (add_nonneg (hb 0 2) (hb 1 2))
      (div_nonneg (hb 0 1) (by norm_num))) (div_nonneg (hb 1 0) (by norm_num)))
    (div_nonneg (add_nonneg (add_nonneg (add_nonneg (hc _ _) (hc _ _))
      (hc _ _)) (hc _ _)) (by norm_num))

end ThreeCopyQutritWerner
