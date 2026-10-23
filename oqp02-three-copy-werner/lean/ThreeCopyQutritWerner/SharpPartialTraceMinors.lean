module

public import ThreeCopyQutritWerner.SharpPartialTraceEquality
public import Mathlib.LinearAlgebra.Matrix.Adjugate

@[expose] public section


/-!
# Polarized minors of sharp partial-trace extremizers

The double-antisymmetric null equation is the literal polarized 2×2-minor
system. In a three-by-three reshape, its derivative-adjugate identity implies
that a nonzero partner forces determinant zero. Thus each common combination
of a qutrit extremizer's singular vectors has reshape rank at most two.
This is pointwise rank, not a common two-dimensional local support theorem.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

/-- The derivative of a 2×2 minor of A in direction B, with no conjugation. -/
def sharpPolarizedMinor {L R : Type*} (A B : Matrix L R ℂ)
    (i j : L) (k l : R) : ℂ :=
  A i k * B j l + B i k * A j l - A i l * B j k - B i l * A j k

/-- The replica null equation is exactly the polarized minor system. -/
theorem sharpDoubleAnti_tensor_null_iff {L R : Type*}
    (u v : L × R → ℂ) :
    sharpDoubleAnti (sharpTensorRay u v) = 0 ↔
      ∀ i j k l, sharpPolarizedMinor (sharpReshape u) (sharpReshape v) i j k l = 0 := by
  constructor
  · intro h i j k l
    have he := congrFun (congrFun h (i, k)) (j, l)
    simp only [sharpDoubleAnti, sharpSwapLeft, sharpSwapRight, sharpTensorRay,
      Matrix.zero_apply] at he
    unfold sharpPolarizedMinor sharpReshape
    linear_combination 4 * he
  · intro h
    ext ⟨i, k⟩ ⟨j, l⟩
    have he := h i j k l
    simp only [sharpPolarizedMinor, sharpReshape] at he
    simp only [sharpDoubleAnti, sharpSwapLeft, sharpSwapRight, sharpTensorRay,
      Matrix.zero_apply]
    linear_combination he / 4

/-- The derivative of the three-by-three adjugate, specified by its nine cofactors. -/
def sharpPolarAdjugate (A B : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![sharpPolarizedMinor A B 1 2 1 2, -sharpPolarizedMinor A B 0 2 1 2,
      sharpPolarizedMinor A B 0 1 1 2;
    -sharpPolarizedMinor A B 1 2 0 2, sharpPolarizedMinor A B 0 2 0 2,
      -sharpPolarizedMinor A B 0 1 0 2;
    sharpPolarizedMinor A B 1 2 0 1, -sharpPolarizedMinor A B 0 2 0 1,
      sharpPolarizedMinor A B 0 1 0 1]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
/-- The cofactor derivative identity is polynomial, so it remains valid on
singular matrices and introduces no inverse or rank premise. -/
theorem sharpPolarAdjugate_identity (A B : Matrix (Fin 3) (Fin 3) ℂ) :
    (2 * A.det) • B = (A * sharpPolarAdjugate A B).trace • A -
      (2 : ℂ) • (A * sharpPolarAdjugate A B * A) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sharpPolarAdjugate, sharpPolarizedMinor, Matrix.det_fin_three,
      Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, Matrix.mul_apply,
      Matrix.trace, Matrix.diag_apply, Fin.sum_univ_three] <;> ring

/-- A nonzero polarized-null partner forces a three-by-three determinant to vanish. -/
theorem sharpPolarizedMinor_det_eq_zero (A B : Matrix (Fin 3) (Fin 3) ℂ)
    (hB : B ≠ 0) (h : ∀ i j k l, sharpPolarizedMinor A B i j k l = 0) :
    A.det = 0 := by
  have hD : sharpPolarAdjugate A B = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sharpPolarAdjugate, h]
  have hid := sharpPolarAdjugate_identity A B
  rw [hD, Matrix.mul_zero, Matrix.zero_mul, Matrix.trace_zero, zero_smul,
    smul_zero, sub_zero] at hid
  by_contra hdet
  apply hB
  ext i j
  have he := congrFun (congrFun hid i) j
  change (2 * A.det) * B i j = 0 at he
  exact (mul_eq_zero.mp he).resolve_left (mul_ne_zero (by norm_num) hdet)

/-- A singular three-by-three complex matrix has rank at most two. -/
theorem sharp_rank_le_two_of_det_eq_zero (A : Matrix (Fin 3) (Fin 3) ℂ)
    (hdet : A.det = 0) : A.rank ≤ 2 := by
  have hle : A.rank ≤ 3 := (Matrix.rank_le_card_height A).trans_eq (Fintype.card_fin 3)
  by_contra hn
  have hr : A.rank = Fintype.card (Fin 3) := by simp only [Fintype.card_fin]; omega
  obtain ⟨B, hB⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp
    (Matrix.mulVec_surjective_iff_rank_eq_card.mpr hr)
  have he := congrArg Matrix.det hB
  rw [Matrix.det_mul, hdet, zero_mul, Matrix.det_one] at he
  exact zero_ne_one he

/-- Nontrivial common coefficients cannot annihilate an orthonormal family. -/
theorem sharp_orthonormal_combination_ne_zero {ι n : Type*} [Fintype ι] [Fintype n]
    [DecidableEq ι] (u : ι → n → ℂ)
    (hgram : ∀ i j, braket (u i) (u j) = if i = j then 1 else 0)
    (z : ι → ℂ) (hz : z ≠ 0) : (fun r => ∑ i, z i * u i r) ≠ 0 := by
  intro hzero
  apply hz
  funext i
  have he : braket (u i) (fun r => ∑ j, z j * u j r) = z i := by
    calc
      _ = ∑ j, z j * braket (u i) (u j) := by
        simp only [braket, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro r _
        ring
      _ = z i := by simp [hgram]
  have h := congrArg (braket (u i)) hzero
  rw [he] at h
  simpa only [braket, Pi.zero_apply, mul_zero, Finset.sum_const_zero] using h

/-- The common singular-vector pencil of a two-qutrit sharp-PT extremizer
consists entirely of singular three-by-three reshapes. -/
theorem sharpPartialTrace_singular_common_reshape_det_zero
    (X : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (hsat : frobSq (ptraceL X) + frobSq (ptraceR X) =
      nuclearTrace X ^ 2 + Complex.normSq X.trace)
    (z : SingularPositiveIndex X → ℂ) :
    (sharpReshape (fun r => ∑ i, z i * singularLeft X i r)).det = 0 := by
  classical
  by_cases hz : z = 0
  · have he : sharpReshape (fun r => ∑ i, z i * singularLeft X i r) = 0 := by
      ext i j
      simp [sharpReshape, hz]
    rw [he, Matrix.det_zero]
  · have hv := sharp_orthonormal_combination_ne_zero (singularRight X)
      (singularRight_braket X) z hz
    have hB : sharpReshape (fun r => ∑ i, z i * singularRight X i r) ≠ 0 := by
      intro h
      apply hv
      funext ⟨i, j⟩
      exact congrFun (congrFun h i) j
    apply sharpPolarizedMinor_det_eq_zero _ _ hB
    exact sharpDoubleAnti_tensor_null_iff _ _ |>.mp
      (sharpPartialTrace_singular_common_combination_null X hsat z)

/-- This is pointwise Schmidt rank at most two for every common singular
combination; it does not assert a fixed thin local support. -/
theorem sharpPartialTrace_singular_common_reshape_rank_le_two
    (X : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (hsat : frobSq (ptraceL X) + frobSq (ptraceR X) =
      nuclearTrace X ^ 2 + Complex.normSq X.trace)
    (z : SingularPositiveIndex X → ℂ) :
    (sharpReshape (fun r => ∑ i, z i * singularLeft X i r)).rank ≤ 2 :=
  sharp_rank_le_two_of_det_eq_zero _
    (sharpPartialTrace_singular_common_reshape_det_zero X hsat z)

end ThreeCopyQutritWerner
