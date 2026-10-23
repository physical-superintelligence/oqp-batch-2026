module

public import ThreeCopyQutritWerner.JointShadowAlgebra
public import ThreeCopyQutritWerner.JointShadowMarginals

@[expose] public section


/-!
# The actual common-four-register shadow bound

The manuscript's shadow lower bound is derived from a squared projector norm.
Every quantity uses the same X,Y and their original logical columns. The exact
balanced-Gram hypothesis is retained; no normality or rank premise is added.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

variable {l a b c : Type*} [Fintype l] [Fintype a] [Fintype b] [Fintype c]

/-- The shadow lower bound B_J using the actual common marginal defect b. -/
def jointShadowLowerBound (X Y : Matrix (a × b × c) l ℂ) : ℝ :=
  (endpointEnergy (X * Xᴴ) + endpointEnergy (Y * Yᴴ)) / 2 -
    (frobSq X ^ 2 - invT (X * Yᴴ)) / 8 +
    jointShadowMarginalDefect X Y / 8 - jointShadowS3 (X * Xᴴ - Y * Yᴴ) / 8

/-- JS2: the exact shadow remainder is four times the literal projector norm.
The balance hypothesis identifies the two logical Grams and is mathematically essential. -/
theorem jointShadow_identity (X Y : Matrix (a × b × c) l ℂ)
    (hG : Xᴴ * X = Yᴴ * Y) :
    endpointEnergy (X * Yᴴ) - jointShadowLowerBound X Y =
      4 * vecNormSq (jointShadowProjection (jointShadowSourceTensor X Y)) := by
  have h := jointShadowProjection_physical_identity X Y
  obtain ⟨hX, hY, hw⟩ := jointShadow_balanced_norms X Y hG
  have hNX : invN (X * Xᴴ) = invN (X * Yᴴ) := hX
  have hNY : invN (Y * Yᴴ) = invN (X * Yᴴ) := hY
  have hTX : invT (X * Xᴴ) = frobSq X ^ 2 := by
    rw [invT, jointShadow_trace_source, Complex.normSq_ofReal, pow_two]
  have hTY : invT (Y * Yᴴ) = frobSq Y ^ 2 := by
    rw [invT, jointShadow_trace_source, Complex.normSq_ofReal, pow_two]
  unfold jointShadowLowerBound
  rw [jointShadowMarginalDefect_eq_invA, jointShadowS3_sub]
  simp only [endpointEnergy, energy]
  rw [hTX, hTY, hNX, hNY, hw]
  rw [hw] at h
  linear_combination -h / 4

/-- The manuscript's B_J inequality follows from actual projector positivity. -/
theorem jointShadow_lower_bound (X Y : Matrix (a × b × c) l ℂ)
    (hG : Xᴴ * X = Yᴴ * Y) :
    jointShadowLowerBound X Y ≤ endpointEnergy (X * Yᴴ) := by
  have h := jointShadow_identity X Y hG
  have hn := vecNormSq_nonneg (jointShadowProjection (jointShadowSourceTensor X Y))
  linarith

/-- The additional common logical partial-trace slack is genuinely nonnegative
for the same two-column factors entering the shadow identity. -/
theorem jointShadow_logical_slack_nonneg (X Y : Matrix (a × b × c) (Fin 2) ℂ) :
    0 ≤ 2 * jointShadowMarginalDefect X Y - invB (X * Xᴴ - Y * Yᴴ) :=
  sub_nonneg.mpr (jointShadow_invB_sub_le_two_mul_defect X Y)

end ThreeCopyQutritWerner
