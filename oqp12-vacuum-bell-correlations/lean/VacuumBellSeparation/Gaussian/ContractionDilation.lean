module

public import VacuumBellSeparation.Gaussian.IsometricCorner
public import Mathlib.Analysis.InnerProductSpace.ProdL2

@[expose] public section


/-!
# Actual Hilbert-space dilation of a contraction

The map x ↦ (C x, sqrt(I−C†C) x) is an isometry into the genuine Hilbert
product. Its compression of the first corner of A is C†AC. Together with
the previously proved isometric compression inequality and nonunital
corner calculus, this proves operator concavity under a contraction.
-/

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def hilbertProductLeft : E →ₗᵢ[ℂ] WithLp 2 (E × E) :=
  ((WithLp.linearEquiv 2 ℂ (E × E)).symm.toLinearMap.comp (LinearMap.inl ℂ E E)).isometryOfInner
    (by intro x y; simp [WithLp.prod_inner_apply])

@[simp] theorem hilbertProductLeft_apply (x : E) :
    hilbertProductLeft x = WithLp.toLp 2 (x, (0 : E)) := rfl

@[simp] theorem hilbertProductLeft_adjoint_apply (z : WithLp 2 (E × E)) :
    (hilbertProductLeft (E := E)).toContinuousLinearMap.adjoint z = (WithLp.ofLp z).1 := by
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp only [LinearIsometry.coe_toContinuousLinearMap, hilbertProductLeft_apply,
    WithLp.prod_inner_apply, WithLp.ofLp_toLp, Prod.fst, Prod.snd, inner_zero_left, add_zero]

def contractionDilation (C : E →L[ℂ] E) (hC : star C * C ≤ 1) :
    E →ₗᵢ[ℂ] WithLp 2 (E × E) := by
  let D := CFC.sqrt (1 - star C * C)
  let f : E →ₗ[ℂ] WithLp 2 (E × E) :=
    (WithLp.linearEquiv 2 ℂ (E × E)).symm.toLinearMap.comp
      (C.toLinearMap.prod D.toLinearMap)
  apply f.isometryOfInner
  intro x y
  change inner ℂ (C x) (C y) + inner ℂ (D x) (D y) = inner ℂ x y
  have hDD : D * D = 1 - star C * C := by
    dsimp only [D]
    rw [← pow_two, CFC.sq_sqrt _ (sub_nonneg.mpr hC)]
  have hD : D.adjoint = D := (CFC.sqrt_nonneg _).isSelfAdjoint.adjoint_eq
  have hsum : star C * C + D * D = 1 := by rw [hDD]; abel
  rw [← C.adjoint_inner_right, ← D.adjoint_inner_right, hD]
  change inner ℂ x ((star C * C) y) + inner ℂ x ((D * D) y) = inner ℂ x y
  rw [← inner_add_right, ← add_apply, hsum, one_apply_eq_self]

@[simp] theorem contractionDilation_apply (C : E →L[ℂ] E)
    (hC : star C * C ≤ 1) (x : E) :
    contractionDilation C hC x =
      WithLp.toLp 2 (C x, CFC.sqrt (1 - star C * C) x) := rfl

theorem compression_contraction_corner (C : E →L[ℂ] E) (hC : star C * C ≤ 1)
    (A : E →L[ℂ] E) :
    compression (contractionDilation C hC) (isometricCorner hilbertProductLeft A) =
      star C * A * C := by
  ext y
  apply ext_inner_left ℂ
  intro x
  change inner ℂ x ((contractionDilation C hC).toContinuousLinearMap.adjoint
    (isometricCorner hilbertProductLeft A (contractionDilation C hC y))) =
      inner ℂ x ((star C * A * C) y)
  rw [ContinuousLinearMap.adjoint_inner_right, isometricCorner_apply,
    hilbertProductLeft_adjoint_apply, hilbertProductLeft_apply]
  simp only [contractionDilation_apply, WithLp.prod_inner_apply, WithLp.ofLp_toLp, Prod.fst, Prod.snd,
    inner_zero_right, add_zero, mul_apply_eq_comp]
  exact (C.adjoint_inner_right x (A (C y))).symm

/-- Hansen's power inequality on the actual infinite-dimensional Hilbert
space, derived by dilation from the proved isometric Jensen inequality. -/
theorem contraction_rpow_le (C : E →L[ℂ] E) (hC : star C * C ≤ 1)
    {A : E →L[ℂ] E} (hA : 0 ≤ A) {p : ℝ} (hp₀ : 0 < p) (hp₁ : p ≤ 1) :
    star C * A ^ p * C ≤ (star C * A * C) ^ p := by
  have h := compression_rpow_le (contractionDilation C hC)
    (isometricCorner_nonneg hilbertProductLeft hA) hp₀ hp₁
  rw [← isometricCorner_rpow hilbertProductLeft hA hp₀,
    compression_contraction_corner, compression_contraction_corner] at h
  exact h

/-- The exact contraction-concavity step used for the source effect bound. -/
theorem effect_sqrt_rpow_le {M A : E →L[ℂ] E} (hM₀ : 0 ≤ M) (hM₁ : M ≤ 1)
    (hA : 0 ≤ A) {p : ℝ} (hp₀ : 0 < p) (hp₁ : p ≤ 1) :
    CFC.sqrt M * A ^ p * CFC.sqrt M ≤ (CFC.sqrt M * A * CFC.sqrt M) ^ p := by
  have hs := (CFC.sqrt_nonneg M).isSelfAdjoint.star_eq
  have hc : star (CFC.sqrt M) * CFC.sqrt M ≤ 1 := by
    rw [hs, ← pow_two, CFC.sq_sqrt M hM₀]
    exact hM₁
  simpa only [hs] using contraction_rpow_le (CFC.sqrt M) hc hA hp₀ hp₁

end VacuumBellSeparation.Gaussian
