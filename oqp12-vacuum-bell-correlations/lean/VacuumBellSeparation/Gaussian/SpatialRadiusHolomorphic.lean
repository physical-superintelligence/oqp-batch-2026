module

public import VacuumBellSeparation.Gaussian.SpatialComplexRadius
public import VacuumBellSeparation.Gaussian.SpatialBesselHolomorphic

@[expose] public section


/-!
# Holomorphic separated radius and its Euclidean upper bound
-/

namespace VacuumBellSeparation.Gaussian

theorem norm_spatialSquaredRadius_le {s d : ℝ} (hs : 0 ≤ s) (hd : 0 ≤ d)
    (δ : EuclideanSpace ℂ (Fin 3)) (hδ : ‖δ‖ ≤ d) :
    ‖spatialSquaredRadius s δ‖ ≤ (s + d) ^ 2 := by
  calc
    _ = ‖(spatialSquaredRadius s δ - (s : ℂ) ^ 2) + (s : ℂ) ^ 2‖ := by
      rw [sub_add_cancel]
    _ ≤ ‖spatialSquaredRadius s δ - (s : ℂ) ^ 2‖ + ‖(s : ℂ) ^ 2‖ := norm_add_le _ _
    _ ≤ (2 * s * d + d ^ 2) + s ^ 2 := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
      exact _root_.add_le_add_left (spatialSquaredRadius_error_le hs hd δ hδ) _
    _ = _ := by ring

theorem norm_spatialComplexRadius_le {s d : ℝ} (hs : 0 ≤ s) (hd : 0 ≤ d)
    (δ : EuclideanSpace ℂ (Fin 3)) (hδ : ‖δ‖ ≤ d) :
    ‖spatialComplexRadius s δ‖ ≤ s + d := by
  have h := Real.sqrt_le_sqrt (norm_spatialSquaredRadius_le hs hd δ hδ)
  rw [Real.sqrt_sq (add_nonneg hs hd)] at h
  change ‖spatialSquaredRadius s δ ^ (2⁻¹ : ℂ)‖ ≤ s + d
  have hnorm : ‖spatialSquaredRadius s δ ^ (2⁻¹ : ℂ)‖ =
      ‖spatialSquaredRadius s δ‖ ^ (2⁻¹ : ℝ) := by
    simpa only [Nat.cast_ofNat] using
      Complex.norm_cpow_inv_nat (spatialSquaredRadius s δ) 2
  rw [hnorm]
  simpa only [← one_div, ← Real.sqrt_eq_rpow] using h

theorem spatialComplexRadius_re_upper {s d : ℝ} (hs : 0 ≤ s) (hd : 0 ≤ d)
    (δ : EuclideanSpace ℂ (Fin 3)) (hδ : ‖δ‖ ≤ d) :
    (spatialComplexRadius s δ).re ≤ s + d :=
  (Complex.re_le_norm _).trans (norm_spatialComplexRadius_le hs hd δ hδ)

theorem differentiable_spatialSquaredRadius (s : ℝ) :
    Differentiable ℂ (spatialSquaredRadius s) := by
  unfold spatialSquaredRadius
  fun_prop

theorem differentiableAt_spatialComplexRadius (s : ℝ)
    (δ : EuclideanSpace ℂ (Fin 3)) (hδ : 0 < (spatialSquaredRadius s δ).re) :
    DifferentiableAt ℂ (spatialComplexRadius s) δ :=
  (Complex.differentiableAt_sqrt (Or.inl hδ)).comp δ
    ((differentiable_spatialSquaredRadius s) δ)

theorem spatialComplexRadius_re_pos_of_squared (s : ℝ)
    (δ : EuclideanSpace ℂ (Fin 3)) (hδ : 0 < (spatialSquaredRadius s δ).re) :
    0 < (spatialComplexRadius s δ).re := by
  change 0 < ((spatialSquaredRadius s δ) ^ (2⁻¹ : ℂ)).re
  rw [Complex.cpow_inv_two_re]
  apply Real.sqrt_pos.mpr
  have hn := norm_nonneg (spatialSquaredRadius s δ)
  linarith

theorem differentiableAt_spatialComplexRadius_of_separated {s d : ℝ}
    (hs : 0 < s) (hd : 0 ≤ d) (hsep : 4 * d ≤ s)
    (δ : EuclideanSpace ℂ (Fin 3)) (hδ : ‖δ‖ ≤ d) :
    DifferentiableAt ℂ (spatialComplexRadius s) δ :=
  differentiableAt_spatialComplexRadius s δ (spatialSquaredRadius_re_pos hs hd hsep δ hδ)

end VacuumBellSeparation.Gaussian
