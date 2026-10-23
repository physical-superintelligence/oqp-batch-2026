module

public import VacuumBellSeparation.Gaussian.PolydiscAngularIntegral
public import VacuumBellSeparation.Gaussian.FiniteComplexProductSeries

@[expose] public section


/-!
# Actual geometric expansion inside the product-angle integral

These coefficients are one product-angle integral. The resulting series
converges to the actual product Cauchy integral. Identification with the
iterated coefficients and the original holomorphic function is supplied
by the separate Fubini and repeated-Cauchy steps.
-/

open Complex MeasureTheory Set
open scoped BigOperators

namespace VacuumBellSeparation.Gaussian

noncomputable def angularPolydiscCoefficient (n : ℕ) (R : ℝ)
    (F : (Fin n → ℂ) → ℂ) (k : Fin n → ℕ) : ℂ :=
  polydiscAngularIntegral n R (fun z => F z * ∏ j, (z j)⁻¹ ^ k j)

noncomputable def angularPolydiscCauchy (n : ℕ) (R : ℝ)
    (F : (Fin n → ℂ) → ℂ) (x : Fin n → ℂ) : ℂ :=
  polydiscAngularIntegral n R (fun z => F z * ∏ j, (1 - x j / z j)⁻¹)

theorem angularPolydiscCoefficient_norm_le (n : ℕ) {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M) (F : (Fin n → ℂ) → ℂ)
    (hF : ∀ z, (∀ j, ‖z j‖ = R) → ‖F z‖ ≤ M) (k : Fin n → ℕ) :
    ‖angularPolydiscCoefficient n R F k‖ ≤ M * ∏ j, R⁻¹ ^ k j := by
  apply polydiscAngularIntegral_norm_le n hR.le
  intro z hz
  simp only [norm_mul, norm_prod, norm_pow, norm_inv, hz]
  exact mul_le_mul_of_nonneg_right (hF z hz) (by positivity)

theorem angularPolydiscCoefficient_monomial (n : ℕ) (R : ℝ)
    (F : (Fin n → ℂ) → ℂ) (x : Fin n → ℂ) (k : Fin n → ℕ) :
    polydiscAngularIntegral n R (fun z => F z * ∏ j, (x j / z j) ^ k j) =
      angularPolydiscCoefficient n R F k * ∏ j, x j ^ k j := by
  have hp (z : Fin n → ℂ) :
      F z * ∏ j, (x j / z j) ^ k j =
        (F z * ∏ j, (z j)⁻¹ ^ k j) * ∏ j, x j ^ k j := by
    simp only [div_eq_mul_inv, mul_pow, Finset.prod_mul_distrib]
    ring
  simp only [polydiscAngularIntegral, angularPolydiscCoefficient, hp,
    integral_mul_const]
  ring

theorem hasSum_angularPolydiscCoefficient (n : ℕ) {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M) (F : (Fin n → ℂ) → ℂ)
    (hcont : Continuous (fun θ => F (polydiscBoundaryPoint n R θ)))
    (hF : ∀ z, (∀ j, ‖z j‖ = R) → ‖F z‖ ≤ M)
    (x : Fin n → ℂ) (hx : ∀ j, ‖x j‖ < R) :
    HasSum (fun k : Fin n → ℕ => angularPolydiscCoefficient n R F k * ∏ j, x j ^ k j)
      (angularPolydiscCauchy n R F x) := by
  let b : (Fin n → ℕ) → ℝ := fun k => M * ∏ j, (‖x j‖ / R) ^ k j
  have hq (j : Fin n) : 0 ≤ ‖x j‖ / R ∧ ‖x j‖ / R < 1 :=
    ⟨by positivity, (div_lt_one hR).mpr (hx j)⟩
  have hb : Summable b :=
    (hasSum_fin_product_nonneg n (fun j k => (‖x j‖ / R) ^ k)
      (fun j => (1 - ‖x j‖ / R)⁻¹) (fun _ _ => by positivity)
      (fun j => hasSum_geometric_of_lt_one (hq j).1 (hq j).2)).summable.mul_left M
  have hseries := hasSum_polydiscAngularIntegral n hR.le
    (fun k z => F z * ∏ j, (x j / z j) ^ k j)
    (fun z => F z * ∏ j, (1 - x j / z j)⁻¹) b
    (fun k => ?_) (fun k z hz => ?_) hb (fun z hz => ?_)
  · simpa only [angularPolydiscCoefficient_monomial, angularPolydiscCauchy] using hseries
  · apply hcont.mul
    apply continuous_finset_prod
    intro j _
    apply Continuous.pow
    apply continuous_const.div
    · exact (continuous_apply j).comp (continuous_polydiscBoundaryPoint n R)
    · intro θ
      exact norm_ne_zero_iff.mp (by rw [norm_polydiscBoundaryPoint n hR.le]; exact hR.ne')
  · dsimp only [b]
    simp only [norm_mul, norm_prod, norm_pow, norm_div, hz]
    exact mul_le_mul_of_nonneg_right (hF z hz) (by positivity)
  · have hgeom (j : Fin n) : ‖x j / z j‖ < 1 := by
      rw [norm_div, hz j]
      exact (hq j).2
    have hs := hasSum_fin_complex_product n (fun j k => (x j / z j) ^ k)
      (fun j => (1 - x j / z j)⁻¹)
      (fun j => by simpa only [norm_pow] using
        summable_geometric_of_lt_one (norm_nonneg (x j / z j)) (hgeom j))
      (fun j => hasSum_geometric_of_norm_lt_one (hgeom j))
    exact hs.mul_left (F z)

end VacuumBellSeparation.Gaussian
