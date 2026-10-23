module

public import VacuumBellSeparation.Gaussian.PolydiscAngularRecursion
public import VacuumBellSeparation.Gaussian.PolydiscCoefficientConvergence

@[expose] public section


/-!
# Full reconstruction by the actual multivariable Cauchy coefficients

The conclusion is a HasSum over every natural-number coordinate tuple.
Joint integrability and geometric dominated convergence establish the
product integral series; actual Fubini identifies its coefficients with
the nested contours, and repeated Cauchy identifies its sum with F.
-/

open Complex Set

namespace VacuumBellSeparation.Gaussian

theorem continuous_boundary_of_polydisc_differentiable (n : ℕ) {R : ℝ}
    (hR : 0 ≤ R) (F : (Fin n → ℂ) → ℂ)
    (hF : ∀ z ∈ coordinateClosedPolydisc n R, DifferentiableAt ℂ F z) :
    Continuous (fun θ => F (polydiscBoundaryPoint n R θ)) := by
  have hc : ContinuousOn F (coordinateClosedPolydisc n R) :=
    fun z hz => (hF z hz).continuousAt.continuousWithinAt
  apply hc.comp_continuous (continuous_polydiscBoundaryPoint n R)
  intro θ j
  exact (norm_polydiscBoundaryPoint n hR θ j).le

theorem hasSum_polydiscCoefficient (n : ℕ) {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M) (F : (Fin n → ℂ) → ℂ)
    (hF : ∀ z ∈ coordinateClosedPolydisc n R, DifferentiableAt ℂ F z)
    (hbound : ∀ z ∈ coordinateClosedPolydisc n R, ‖F z‖ ≤ M)
    (x : Fin n → ℂ) (hx : ∀ j, ‖x j‖ < R) :
    HasSum (fun k : Fin n → ℕ => polydiscCoefficient n R F k * ∏ j, x j ^ k j) (F x) := by
  have hc := continuous_boundary_of_polydisc_differentiable n hR.le F hF
  have hb : ∀ z, (∀ j, ‖z j‖ = R) → ‖F z‖ ≤ M :=
    fun z hz => hbound z (fun j => (hz j).le)
  have hs := hasSum_angularPolydiscCoefficient n hR hM F hc hb x hx
  simp only [angularPolydiscCoefficient_eq n hR hM F hc hb,
    angularPolydiscCauchy_eq n hR hM F hc hb x hx,
    polydiscCauchyTransform_eq n hR F hF x hx] at hs
  exact hs

/-- Actual reconstruction and absolute convergence use the same coefficients. -/
theorem polydiscCoefficient_expansion (n : ℕ) {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M) (F : (Fin n → ℂ) → ℂ)
    (hF : ∀ z ∈ coordinateClosedPolydisc n R, DifferentiableAt ℂ F z)
    (hbound : ∀ z ∈ coordinateClosedPolydisc n R, ‖F z‖ ≤ M)
    (x : Fin n → ℂ) (hx : ∀ j, ‖x j‖ < R) :
    HasSum (fun k : Fin n → ℕ => polydiscCoefficient n R F k * ∏ j, x j ^ k j) (F x) ∧
      Summable (fun k : Fin n → ℕ => ‖polydiscCoefficient n R F k * ∏ j, x j ^ k j‖) :=
  ⟨hasSum_polydiscCoefficient n hR hM F hF hbound x hx,
    summable_norm_polydiscCoefficient_monomial n hR hM F hbound x hx⟩

end VacuumBellSeparation.Gaussian
