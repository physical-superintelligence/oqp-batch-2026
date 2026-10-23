module

public import Mathlib

@[expose] public section


/-!
# Literal scalar spatial Fourier integrals and absolutely convergent pairing

The measure may be infinite. Every use of Fubini is backed by the product
majorant |g(x)| |A(p)| with both factors genuinely integrable.
-/

namespace VacuumBellSeparation

open MeasureTheory Filter
open scoped InnerProductSpace

noncomputable def scalarSpatialFourier
    (μ : Measure (EuclideanSpace ℝ (Fin 3)))
    (A : EuclideanSpace ℝ (Fin 3) → ℂ) (x : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  ∫ p, Complex.exp (-(Complex.I * (⟪p, x⟫_ℝ : ℂ))) * A p ∂μ

theorem norm_scalarSpatialFourierCharacter (p x : EuclideanSpace ℝ (Fin 3)) :
    ‖Complex.exp (-(Complex.I * (⟪p, x⟫_ℝ : ℂ)))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem continuous_scalarSpatialFourier
    {μ : Measure (EuclideanSpace ℝ (Fin 3))}
    {A : EuclideanSpace ℝ (Fin 3) → ℂ} (hA : Integrable A μ) :
    Continuous (scalarSpatialFourier μ A) := by
  apply continuous_of_dominated (bound := fun p => ‖A p‖)
  · intro x
    exact (show Continuous (fun p : EuclideanSpace ℝ (Fin 3) =>
      Complex.exp (-(Complex.I * (⟪p, x⟫_ℝ : ℂ)))) by fun_prop).aestronglyMeasurable.mul
        hA.aestronglyMeasurable
  · intro x
    exact Eventually.of_forall fun p => by rw [norm_mul, norm_scalarSpatialFourierCharacter, one_mul]
  · exact hA.norm
  · exact Eventually.of_forall fun p => by fun_prop

theorem integrable_scalarSpatialFourier_pairing
    {μ : Measure (EuclideanSpace ℝ (Fin 3))} [SFinite μ]
    {A g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hA : Integrable A μ) (hg : Integrable g) (c : ℝ) :
    Integrable (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      g q.1 * (Complex.exp (-(Complex.I * ((c * ⟪q.2, q.1⟫_ℝ : ℝ) : ℂ))) * A q.2))
      (volume.prod μ) := by
  apply (hg.norm.mul_prod hA.norm).mono'
  · exact hg.aestronglyMeasurable.comp_fst.mul
      ((show Continuous (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Complex.exp (-(Complex.I * ((c * ⟪q.2, q.1⟫_ℝ : ℝ) : ℂ)))) by
        fun_prop).aestronglyMeasurable.mul hA.aestronglyMeasurable.comp_snd)
  · exact Eventually.of_forall fun q => by
      rw [norm_mul, norm_mul, Complex.norm_exp]
      simp

theorem integral_scalarSpatialFourier_pairing
    {μ : Measure (EuclideanSpace ℝ (Fin 3))} [SFinite μ]
    {A g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hA : Integrable A μ) (hg : Integrable g) (c : ℝ) :
    (∫ x, g x * scalarSpatialFourier μ A (c • x)) =
      ∫ p, (∫ x, Complex.exp (-(Complex.I * ((c * ⟪p, x⟫_ℝ : ℝ) : ℂ))) * g x) * A p ∂μ := by
  have h := integral_integral_swap
    (f := fun (x p : EuclideanSpace ℝ (Fin 3)) =>
      g x * (Complex.exp (-(Complex.I * ((c * ⟪p, x⟫_ℝ : ℝ) : ℂ))) * A p))
    (integrable_scalarSpatialFourier_pairing hA hg c)
  calc
    _ = ∫ x, ∫ p, g x *
        (Complex.exp (-(Complex.I * ((c * ⟪p, x⟫_ℝ : ℝ) : ℂ))) * A p) ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only
        unfold scalarSpatialFourier
        rw [← integral_const_mul]
        simp only [inner_smul_right, smul_eq_mul, Complex.ofReal_mul]
    _ = ∫ p, (∫ x, g x *
        (Complex.exp (-(Complex.I * ((c * ⟪p, x⟫_ℝ : ℝ) : ℂ))) * A p)) ∂μ := h
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun p => by
        dsimp only
        rw [← integral_mul_const]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by ring

end VacuumBellSeparation
