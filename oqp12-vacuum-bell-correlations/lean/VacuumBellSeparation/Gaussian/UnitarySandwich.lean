module

public import VacuumBellSeparation.Gaussian.GaussianNormalizedPowers

@[expose] public section


/-!
# Unitary transport of actual positive trace-class sandwich factorizations

The factorization R Θ R = A uses actual bounded CFC powers of the
reference. Its existence, extended positive trace and normalization
are preserved by an actual Hilbert-space unitary. No inverse of a
faithful trace-class density is treated as a bounded operator.
-/

namespace VacuumBellSeparation.Gaussian

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def HasPositiveTraceClassSandwich (σ A : E →L[ℂ] E) (τ : ℝ) : Prop :=
  ∃ Θ : E →L[ℂ] E, IsPositiveTraceClass Θ ∧ σ ^ (τ / 2) * Θ * σ ^ (τ / 2) = A

theorem conjStarAlgEquiv_sandwich (e : E ≃ₗᵢ[ℂ] F)
    {σ : E →L[ℂ] E} (hσ : 0 ≤ σ) {τ : ℝ} (hτ : 0 ≤ τ) (Θ : E →L[ℂ] E) :
    e.conjStarAlgEquiv (σ ^ (τ / 2) * Θ * σ ^ (τ / 2)) =
      (e.conjStarAlgEquiv σ) ^ (τ / 2) * e.conjStarAlgEquiv Θ *
        (e.conjStarAlgEquiv σ) ^ (τ / 2) := by
  rw [map_mul, map_mul, conjStarAlgEquiv_rpow e hσ (div_nonneg hτ (by norm_num))]

theorem hasPositiveTraceClassSandwich_conjStarAlgEquiv_iff
    (e : E ≃ₗᵢ[ℂ] F) {σ A : E →L[ℂ] E} (hσ : 0 ≤ σ) {τ : ℝ} (hτ : 0 ≤ τ) :
    HasPositiveTraceClassSandwich (e.conjStarAlgEquiv σ) (e.conjStarAlgEquiv A) τ ↔
      HasPositiveTraceClassSandwich σ A τ := by
  constructor
  · rintro ⟨Θ, hΘ, hf⟩
    refine ⟨e.symm.conjStarAlgEquiv Θ, IsPositiveTraceClass.conjStarAlgEquiv _ hΘ, ?_⟩
    apply e.conjStarAlgEquiv.injective
    change e.conjStarAlgEquiv (σ ^ (τ / 2) * e.symm.conjStarAlgEquiv Θ * σ ^ (τ / 2)) =
      e.conjStarAlgEquiv A
    rw [conjStarAlgEquiv_sandwich e hσ hτ,
      ← LinearIsometryEquiv.symm_conjStarAlgEquiv, StarAlgEquiv.apply_symm_apply]
    exact hf
  · rintro ⟨Θ, hΘ, hf⟩
    refine ⟨e.conjStarAlgEquiv Θ, IsPositiveTraceClass.conjStarAlgEquiv _ hΘ, ?_⟩
    rw [← conjStarAlgEquiv_sandwich e hσ hτ, hf]

theorem normalizedPositiveDensity_unitary_sandwich
    (e : E ≃ₗᵢ[ℂ] F) {Θ : E →L[ℂ] E} (hΘ : IsPositiveTraceClass Θ) :
    IsPositiveTraceClass (e.conjStarAlgEquiv Θ) ∧
      positiveTrace (e.conjStarAlgEquiv Θ) = positiveTrace Θ ∧
      normalizedPositiveDensity (e.conjStarAlgEquiv Θ) =
        e.conjStarAlgEquiv (normalizedPositiveDensity Θ) :=
  ⟨IsPositiveTraceClass.conjStarAlgEquiv e hΘ,
    positiveTrace_conjStarAlgEquiv e hΘ.1,
    normalizedPositiveDensity_conjStarAlgEquiv e hΘ.1⟩

end VacuumBellSeparation.Gaussian
