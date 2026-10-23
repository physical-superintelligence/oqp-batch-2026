module

public import VacuumBellSeparation.Gaussian.GaussianRenyiComparison
public import VacuumBellSeparation.Gaussian.FaithfulGaussianUncertainty
public import VacuumBellSeparation.Gaussian.GaussianUncertaintyNecessity
public import VacuumBellSeparation.Gaussian.SandwichedRenyiQuantity

@[expose] public section


/-!
# Rényi comparison for actual faithful Gaussian densities

Symmetric physical covariance and the actual Gaussian characteristic
imply the genuine quantum uncertainty inequality. Actual injectivity then
excludes every pure mode. Consequently the source comparison applies
without a separate quantum-positivity premise. The conclusion is about
the uniquely determined inverse-domain sandwiched Rényi quantity.
-/

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {m : ℕ}
variable {ρ σ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
variable {Vρ Vσ : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}

theorem actual_faithful_gaussian_quantum_posDef
    (hρ : IsFaithfulDensity ρ) (hVρ : Vρ.IsHermitian)
    (hGρ : HasGaussianPhysicalCharacteristic ρ Vρ) :
    (quantumCovariance Vρ modeSymplecticForm).PosDef :=
  faithful_gaussian_quantum_posDef hρ hGρ
    (gaussianPhysical_quantum_posSemidef hρ.isPositiveTraceClass hVρ hGρ)

theorem exists_faithful_gaussian_renyi_comparison
    (hρ : IsFaithfulDensity ρ) (hσ : IsFaithfulDensity σ)
    (hVρ : Vρ.IsHermitian) (hVσ : Vσ.IsHermitian)
    (hGρ : HasGaussianPhysicalCharacteristic ρ Vρ)
    (hGσ : HasGaussianPhysicalCharacteristic σ Vσ) :
    ∃ (q : Fin m → ℝ) (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
      (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm),
      (∀ j, 0 < q j) ∧ (∀ j, q j < 1) ∧
      S * thermalReferenceCovariance q * Sᵀ = Vσ ∧
      (∀ a : ℝ, 0 < a → HasGaussianPhysicalCharacteristic (normalizedPositiveDensity (σ ^ a))
        (S * thermalPowerCovariance q a * Sᵀ)) ∧
      ∀ r : ℝ, 1 < r →
        ‖transportedGaussianRelativePerturbation S q (gaussianRenyiTau r) Vρ‖ ≤
          (4 * max 2 (gaussianRenyiTau r)⁻¹)⁻¹ →
        0 < sandwichedRenyiQuantity ρ σ r ∧ sandwichedRenyiQuantity ρ σ r < ⊤ ∧
        Real.log (sandwichedRenyiQuantity ρ σ r).toReal ≤
          2 * r * max 2 (gaussianRenyiTau r)⁻¹ *
            matrixTraceNorm (transportedGaussianRelativePerturbation S q (gaussianRenyiTau r) Vρ) := by
  obtain ⟨q, S, hS, hq₀, hq₁, hcov, hpower, hcomp⟩ :=
    exists_gaussian_renyi_comparison hρ.isPositiveTraceClass hσ.isPositiveTraceClass hGρ hGσ
      (actual_faithful_gaussian_quantum_posDef hρ hVρ hGρ)
      (actual_faithful_gaussian_quantum_posDef hσ hVσ hGσ)
  refine ⟨q, S, hS, hq₀, hq₁, hcov, hpower, ?_⟩
  intro r hr hsmall
  obtain ⟨Θ, hΘ, hf, hp, hfin, hb⟩ := hcomp r hr hsmall
  rw [sandwichedRenyiQuantity_eq_power_trace hσ hr hΘ.1 hf]
  exact ⟨hp, hfin, hb⟩

end VacuumBellSeparation.Gaussian
