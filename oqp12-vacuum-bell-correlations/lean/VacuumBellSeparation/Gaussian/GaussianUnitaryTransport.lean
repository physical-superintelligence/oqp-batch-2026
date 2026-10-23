module

public import VacuumBellSeparation.Gaussian.MatrixWeylLabels
public import VacuumBellSeparation.Gaussian.UnitaryDensityExpectation
public import VacuumBellSeparation.Gaussian.ThermalDensityCharacteristic
public import VacuumBellSeparation.Gaussian.ThermalCovarianceParameters

@[expose] public section


/-!
# Actual Gaussian densities transported in the fixed oscillator representation

Pulling an actual density back by the constructed symplectic unitary
pulls its displacement covariance back by the literal real label matrix.
The direction is explicit: label S gives covariance Sᵀ V S for U_S† A U_S.
Thermal product densities then realize every Williamson congruence on
the original canonical Weyl family, not a separately relabeled family.
-/

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix

variable {m : ℕ}

def matrixDensityPullback
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : Sᵀ * modeSymplecticForm * S = modeSymplecticForm)
    (A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m) :
    MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m :=
  (symplecticWeylImplementer (matrixWeylLabelMap_preservesWeylForm S hS)).symm.conjStarAlgEquiv A

theorem matrixDensityPullback_isPositiveTraceClass
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : Sᵀ * modeSymplecticForm * S = modeSymplecticForm)
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A) : IsPositiveTraceClass (matrixDensityPullback S hS A) :=
  IsPositiveTraceClass.conjStarAlgEquiv _ hA

theorem matrixDensityPullback_isFaithfulDensity
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : Sᵀ * modeSymplecticForm * S = modeSymplecticForm)
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsFaithfulDensity A) : IsFaithfulDensity (matrixDensityPullback S hS A) :=
  IsFaithfulDensity.conjStarAlgEquiv _ hA

theorem densityExpectation_matrixDensityPullback_weyl
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : Sᵀ * modeSymplecticForm * S = modeSymplecticForm)
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A) (z : MultiModePhaseSpace m) :
    densityExpectation (multiModeNumberBasis m) (matrixDensityPullback S hS A) (multiOscillatorWeyl z) =
      densityExpectation (multiModeNumberBasis m) A (multiOscillatorWeyl (matrixWeylLabelMap S z)) := by
  rw [matrixDensityPullback, densityExpectation_symm_conjStarAlgEquiv_left _
    (multiModeNumberBasis m) (multiModeNumberBasis m) hA,
    symplecticWeylImplementer_conj_weyl]

theorem matrixDensityPullback_hasGaussianDisplacementCharacteristic
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : Sᵀ * modeSymplecticForm * S = modeSymplecticForm)
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A)
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hG : HasGaussianDisplacementCharacteristic A V) :
    HasGaussianDisplacementCharacteristic (matrixDensityPullback S hS A) (Sᵀ * V * S) := by
  intro z
  rw [densityExpectation_matrixDensityPullback_weyl S hS hA]
  have hg := hG (fun j => matrixWeylLabelMap S (WithLp.toLp 2 z) j)
  change densityExpectation (multiModeNumberBasis m) A
    (multiOscillatorWeyl (matrixWeylLabelMap S (WithLp.toLp 2 z))) =
      Complex.exp ((-(complexRealLinearEquiv m (matrixWeylLabelMap S (WithLp.toLp 2 z)) ⬝ᵥ
        (V *ᵥ complexRealLinearEquiv m (matrixWeylLabelMap S (WithLp.toLp 2 z)))) : ℝ) : ℂ) at hg
  rw [hg]
  simp only [complexRealLinearEquiv_matrixWeylLabelMap]
  have hquad := dotProduct_congruence Sᵀ V
    (complexRealLinearEquiv m (WithLp.toLp 2 z)) (complexRealLinearEquiv m (WithLp.toLp 2 z))
  rw [Matrix.transpose_transpose] at hquad
  rw [hquad]
  rfl

theorem covarianceProductDensity_isPositiveTraceClass {ν : Fin m → ℝ}
    (hν : ∀ j, 1 / 2 ≤ ν j) : IsPositiveTraceClass (covarianceProductDensity ν) := by
  refine ⟨covarianceProductDensity_nonneg hν, ?_⟩
  rw [positiveTrace_covarianceProductDensity hν]
  exact ENNReal.one_lt_top

theorem covarianceProductDensity_hasGaussianDisplacementCharacteristic {ν : Fin m → ℝ}
    (hν : ∀ j, 1 / 2 ≤ ν j) :
    HasGaussianDisplacementCharacteristic (covarianceProductDensity ν) (modeDiagonal ν) := by
  have h := multiModeThermalDensity_hasGaussianPhysicalCharacteristic
    (fun j => covarianceThermalParameter_nonneg (hν j))
    (fun j => covarianceThermalParameter_lt_one (hν j))
  change HasGaussianDisplacementCharacteristic (covarianceProductDensity ν)
    (physicalDisplacementCovariance
      (modeDiagonal (fun j => thermalQuadratureVariance (covarianceThermalParameter (ν j))))) at h
  simpa only [physicalDisplacementCovariance_modeDiagonal,
    thermalQuadratureVariance_covarianceParameter (hν _)] using h

/-- Genuine fixed-representation realization of a Williamson congruence,
by the constructed unitary acting on the actual full oscillator density. -/
theorem williamsonDensity_hasGaussianDisplacementCharacteristic
    {ν : Fin m → ℝ} (hν : ∀ j, 1 / 2 ≤ ν j)
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm) :
    HasGaussianDisplacementCharacteristic
      (matrixDensityPullback Sᵀ (by simpa only [Matrix.transpose_transpose] using hS)
        (covarianceProductDensity ν)) (S * modeDiagonal ν * Sᵀ) := by
  simpa only [Matrix.transpose_transpose] using
    matrixDensityPullback_hasGaussianDisplacementCharacteristic Sᵀ
      (by simpa only [Matrix.transpose_transpose] using hS)
      (covarianceProductDensity_isPositiveTraceClass hν)
      (covarianceProductDensity_hasGaussianDisplacementCharacteristic hν)

end VacuumBellSeparation.Gaussian
