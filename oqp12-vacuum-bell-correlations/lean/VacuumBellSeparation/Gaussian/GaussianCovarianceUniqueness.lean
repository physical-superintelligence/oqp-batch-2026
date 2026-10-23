module

public import VacuumBellSeparation.Gaussian.GaussianUncertaintyNecessity

@[expose] public section


/-!
# Intrinsic covariance from the actual Gaussian characteristic

The symmetric real covariance in the genuine Weyl expectation is unique.
The physical covariance below chooses that unique matrix when it exists;
its zero fallback is never used in Gaussian evaluation theorems. Symmetry
is essential because a quadratic characteristic cannot detect an
antisymmetric addition. Normalized power covariance uses the actual CFC
power and actual positive-trace normalization of the density.
-/

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix

variable {m : ℕ}

theorem real_symmetric_matrix_eq_of_quadratic_eq
    {V W : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hV : V.IsHermitian) (hW : W.IsHermitian)
    (h : ∀ x : Fin m × Fin 2 → ℝ, x ⬝ᵥ (V *ᵥ x) = x ⬝ᵥ (W *ᵥ x)) : V = W := by
  ext i j
  have hi := h (Pi.single i 1)
  have hj := h (Pi.single j 1)
  have hij := h (Pi.single i 1 + Pi.single j 1)
  have hv : V j i = V i j := by simpa only [star_trivial] using hV.apply i j
  have hw : W j i = W i j := by simpa only [star_trivial] using hW.apply i j
  simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add,
    real_coordinate_basis_bilinear, hv, hw] at hi hj hij
  linarith

theorem gaussianDisplacement_covariance_unique
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    {V W : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hV : V.IsHermitian) (hW : W.IsHermitian)
    (hGV : HasGaussianDisplacementCharacteristic A V)
    (hGW : HasGaussianDisplacementCharacteristic A W) : V = W := by
  apply real_symmetric_matrix_eq_of_quadratic_eq hV hW
  intro x
  have he := (gaussianDisplacement_realCoordinateWeyl hGV x).symm.trans
    (gaussianDisplacement_realCoordinateWeyl hGW x)
  have hre := congrArg Complex.re he
  simp only [Complex.exp_ofReal_re] at hre
  exact neg_injective (Real.exp_injective hre)

theorem physicalDisplacementCovariance_isHermitian
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ} (hV : V.IsHermitian) :
    (physicalDisplacementCovariance V).IsHermitian := by
  simpa only [physicalDisplacementCovariance, Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.isHermitian_conjTranspose_mul_mul modeSymplecticForm hV

theorem gaussianPhysical_covariance_unique
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    {V W : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hV : V.IsHermitian) (hW : W.IsHermitian)
    (hGV : HasGaussianPhysicalCharacteristic A V)
    (hGW : HasGaussianPhysicalCharacteristic A W) : V = W := by
  have he := gaussianDisplacement_covariance_unique
    (physicalDisplacementCovariance_isHermitian hV)
    (physicalDisplacementCovariance_isHermitian hW) hGV hGW
  have hh := congrArg (fun B => modeSymplecticForm * B * modeSymplecticFormᵀ) he
  have hc (B : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) :
      modeSymplecticForm * physicalDisplacementCovariance B * modeSymplecticFormᵀ = B := by
    unfold physicalDisplacementCovariance
    calc
      _ = (modeSymplecticForm * modeSymplecticFormᵀ) * B *
          (modeSymplecticForm * modeSymplecticFormᵀ) := by noncomm_ring
      _ = B := by rw [modeSymplecticForm_mul_transpose, Matrix.one_mul, Matrix.mul_one]
  simpa only [hc] using hh

open scoped Classical in
def gaussianPhysicalCovariance
    (A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m) :
    Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ :=
  if h : ∃ V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ,
      V.IsHermitian ∧ HasGaussianPhysicalCharacteristic A V then h.choose else 0

theorem gaussianPhysicalCovariance_eq
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hV : V.IsHermitian) (hG : HasGaussianPhysicalCharacteristic A V) :
    gaussianPhysicalCovariance A = V := by
  let h : ∃ W : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ,
      W.IsHermitian ∧ HasGaussianPhysicalCharacteristic A W := ⟨V, hV, hG⟩
  rw [gaussianPhysicalCovariance, dif_pos h]
  exact gaussianPhysical_covariance_unique h.choose_spec.1 hV h.choose_spec.2 hG

def normalizedGaussianPowerCovariance
    (A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m) (a : ℝ) :
    Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ :=
  gaussianPhysicalCovariance (normalizedPositiveDensity (A ^ a))

end VacuumBellSeparation.Gaussian
