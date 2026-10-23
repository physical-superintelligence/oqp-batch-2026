module

public import ThreeCopyQutritWerner.CertificateReduction
public import ThreeCopyQutritWerner.AppendixCInputs
public import ThreeCopyQutritWerner.BinaryZeros

@[expose] public section


/-!
# Actual endpoint stationarity on every rank-two source

This is an implication from the qutrit endpoint inequality. Its
compression is the original endpoint operator on all coefficient matrices
of a fixed two-column physical source. A zero annihilates the full complex
source gradient, not merely its real part or a chosen finite set of tests.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker ComplexOrder

namespace ThreeCopyQutritWerner

/-- The original physical endpoint operator is Hermitian independently of
the open rank-two nonnegativity theorem. -/
theorem endpointOperator_isHermitian : endpointOperator.IsHermitian := by
  unfold endpointOperator
  apply (partialTranspose_isHermitian _
    (tripleCopy_isHermitian _ (werner_isHermitian 3 (1 / 2)))).smul
  change star ((15 / 2 : ℂ) ^ 3) = (15 / 2 : ℂ) ^ 3
  norm_num

/-- The actual coefficient-to-physical-vector map for C=X*B. -/
def endpointSourceLift (X : Matrix QutritSites (Fin 2) ℂ) :
    Matrix (QutritSites × QutritSites) (Fin 2 × QutritSites) ℂ :=
  X ⊗ₖ (1 : Matrix QutritSites QutritSites ℂ)

theorem endpointSourceLift_mulVec (X : Matrix QutritSites (Fin 2) ℂ)
    (B : Matrix (Fin 2) QutritSites ℂ) :
    endpointSourceLift X *ᵥ vec B = vec (X * B) := by
  funext p
  simp [endpointSourceLift, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.one_apply, vec, Matrix.mul_apply]

/-- The literal Hermitian restriction to all source coefficients. -/
def endpointSourceCompression (X : Matrix QutritSites (Fin 2) ℂ) :
    Matrix (Fin 2 × QutritSites) (Fin 2 × QutritSites) ℂ :=
  (endpointSourceLift X)ᴴ * endpointOperator * endpointSourceLift X

theorem endpointSourceCompression_expectation (X : Matrix QutritSites (Fin 2) ℂ)
    (B : Matrix (Fin 2) QutritSites ℂ) :
    expectation (endpointSourceCompression X) (vec B) = (endpointEnergy (X * B) : ℂ) := by
  rw [endpointSourceCompression, ← expectation_mulVec, endpointSourceLift_mulVec,
    expectation_endpointOperator]

/-- REDUCTION: endpoint nonnegativity makes the complete source restriction PSD. -/
theorem endpointSourceCompression_posSemidef (hendpoint : QutritEndpointInequality)
    (X : Matrix QutritSites (Fin 2) ℂ) : (endpointSourceCompression X).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨Matrix.isHermitian_conjTranspose_mul_mul _ endpointOperator_isHermitian, ?_⟩
  intro v
  let B : Matrix (Fin 2) QutritSites ℂ := fun i j => v (i, j)
  have hv : vec B = v := rfl
  rw [← expectation_eq_dotProduct, ← hv, endpointSourceCompression_expectation]
  have h := hendpoint (X * B) (rank_le_two_of_eq_mul _ X B rfl)
  exact_mod_cast h

/-- REDUCTION: every zero gives an actual complex kernel vector of the restriction. -/
theorem endpointSourceCompression_zero_kernel (hendpoint : QutritEndpointInequality)
    (X : Matrix QutritSites (Fin 2) ℂ) (B : Matrix (Fin 2) QutritSites ℂ)
    (hzero : endpointEnergy (X * B) = 0) :
    endpointSourceCompression X *ᵥ vec B = 0 := by
  apply (endpointSourceCompression_posSemidef hendpoint X).dotProduct_mulVec_zero_iff.mp
  rw [← expectation_eq_dotProduct, endpointSourceCompression_expectation, hzero,
    Complex.ofReal_zero]

/-- Apply the original endpoint operator and restore its actual matrix indices. -/
def endpointImage (C : Matrix QutritSites QutritSites ℂ) :
    Matrix QutritSites QutritSites ℂ :=
  fun i j => (endpointOperator *ᵥ vec C) (i, j)

/-- REDUCTION: stationarity holds for every complex coefficient variation on
the source plane. No normalization or full-rank source assumption is required. -/
theorem endpointSource_zero_gradient (hendpoint : QutritEndpointInequality)
    (X : Matrix QutritSites (Fin 2) ℂ) (B : Matrix (Fin 2) QutritSites ℂ)
    (hzero : endpointEnergy (X * B) = 0) : Xᴴ * endpointImage (X * B) = 0 := by
  have h := endpointSourceCompression_zero_kernel hendpoint X B hzero
  rw [endpointSourceCompression, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    endpointSourceLift_mulVec] at h
  have hcontract (Y : Matrix QutritSites QutritSites ℂ) :
      (endpointSourceLift X)ᴴ *ᵥ vec Y = vec (Xᴴ * Y) := by
    funext p
    rcases p with ⟨i, a, b, c⟩
    simp [endpointSourceLift, Matrix.conjTranspose_kronecker,
      Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
      Matrix.one_apply, vec, Matrix.mul_apply, apply_ite, ite_mul]
  change (endpointSourceLift X)ᴴ *ᵥ vec (endpointImage (X * B)) = 0 at h
  rw [hcontract] at h
  ext i j
  exact congrFun h (i, j)

end ThreeCopyQutritWerner
