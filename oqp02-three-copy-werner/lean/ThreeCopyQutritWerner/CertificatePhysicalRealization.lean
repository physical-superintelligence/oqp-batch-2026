module

public import ThreeCopyQutritWerner.CertificateIntertwinerTrace
public import Mathlib.LinearAlgebra.Matrix.Kronecker

@[expose] public section


/-!
# Reconstructing physical operators from a complete, nonorthogonal basis

The metric here is the literal full physical Gram matrix `Sᴴ S`.
Hermiticity and positivity of a reconstructed coefficient operator follow from
that metric, rather than an assumed Euclidean or block-diagonal metric.
Concrete source-type factorization of this full Gram is a separate finite task.
-/

noncomputable section

open scoped Matrix Kronecker ComplexOrder

namespace ThreeCopyQutritWerner

/-- A true left inverse gives the prescribed action of the reconstructed operator. -/
theorem certificate_realization_action
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (S : Matrix n m ℂ) (T : Matrix m n ℂ) (A : Matrix m m ℂ)
    (hTS : T * S = 1) :
    (S * A * T) * S = S * A := by
  rw [Matrix.mul_assoc, hTS, Matrix.mul_one]

/-- Its actual compression uses the full descendant Gram. -/
theorem certificate_realization_compression
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (S : Matrix n m ℂ) (T : Matrix m n ℂ) (A : Matrix m m ℂ)
    (hTS : T * S = 1) :
    Sᴴ * (S * A * T) * S = (Sᴴ * S) * A := by
  rw [Matrix.mul_assoc Sᴴ, certificate_realization_action S T A hTS,
    ← Matrix.mul_assoc]

/-- Similarity is an actual physical congruence in the original full Gram. -/
theorem certificate_realization_eq_congruence
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n]
    (S : Matrix n m ℂ) (T : Matrix m n ℂ) (A : Matrix m m ℂ)
    (hST : S * T = 1) :
    Tᴴ * ((Sᴴ * S) * A) * T = S * A * T := by
  calc
    Tᴴ * ((Sᴴ * S) * A) * T = (Tᴴ * Sᴴ) * (S * A * T) := by
      simp only [Matrix.mul_assoc]
    _ = (S * T)ᴴ * (S * A * T) := by rw [Matrix.conjTranspose_mul]
    _ = S * A * T := by rw [hST, Matrix.conjTranspose_one, Matrix.one_mul]

/-- Positivity of the full-metric quadratic form constructs a positive physical operator. -/
theorem certificate_realization_posSemidef
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n]
    (S : Matrix n m ℂ) (T : Matrix m n ℂ) (A : Matrix m m ℂ)
    (hST : S * T = 1) (hD : ((Sᴴ * S) * A).PosSemidef) :
    (S * A * T).PosSemidef := by
  rw [← certificate_realization_eq_congruence S T A hST]
  exact hD.conjTranspose_mul_mul_same T

/-- A two-sided basis inverse makes this original-metric criterion exact. -/
theorem certificate_realization_posSemidef_iff
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (S : Matrix n m ℂ) (T : Matrix m n ℂ) (A : Matrix m m ℂ)
    (hST : S * T = 1) (hTS : T * S = 1) :
    (S * A * T).PosSemidef ↔ ((Sᴴ * S) * A).PosSemidef := by
  constructor
  · intro h
    have hc := h.conjTranspose_mul_mul_same S
    rwa [certificate_realization_compression S T A hTS] at hc
  · exact certificate_realization_posSemidef S T A hST

/-- Tensor products of complete physical bases remain bijective. -/
theorem certificate_kronecker_bijective
    {n m p q : Type*} [Fintype n] [Fintype m] [Fintype p] [Fintype q]
    [DecidableEq n] [DecidableEq m] [DecidableEq p] [DecidableEq q]
    (S : Matrix n m ℂ) (U : Matrix p q ℂ)
    (hS : Function.Bijective S.mulVec) (hU : Function.Bijective U.mulVec) :
    Function.Bijective (S ⊗ₖ U).mulVec := by
  obtain ⟨T, hST, hTS⟩ := certificate_exists_inverse_of_bijective S hS
  obtain ⟨V, hUV, hVU⟩ := certificate_exists_inverse_of_bijective U hU
  have hright : (S ⊗ₖ U) * (T ⊗ₖ V) = 1 := by
    rw [← Matrix.mul_kronecker_mul, hST, hUV, Matrix.one_kronecker_one]
  have hleft : (T ⊗ₖ V) * (S ⊗ₖ U) = 1 := by
    rw [← Matrix.mul_kronecker_mul, hTS, hVU, Matrix.one_kronecker_one]
  constructor
  · intro x y h
    have hc := congrArg (fun v => (T ⊗ₖ V) *ᵥ v) h
    simpa only [Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec] using hc
  · exact Matrix.mulVec_surjective_iff_exists_right_inverse.mpr ⟨T ⊗ₖ V, hright⟩

/-- Tensoring literal physical actions preserves their exact coefficient actions. -/
theorem certificate_kronecker_intertwines
    {n m p q : Type*} [Fintype n] [Fintype m] [Fintype p] [Fintype q]
    (M : Matrix n n ℂ) (N : Matrix p p ℂ)
    (S : Matrix n m ℂ) (U : Matrix p q ℂ)
    (A : Matrix m m ℂ) (B : Matrix q q ℂ)
    (hM : M * S = S * A) (hN : N * U = U * B) :
    (M ⊗ₖ N) * (S ⊗ₖ U) = (S ⊗ₖ U) * (A ⊗ₖ B) := by
  rw [← Matrix.mul_kronecker_mul, hM, hN, Matrix.mul_kronecker_mul]

end ThreeCopyQutritWerner
