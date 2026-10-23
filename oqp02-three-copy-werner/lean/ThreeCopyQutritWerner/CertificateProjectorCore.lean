module

public import ThreeCopyQutritWerner.CertificateCharacter
public import ThreeCopyQutritWerner.CertificateRegisterPerm
public import Mathlib.LinearAlgebra.Matrix.Permutation

@[expose] public section



/-! Generic character carrier, antisymmetry and tensor/reindex lemmas.
The existing generic declarations and proofs are moved verbatim;
the concrete SixRegisters carrier remains in CertificateProjector. -/

noncomputable section
open scoped BigOperators Matrix Kronecker ComplexOrder
set_option maxRecDepth 100000
namespace ThreeCopyQutritWerner

theorem certificateFixedCount_inv {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    certificateFixedCount σ⁻¹ = certificateFixedCount σ := by
  unfold certificateFixedCount
  apply Finset.sum_congr rfl
  intro i _
  have hi : σ⁻¹ i = i ↔ σ i = i := by
    constructor
    · intro h
      have h' := congrArg σ h
      simpa using h'.symm
    · intro h
      have h' := congrArg (fun j => (σ⁻¹ : Equiv.Perm (Fin k)) j) h
      simpa using h'.symm
  simp only [hi]

/-- Appendix B's character is unchanged by reversing a permutation. -/
theorem certificateCharacter_inv {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    certificateCharacter σ⁻¹ = certificateCharacter σ := by
  have hsq : σ⁻¹ * σ⁻¹ = (σ * σ)⁻¹ := by rw [mul_inv_rev]
  simp only [certificateCharacter, hsq, certificateFixedCount_inv]

/-- Matrix realization of the literal rational character sum. -/
def certificateCentralMatrix {k : ℕ} {n : Type*} [Fintype n] [DecidableEq n]
    (denominator : ℚ) : Matrix (Fin k → n) (Fin k → n) ℂ :=
  ∑ σ : Equiv.Perm (Fin k), ((certificateCharacter σ / denominator : ℚ) : ℂ) •
    (certificateRegisterPerm σ).permMatrix ℂ

theorem certificateCentralMatrix_mulVec {k : ℕ} {n : Type*} [Fintype n] [DecidableEq n]
    (denominator : ℚ) (f : (Fin k → n) → ℂ) :
    certificateCentralMatrix denominator *ᵥ f = certificateCentralAction denominator f := by
  ext r
  simp only [certificateCentralMatrix, Matrix.sum_mulVec, Matrix.smul_mulVec,
    Matrix.permMatrix_mulVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Function.comp_apply, certificateRegisterPerm, Equiv.coe_fn_mk,
    certificateCentralAction, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  push_cast
  ring

/-- The character sum is Hermitian because its real coefficients are inverse-invariant. -/
theorem certificateCentralMatrix_hermitian {k : ℕ} {n : Type*} [Fintype n]
    [DecidableEq n] (denominator : ℚ) :
    (certificateCentralMatrix (k := k) (n := n) denominator)ᴴ =
      certificateCentralMatrix denominator := by
  unfold certificateCentralMatrix
  rw [Matrix.conjTranspose_sum]
  refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin k))) _ _ ?_
  intro σ
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_permMatrix, star_ratCast,
    Equiv.inv_apply, certificateCharacter_inv, certificateRegisterPerm_inv]

/-- Antisymmetrization on two whole registers, `Aᵢⱼ=(I−Fᵢⱼ)/2`. -/
def certificateRegisterAntisym {k : ℕ} {n : Type*} [Fintype n] [DecidableEq n]
    (i j : Fin k) : Matrix (Fin k → n) (Fin k → n) ℂ :=
  (1 / 2 : ℂ) • (1 - (certificateRegisterPerm (Equiv.swap i j)).permMatrix ℂ)

theorem certificateRegisterAntisym_hermitian {k : ℕ} {n : Type*} [Fintype n]
    [DecidableEq n] (i j : Fin k) :
    (certificateRegisterAntisym (n := n) i j)ᴴ = certificateRegisterAntisym i j := by
  simp [certificateRegisterAntisym, Matrix.conjTranspose_smul,
    certificateRegisterPerm_inv]

/-- The holomorphic column feature on its five non-column registers. -/
def certificateColumnFeature {n : Type*} [Fintype n]
    (X : Matrix n (Fin 2) ℂ) (B : Matrix (Fin 2) n ℂ) (q : n) (r : Fin 5 → n) : ℂ :=
  (X * B) (r 0) q * bivecMat X (r 1) (r 2) * bivecMat X (r 3) (r 4)

theorem certificateRegisterAntisym₁₂_fixes {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n (Fin 2) ℂ) (B : Matrix (Fin 2) n ℂ) (q : n) :
    certificateRegisterAntisym 1 2 *ᵥ certificateColumnFeature X B q =
      certificateColumnFeature X B q := by
  ext r
  simp [certificateRegisterAntisym, Matrix.smul_mulVec, Matrix.sub_mulVec,
    Matrix.permMatrix_mulVec, certificateRegisterPerm, certificateColumnFeature,
    Equiv.swap_apply_def]
  rw [bivecMat_entry_skew X (r 1) (r 2)]
  ring

theorem certificateRegisterAntisym₃₄_fixes {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n (Fin 2) ℂ) (B : Matrix (Fin 2) n ℂ) (q : n) :
    certificateRegisterAntisym 3 4 *ᵥ certificateColumnFeature X B q =
      certificateColumnFeature X B q := by
  ext r
  simp [certificateRegisterAntisym, Matrix.smul_mulVec, Matrix.sub_mulVec,
    Matrix.permMatrix_mulVec, certificateRegisterPerm, certificateColumnFeature,
    Equiv.swap_apply_def]
  rw [bivecMat_entry_skew X (r 3) (r 4)]
  ring

/-- A concrete Hermitian compression of the holomorphic character sum.
No positivity or endpoint inequality occurs in this definition. -/
def certificateHolomorphicCarrier {n : Type*} [Fintype n] [DecidableEq n] :
    Matrix (Fin 5 → n) (Fin 5 → n) ℂ :=
  let A₁₂ := certificateRegisterAntisym (n := n) (1 : Fin 5) 2
  let A₃₄ := certificateRegisterAntisym (n := n) (3 : Fin 5) 4
  A₁₂ * A₃₄ * certificateCentralMatrix 24 * A₃₄ * A₁₂

theorem certificateHolomorphicCarrier_hermitian {n : Type*} [Fintype n]
    [DecidableEq n] :
    (certificateHolomorphicCarrier (n := n))ᴴ = certificateHolomorphicCarrier := by
  simp only [certificateHolomorphicCarrier, Matrix.conjTranspose_mul,
    certificateRegisterAntisym_hermitian, certificateCentralMatrix_hermitian,
    Matrix.mul_assoc]

/-- Appendix B's holomorphic carrier inclusion, with a concrete Hermitian matrix. -/
theorem certificateHolomorphicCarrier_fixes {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n (Fin 2) ℂ) (B : Matrix (Fin 2) n ℂ) (q : n) :
    certificateHolomorphicCarrier *ᵥ certificateColumnFeature X B q =
      certificateColumnFeature X B q := by
  have hE : certificateCentralMatrix 24 *ᵥ certificateColumnFeature X B q =
      certificateColumnFeature X B q := by
    rw [certificateCentralMatrix_mulVec]
    funext r
    exact certificateCentralAction_column_bivec_square X B q r
  simp only [certificateHolomorphicCarrier, ← Matrix.mulVec_mulVec,
    certificateRegisterAntisym₁₂_fixes, certificateRegisterAntisym₃₄_fixes, hE]

/-- Tensoring an operator with the column identity acts independently on every column. -/
theorem certificateTensorIdentity_mulVec {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq b] (A : Matrix a a ℂ) (f : a × b → ℂ) :
    (A ⊗ₖ (1 : Matrix b b ℂ)) *ᵥ f =
      fun x => (A *ᵥ fun r => f (r, x.2)) x.1 := by
  ext x
  simp [Matrix.mulVec, dotProduct, Matrix.kronecker_apply, Fintype.sum_prod_type,
    Matrix.one_apply, mul_ite, ite_mul]

/-- Reindex the same tensor carrier, with all index types still abstract. -/
theorem certificateHolomorphicCarrier_reindex_hermitian {n m : Type*}
    [Fintype n] [DecidableEq n] (e : m ≃ ((Fin 5 → n) × n)) :
    ((certificateHolomorphicCarrier (n := n) ⊗ₖ (1 : Matrix n n ℂ)).submatrix e e)ᴴ =
      (certificateHolomorphicCarrier (n := n) ⊗ₖ (1 : Matrix n n ℂ)).submatrix e e := by
  simp only [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_kronecker,
    certificateHolomorphicCarrier_hermitian, Matrix.conjTranspose_one]

/-- The original carrier fixes each column feature under any equivalent indexing.
No feature-membership or carrier premise is added. The concrete six-register
statement is a specialization of this proof, not a separate finite expansion. -/
theorem certificateHolomorphicCarrier_reindex_fixes {n m : Type*}
    [Fintype n] [DecidableEq n] [Fintype m]
    (e : m ≃ ((Fin 5 → n) × n))
    (X : Matrix n (Fin 2) ℂ) (B : Matrix (Fin 2) n ℂ) :
    (certificateHolomorphicCarrier (n := n) ⊗ₖ (1 : Matrix n n ℂ)).submatrix e e *ᵥ
        (fun x => certificateColumnFeature X B (e x).2 (e x).1) =
      (fun x => certificateColumnFeature X B (e x).2 (e x).1) := by
  rw [Matrix.submatrix_mulVec_equiv]
  have hf : (fun x => certificateColumnFeature X B (e x).2 (e x).1) ∘ e.symm =
      fun y => certificateColumnFeature X B y.2 y.1 := by
    funext y
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
  rw [hf, certificateTensorIdentity_mulVec]
  funext x
  exact congrFun (certificateHolomorphicCarrier_fixes X B (e x).2) (e x).1

end ThreeCopyQutritWerner
