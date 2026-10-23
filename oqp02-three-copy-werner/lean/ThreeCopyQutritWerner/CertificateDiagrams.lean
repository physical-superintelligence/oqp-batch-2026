module

public import ThreeCopyQutritWerner.CertificateRegisterPerm
public import Mathlib.Data.Matrix.Basis

@[expose] public section


/-!
# Sparse physical diagrams for the exact local certificate data

The archive's local diagrams are permutations of six registers followed by
partial transpose on a selected set of registers.  Their sparse expansion has
only `d^k` terms.  In particular, checking their compression to the original
integer multiplicity frames requires 729 summands per entry at `d=3`, `k=6`,
rather than a dense 729 by 729 matrix multiplication.

This file binds that sparse formula to literal partial transpose.  It does not
assert that any archive frame is complete or that any archive array is correct.
Those are separate finite identities and representation-completeness obligations.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

/-- Swap the row and column coordinate exactly on the selected registers. -/
def certificateWordSwap {k : ℕ} {n : Type*} (S : Finset (Fin k))
    (r c : Fin k → n) : Fin k → n :=
  fun i => if i ∈ S then c i else r i

theorem certificateWordSwap_involution {k : ℕ} {n : Type*} (S : Finset (Fin k))
    (r c : Fin k → n) :
    certificateWordSwap S (certificateWordSwap S r c) (certificateWordSwap S c r) = r := by
  funext i
  by_cases hi : i ∈ S <;> simp [certificateWordSwap, hi]

/-- The index permutation underlying register partial transpose. -/
def certificateWordSwapEquiv {k : ℕ} {n : Type*} (S : Finset (Fin k)) :
    Equiv.Perm ((Fin k → n) × (Fin k → n)) where
  toFun x := (certificateWordSwap S x.1 x.2, certificateWordSwap S x.2 x.1)
  invFun x := (certificateWordSwap S x.1 x.2, certificateWordSwap S x.2 x.1)
  left_inv x := by simp only [certificateWordSwap_involution]
  right_inv x := by simp only [certificateWordSwap_involution]

/-- Literal partial transpose on arbitrary whole registers. -/
def certificateWordTranspose {k : ℕ} {n R : Type*} (S : Finset (Fin k))
    (M : Matrix (Fin k → n) (Fin k → n) R) : Matrix (Fin k → n) (Fin k → n) R :=
  fun r c => M (certificateWordSwap S r c) (certificateWordSwap S c r)

@[simp]
theorem certificateWordTranspose_involution {k : ℕ} {n R : Type*}
    (S : Finset (Fin k)) (M : Matrix (Fin k → n) (Fin k → n) R) :
    certificateWordTranspose S (certificateWordTranspose S M) = M := by
  ext r c
  simp only [certificateWordTranspose, certificateWordSwap_involution]

theorem certificateWordTranspose_sum {k : ℕ} {n R ι : Type*} [AddCommMonoid R]
    [Fintype ι] (S : Finset (Fin k)) (M : ι → Matrix (Fin k → n) (Fin k → n) R) :
    certificateWordTranspose S (∑ t, M t) = ∑ t, certificateWordTranspose S (M t) := by
  ext r c
  simp only [certificateWordTranspose, Matrix.sum_apply]

/-- Partial transpose moves the two coordinates of a matrix unit. -/
theorem certificateWordTranspose_single {k : ℕ} {n R : Type*} [DecidableEq n]
    [Zero R] (S : Finset (Fin k)) (a b : Fin k → n) (z : R) :
    certificateWordTranspose S (Matrix.single a b z) =
      Matrix.single (certificateWordSwap S a b) (certificateWordSwap S b a) z := by
  ext r c
  have h : (a = certificateWordSwap S r c ∧ b = certificateWordSwap S c r) ↔
      (certificateWordSwap S a b = r ∧ certificateWordSwap S b a = c) := by
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨certificateWordSwap_involution S r c, certificateWordSwap_involution S c r⟩
    · rintro ⟨ha, hb⟩
      rw [← ha, ← hb]
      simp only [certificateWordSwap_involution, and_self]
  simp only [certificateWordTranspose, Matrix.single, Matrix.of_apply, h]

/-- Sparse expansion of a permutation matrix, in the archive's row/column convention. -/
theorem certificateInversePermMatrix_eq_sum_single {n R : Type*}
    [Fintype n] [DecidableEq n] [AddCommMonoid R] [One R] (e : Equiv.Perm n) :
    (e⁻¹).permMatrix R = ∑ w : n, Matrix.single (e w) w (1 : R) := by
  ext r c
  simp [Matrix.sum_apply, Matrix.single, PEquiv.toMatrix_toPEquiv_apply, Equiv.eq_symm_apply,
    eq_comm, and_comm, ite_and]

/-- The exact local diagram: permute the words, then transpose the selected registers. -/
def certificateLocalDiagram {k : ℕ} {n R : Type*} [Fintype n] [DecidableEq n]
    [Zero R] [One R] (S : Finset (Fin k)) (σ : Equiv.Perm (Fin k)) :
    Matrix (Fin k → n) (Fin k → n) R :=
  certificateWordTranspose S (((certificateRegisterPerm (n := n) σ)⁻¹).permMatrix R)

/-- Literal physical diagrams have exactly the archive's word-indexed sparse formula. -/
theorem certificateLocalDiagram_eq_sparse {k : ℕ} {n R : Type*}
    [Fintype n] [DecidableEq n] [AddCommMonoid R] [One R]
    (S : Finset (Fin k)) (σ : Equiv.Perm (Fin k)) :
    certificateLocalDiagram (n := n) (R := R) S σ =
      ∑ w : Fin k → n,
        Matrix.single (certificateWordSwap S (w ∘ σ) w)
          (certificateWordSwap S w (w ∘ σ)) (1 : R) := by
  rw [certificateLocalDiagram, certificateInversePermMatrix_eq_sum_single,
    certificateWordTranspose_sum]
  apply Finset.sum_congr rfl
  intro w _
  exact certificateWordTranspose_single S _ _ _

/-- Compressing a sparse matrix only sums over its listed nonzero contributions. -/
theorem certificateSparseMatrix_compression {n m w R : Type*}
    [Fintype n] [Fintype w] [DecidableEq n] [CommSemiring R]
    (U : Matrix n m R) (row col : w → n) (weight : w → R) (i j : m) :
    (Uᵀ * (∑ t, Matrix.single (row t) (col t) (weight t)) * U) i j =
      ∑ t, U (row t) i * weight t * U (col t) j := by
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro t _
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.transpose_apply,
    ite_and, mul_ite, ite_mul]

/-- The integer/rational table formula `Dσ = Uᵀ (Γ Pσ) U` of the certificate. -/
theorem certificateLocalDiagram_compression {k : ℕ} {n m R : Type*}
    [Fintype n] [DecidableEq n] [CommSemiring R]
    (S : Finset (Fin k)) (σ : Equiv.Perm (Fin k))
    (U : Matrix (Fin k → n) m R) (i j : m) :
    (Uᵀ * certificateLocalDiagram (n := n) (R := R) S σ * U) i j =
      ∑ w : Fin k → n,
        U (certificateWordSwap S (w ∘ σ) w) i *
          U (certificateWordSwap S w (w ∘ σ)) j := by
  rw [certificateLocalDiagram_eq_sparse, certificateSparseMatrix_compression]
  simp only [mul_one]

/-- The same sparse compression formula with the physical Hermitian adjoint. -/
theorem certificateLocalDiagram_compression_complex {k : ℕ} {n m : Type*}
    [Fintype n] [DecidableEq n]
    (S : Finset (Fin k)) (σ : Equiv.Perm (Fin k))
    (U : Matrix (Fin k → n) m ℂ) (i j : m) :
    (Uᴴ * certificateLocalDiagram (n := n) (R := ℂ) S σ * U) i j =
      ∑ w : Fin k → n,
        star (U (certificateWordSwap S (w ∘ σ) w) i) *
          U (certificateWordSwap S w (w ∘ σ)) j := by
  rw [certificateLocalDiagram_eq_sparse]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro w _
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply,
    ite_and, mul_ite, ite_mul]

end ThreeCopyQutritWerner
