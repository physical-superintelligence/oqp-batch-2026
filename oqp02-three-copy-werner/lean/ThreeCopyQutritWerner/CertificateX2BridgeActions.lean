module

public import ThreeCopyQutritWerner.CertificateX2Reduced
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Data.Matrix.Block

@[expose] public section


/-!
# Block actions on a complete basis

An operator `G` *acts by* block data `A` on a basis `S` (columns indexed by `Σ i, d i`) when
`G * S = S * blockDiagonal' A`. Sums, scalar multiples and products of operators act by the
corresponding block data, and on a complete basis (surjective `S`) the block data determine the
operator. Hence an operator is positive semidefinite as soon as some positive semidefinite
operator acts by the same block data (in the bridge: the frame systems' `..._realize`).
-/

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace ThreeCopyQutritWerner

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι] {d : ι → Type*}
  [∀ i, Fintype (d i)] [∀ i, DecidableEq (d i)]

/-- `G` acts on the basis `S` by the block data `A`. -/
def X2Acts (S : Matrix n (Σ i, d i) ℂ) (G : Matrix n n ℂ) (A : ∀ i, Matrix (d i) (d i) ℂ) : Prop :=
  G * S = S * Matrix.blockDiagonal' A

theorem X2Acts.add {S : Matrix n (Σ i, d i) ℂ} {G H : Matrix n n ℂ}
    {A B : ∀ i, Matrix (d i) (d i) ℂ} (hG : X2Acts S G A) (hH : X2Acts S H B) :
    X2Acts S (G + H) (fun i => A i + B i) := by
  unfold X2Acts at *
  rw [Matrix.add_mul, hG, hH, ← Matrix.mul_add, ← Matrix.blockDiagonal'_add] <;> rfl

theorem X2Acts.sub {S : Matrix n (Σ i, d i) ℂ} {G H : Matrix n n ℂ}
    {A B : ∀ i, Matrix (d i) (d i) ℂ} (hG : X2Acts S G A) (hH : X2Acts S H B) :
    X2Acts S (G - H) (fun i => A i - B i) := by
  unfold X2Acts at *
  rw [Matrix.sub_mul, hG, hH, ← Matrix.mul_sub, ← Matrix.blockDiagonal'_sub] <;> rfl

theorem X2Acts.smul {S : Matrix n (Σ i, d i) ℂ} {G : Matrix n n ℂ}
    {A : ∀ i, Matrix (d i) (d i) ℂ} (c : ℂ) (hG : X2Acts S G A) :
    X2Acts S (c • G) (fun i => c • A i) := by
  unfold X2Acts at *
  rw [Matrix.smul_mul, hG]
  show c • (S * Matrix.blockDiagonal' A) = S * Matrix.blockDiagonal' (c • A)
  rw [Matrix.blockDiagonal'_smul, Matrix.mul_smul]

theorem X2Acts.mul {S : Matrix n (Σ i, d i) ℂ} {G H : Matrix n n ℂ}
    {A B : ∀ i, Matrix (d i) (d i) ℂ} (hG : X2Acts S G A) (hH : X2Acts S H B) :
    X2Acts S (G * H) (fun i => A i * B i) := by
  unfold X2Acts at *
  rw [Matrix.mul_assoc, hH, ← Matrix.mul_assoc, hG, Matrix.mul_assoc,
    ← Matrix.blockDiagonal'_mul]

theorem X2Acts.sum {S : Matrix n (Σ i, d i) ℂ} {κ : Type*} (s : Finset κ)
    {G : κ → Matrix n n ℂ} {A : κ → ∀ i, Matrix (d i) (d i) ℂ}
    (hG : ∀ k ∈ s, X2Acts S (G k) (A k)) :
    X2Acts S (∑ k ∈ s, G k) (fun i => ∑ k ∈ s, A k i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      unfold X2Acts
      simp only [Finset.sum_empty, Matrix.zero_mul]
      rw [show (fun i => (0 : Matrix (d i) (d i) ℂ)) = 0 from rfl, Matrix.blockDiagonal'_zero,
        Matrix.mul_zero]
  | @insert a s ha ih =>
      have h1 := hG a (Finset.mem_insert_self a s)
      have h2 := ih (fun k hk => hG k (Finset.mem_insert_of_mem hk))
      have h3 := h1.add h2
      simpa only [Finset.sum_insert ha] using h3

/-- On a complete basis, the block data determine the operator. -/
theorem X2Acts.unique {S : Matrix n (Σ i, d i) ℂ} (hS : Function.Surjective S.mulVec)
    {G H : Matrix n n ℂ} {A : ∀ i, Matrix (d i) (d i) ℂ} (hG : X2Acts S G A)
    (hH : X2Acts S H A) : G = H := by
  obtain ⟨T, hT⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp hS
  have h : G * S = H * S := by rw [hG, hH]
  calc G = G * (S * T) := by rw [hT, Matrix.mul_one]
    _ = (G * S) * T := (Matrix.mul_assoc _ _ _).symm
    _ = (H * S) * T := by rw [h]
    _ = H * (S * T) := Matrix.mul_assoc _ _ _
    _ = H := by rw [hT, Matrix.mul_one]

/-- Positivity transported from any positive semidefinite operator with the same block data. -/
theorem X2Acts.posSemidef_of_realize {S : Matrix n (Σ i, d i) ℂ}
    (hS : Function.Surjective S.mulVec) {G : Matrix n n ℂ} {A : ∀ i, Matrix (d i) (d i) ℂ}
    (hG : X2Acts S G A) (hreal : ∃ M : Matrix n n ℂ, M.PosSemidef ∧ X2Acts S M A) :
    G.PosSemidef := by
  obtain ⟨M, hM, hMA⟩ := hreal
  rw [X2Acts.unique hS hG hMA]
  exact hM

end ThreeCopyQutritWerner

end
