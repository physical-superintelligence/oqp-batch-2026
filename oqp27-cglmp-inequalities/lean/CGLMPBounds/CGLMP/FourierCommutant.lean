module

public import Mathlib

@[expose] public section


/-!
# Computational projectors and a full-support second vector

Supplement, Appendix E.1, p. 17. The argument is entrywise: commuting with
the coordinate projections forces diagonality, and one matrix with no zero
entries forces the diagonal entries to agree. A full-support rank-one vector
supplies such a matrix. The same matrix-unit calculation proves generation
of the full complex matrix algebra, with no irreducibility oracle.
-/

open Matrix
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

namespace CGLMPBounds
noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

/-- Commuting with all computational rank-one projectors forces diagonality. -/
theorem eq_diagonal_of_commute_coordinate (X : Matrix ι ι ℂ)
    (hX : ∀ a, X * Matrix.single a a 1 = Matrix.single a a 1 * X) :
    X = Matrix.diagonal (fun i => X i i) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · rw [Matrix.diagonal_apply_ne _ hij]
    exact Matrix.row_eq_zero_of_commute_single
      (show Commute (Matrix.single i i 1) X from (hX i).symm) (Ne.symm hij)

/-- A diagonal matrix commuting with a matrix having no zero entries is scalar. -/
theorem eq_scalar_of_commute_coordinate_and_full_support [Nonempty ι]
    (X R : Matrix ι ι ℂ)
    (hX : ∀ a, X * Matrix.single a a 1 = Matrix.single a a 1 * X)
    (hR : ∀ i j, R i j ≠ 0) (hXR : X * R = R * X) :
    ∃ c : ℂ, X = c • (1 : Matrix ι ι ℂ) := by
  have hD := eq_diagonal_of_commute_coordinate X hX
  have hdiag (i j : ι) : X i i = X j j := by
    have h : (Matrix.diagonal (fun k => X k k) * R) i j =
        (R * Matrix.diagonal (fun k => X k k)) i j := by
      simpa only [← hD] using congrArg (fun M : Matrix ι ι ℂ => M i j) hXR
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at h
    apply mul_right_cancel₀ (hR i j)
    simpa only [mul_comm (R i j) (X j j)] using h
  let i₀ : ι := Classical.choice inferInstance
  refine ⟨X i₀ i₀, ?_⟩
  rw [hD]
  ext i j
  by_cases hij : i = j
  · subst j
    simpa using hdiag i i₀
  · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply, hij]

/-- The rank-one matrix of a full-support vector has no zero entries. -/
theorem vecMulVec_star_entry_ne_zero (u : ι → ℂ) (hu : ∀ i, u i ≠ 0)
    (i j : ι) : Matrix.vecMulVec u (star u) i j ≠ 0 := by
  change u i * star (u j) ≠ 0
  refine mul_ne_zero (hu i) ?_
  intro h
  apply hu j
  simpa only [star_star, star_zero] using congrArg star h

/-- One full-support rank-one projector suffices in addition to the coordinate PVM.
Normalization is unnecessary for this algebraic implication. -/
theorem eq_scalar_of_commute_coordinate_and_rankOne [Nonempty ι]
    (X : Matrix ι ι ℂ) (u : ι → ℂ)
    (hX : ∀ a, X * Matrix.single a a 1 = Matrix.single a a 1 * X)
    (hu : ∀ i, u i ≠ 0)
    (hXu : X * Matrix.vecMulVec u (star u) = Matrix.vecMulVec u (star u) * X) :
    ∃ c : ℂ, X = c • (1 : Matrix ι ι ℂ) :=
  eq_scalar_of_commute_coordinate_and_full_support X _ hX
    (vecMulVec_star_entry_ne_zero u hu) hXu

/-- In particular, a second basis whose every entry is nonzero has scalar joint
commutant with the computational PVM. The stronger lemma needs only one column. -/
theorem eq_scalar_of_commute_coordinate_and_columns [Nonempty ι] [Nonempty κ]
    (X : Matrix ι ι ℂ) (U : Matrix ι κ ℂ)
    (hX : ∀ a, X * Matrix.single a a 1 = Matrix.single a a 1 * X)
    (hU : ∀ i b, U i b ≠ 0)
    (hXU : ∀ b, X * Matrix.vecMulVec (fun i => U i b) (star (fun i => U i b)) =
      Matrix.vecMulVec (fun i => U i b) (star (fun i => U i b)) * X) :
    ∃ c : ℂ, X = c • (1 : Matrix ι ι ℂ) := by
  let b : κ := Classical.choice inferInstance
  exact eq_scalar_of_commute_coordinate_and_rankOne X (fun i => U i b)
    hX (fun i => hU i b) (hXU b)

/-- A complex subalgebra containing the coordinate projections and any
full-support matrix contains every matrix unit, hence every matrix. -/
theorem subalgebra_eq_top_of_coordinate_and_full_support
    (S : Subalgebra ℂ (Matrix ι ι ℂ)) (R : Matrix ι ι ℂ)
    (hcoord : ∀ a, Matrix.single a a (1 : ℂ) ∈ S)
    (hR : R ∈ S) (hnz : ∀ i j, R i j ≠ 0) : S = ⊤ := by
  have hunit (i j : ι) : Matrix.single i j (1 : ℂ) ∈ S := by
    have h := S.mul_mem (S.mul_mem (hcoord i) hR) (hcoord j)
    rw [Matrix.single_mul_mul_single, one_mul, mul_one] at h
    have hs := S.smul_mem h (R i j)⁻¹
    simpa only [Matrix.smul_single, smul_eq_mul, inv_mul_cancel₀ (hnz i j)] using hs
  apply top_unique
  intro M _
  rw [Matrix.matrix_eq_sum_single M]
  apply S.sum_mem
  intro i _
  apply S.sum_mem
  intro j _
  simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using
    S.smul_mem (hunit i j) (M i j)

theorem subalgebra_eq_top_of_coordinate_and_rankOne
    (S : Subalgebra ℂ (Matrix ι ι ℂ)) (u : ι → ℂ)
    (hcoord : ∀ a, Matrix.single a a (1 : ℂ) ∈ S)
    (hu : Matrix.vecMulVec u (star u) ∈ S) (hnz : ∀ i, u i ≠ 0) : S = ⊤ :=
  subalgebra_eq_top_of_coordinate_and_full_support S _ hcoord hu
    (vecMulVec_star_entry_ne_zero u hnz)

section ChangeBasis
variable [Fintype κ] [DecidableEq κ]

/-- Conjugation by a possibly differently indexed unitary preserves products. -/
theorem basis_conjugate_mul (U : Matrix ι κ ℂ) (hU : U * Uᴴ = 1)
    (X Y : Matrix ι ι ℂ) :
    (Uᴴ * X * U) * (Uᴴ * Y * U) = Uᴴ * (X * Y) * U := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc U Uᴴ, hU, Matrix.one_mul]

theorem basis_conjugate_commute (U : Matrix ι κ ℂ) (hU : U * Uᴴ = 1)
    (X Y : Matrix ι ι ℂ) (hXY : X * Y = Y * X) :
    (Uᴴ * X * U) * (Uᴴ * Y * U) = (Uᴴ * Y * U) * (Uᴴ * X * U) := by
  rw [basis_conjugate_mul U hU, basis_conjugate_mul U hU, hXY]

/-- Conjugating a rank-one projector conjugates its generating vector. -/
theorem basis_conjugate_rankOne (U : Matrix ι κ ℂ) (u : ι → ℂ) :
    Uᴴ * Matrix.vecMulVec u (star u) * U =
      Matrix.vecMulVec (Uᴴ *ᵥ u) (star (Uᴴ *ᵥ u)) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec,
    Matrix.conjTranspose_conjTranspose]

/-- A scalar matrix in unitary coordinates is the same scalar in the original coordinates. -/
theorem eq_scalar_of_basis_conjugate_eq (U : Matrix ι κ ℂ) (hU : U * Uᴴ = 1)
    (X : Matrix ι ι ℂ) (c : ℂ) (hX : Uᴴ * X * U = c • (1 : Matrix κ κ ℂ)) :
    X = c • (1 : Matrix ι ι ℂ) := by
  calc
    X = U * (Uᴴ * X * U) * Uᴴ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc U Uᴴ, hU, Matrix.one_mul,
        Matrix.mul_one]
    _ = c • (1 : Matrix ι ι ℂ) := by
      rw [hX, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hU]

end ChangeBasis
end
end CGLMPBounds
