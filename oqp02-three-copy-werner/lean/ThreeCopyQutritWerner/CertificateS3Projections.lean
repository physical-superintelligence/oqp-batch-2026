module

public import ThreeCopyQutritWerner.CertificateRegisterMatrix
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section


/-!
# Exact three-site stabilizer projections

The archive uses the symmetric, alternating, and one minimal standard
projection when all three local types agree. We retain the other standard
projection too, so the four projections sum to the full identity. Every
coefficient identity is checked over all six permutations using rational
kernel arithmetic. Equal multiplicity of the two standard pieces and the
particular archive image frames are separate obligations.
-/

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace ThreeCopyQutritWerner

def certificatePerm3Images : Fin 6 → Fin 3 → Fin 3 :=
  ![![0, 1, 2], ![0, 2, 1], ![1, 0, 2], ![1, 2, 0], ![2, 0, 1], ![2, 1, 0]]

def certificatePerm3InverseImages : Fin 6 → Fin 3 → Fin 3 :=
  ![![0, 1, 2], ![0, 2, 1], ![1, 0, 2], ![2, 0, 1], ![1, 2, 0], ![2, 1, 0]]

def certificatePerm3 (i : Fin 6) : Equiv.Perm (Fin 3) where
  toFun := certificatePerm3Images i
  invFun := certificatePerm3InverseImages i
  left_inv := by fin_cases i <;> decide
  right_inv := by fin_cases i <;> decide

theorem certificatePerm3_bijective : Function.Bijective certificatePerm3 := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro i j h
    have hi : Function.Injective certificatePerm3Images := by decide
    apply hi
    funext k
    exact Equiv.congr_fun h k
  · norm_num [Fintype.card_perm, Nat.factorial]

theorem certificate_sum_perm3 {M : Type*} [AddCommMonoid M]
    (f : Equiv.Perm (Fin 3) → M) :
    (∑ σ, f σ) = ∑ i : Fin 6, f (certificatePerm3 i) := by
  symm
  exact Fintype.sum_equiv (Equiv.ofBijective certificatePerm3
    certificatePerm3_bijective) _ _ (fun _ => rfl)

/-- Symmetric, alternating, standard-plus and standard-minus coefficients.
The third row is `(1 - (1+r+r²)/3) (1+s)/2` for `s=(01)`. -/
def certificateS3Weight (kind : Fin 4) (σ : Equiv.Perm (Fin 3)) : ℚ :=
  let plus : ℚ := 1 / 6
  let minus : ℚ := if σ = certificatePerm3 0 ∨ σ = certificatePerm3 3 ∨
    σ = certificatePerm3 4 then 1 / 6 else -(1 / 6)
  let standard : ℚ := if σ = certificatePerm3 0 ∨ σ = certificatePerm3 2 then
    1 / 3 else -(1 / 6)
  ![plus, minus, standard, (if σ = 1 then 1 else 0) - plus - minus - standard] kind

set_option maxHeartbeats 2000000 in
/-- Full rational convolution gives four pairwise orthogonal idempotents. -/
theorem certificateS3Weight_convolution (a b : Fin 4) (τ : Equiv.Perm (Fin 3)) :
    (∑ σ : Equiv.Perm (Fin 3),
      certificateS3Weight a σ * certificateS3Weight b (σ⁻¹ * τ)) =
        if a = b then certificateS3Weight a τ else 0 := by
  obtain ⟨t, rfl⟩ := certificatePerm3_bijective.surjective τ
  rw [certificate_sum_perm3]
  fin_cases a <;> fin_cases b <;> fin_cases t <;> decide +kernel

theorem certificateS3Weight_inv (a : Fin 4) (σ : Equiv.Perm (Fin 3)) :
    certificateS3Weight a σ⁻¹ = certificateS3Weight a σ := by
  obtain ⟨t, rfl⟩ := certificatePerm3_bijective.surjective σ
  fin_cases a <;> fin_cases t <;> decide +kernel

theorem certificateS3Weight_partition (σ : Equiv.Perm (Fin 3)) :
    (∑ a : Fin 4, certificateS3Weight a σ) = if σ = 1 then 1 else 0 := by
  obtain ⟨t, rfl⟩ := certificatePerm3_bijective.surjective σ
  fin_cases t <;> decide +kernel

/-- The finite group-algebra product identity for arbitrary matrix representations. -/
theorem certificate_matrix_sum_mul
    {G n : Type*} [Group G] [Fintype G] [Fintype n]
    (A : G → Matrix n n ℂ) (w v : G → ℂ)
    (hA : ∀ σ τ, A σ * A τ = A (σ * τ)) :
    (∑ σ, w σ • A σ) * (∑ τ, v τ • A τ) =
      ∑ τ, (∑ σ, w σ * v (σ⁻¹ * τ)) • A τ := by
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hA]
  have hre : ∀ σ : G,
      (∑ τ : G, (w σ * v τ) • A (σ * τ)) =
        ∑ τ : G, (w σ * v (σ⁻¹ * τ)) • A τ := by
    intro σ
    refine Fintype.sum_equiv (Equiv.mulLeft σ) _ _ ?_
    intro τ
    simp
  simp_rw [hre]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro τ _
  rw [Finset.sum_smul]

/-- The exact stabilizer matrix in any complex representation of the three-site group. -/
def certificateS3Projection {n : Type*} [Fintype n]
    (A : Equiv.Perm (Fin 3) → Matrix n n ℂ) (kind : Fin 4) : Matrix n n ℂ :=
  ∑ σ, (certificateS3Weight kind σ : ℂ) • A σ

theorem certificateS3Projection_mul
    {n : Type*} [Fintype n]
    (A : Equiv.Perm (Fin 3) → Matrix n n ℂ)
    (hA : ∀ σ τ, A σ * A τ = A (σ * τ)) (a b : Fin 4) :
    certificateS3Projection A a * certificateS3Projection A b =
      if a = b then certificateS3Projection A a else 0 := by
  rw [certificateS3Projection, certificateS3Projection, certificate_matrix_sum_mul A _ _ hA]
  have hcast : ∀ τ : Equiv.Perm (Fin 3),
      (∑ σ, (certificateS3Weight a σ : ℂ) * (certificateS3Weight b (σ⁻¹ * τ) : ℂ)) =
        if a = b then (certificateS3Weight a τ : ℂ) else 0 := by
    intro τ
    have h := congrArg (fun x : ℚ => (x : ℂ)) (certificateS3Weight_convolution a b τ)
    by_cases hab : a = b <;>
      simpa only [hab, if_true, if_false, Rat.cast_sum, Rat.cast_mul, Rat.cast_zero] using h
  simp_rw [hcast]
  by_cases h : a = b <;> simp [h, certificateS3Projection]

/-- The four actual projections partition the complete representation space. -/
theorem certificateS3Projection_sum
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Equiv.Perm (Fin 3) → Matrix n n ℂ) (hA : A 1 = 1) :
    (∑ a : Fin 4, certificateS3Projection A a) = 1 := by
  simp only [certificateS3Projection]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, ← Rat.cast_sum, certificateS3Weight_partition]
  simp only [apply_ite, Rat.cast_one, Rat.cast_zero, ite_smul, one_smul, zero_smul]
  simpa using hA

/-- Real inverse-invariant weights give physical Hermitian projections. -/
theorem certificateS3Projection_hermitian
    {n : Type*} [Fintype n]
    (A : Equiv.Perm (Fin 3) → Matrix n n ℂ)
    (hA : ∀ σ, (A σ)ᴴ = A σ⁻¹) (a : Fin 4) :
    (certificateS3Projection A a)ᴴ = certificateS3Projection A a := by
  unfold certificateS3Projection
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_ratCast, hA]
  refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin 3))) _ _ ?_
  intro σ
  simp only [Equiv.inv_apply, certificateS3Weight_inv]

/-- Every piece is positive in a unitary physical representation. -/
theorem certificateS3Projection_posSemidef
    {n : Type*} [Fintype n]
    (A : Equiv.Perm (Fin 3) → Matrix n n ℂ)
    (hmul : ∀ σ τ, A σ * A τ = A (σ * τ))
    (hstar : ∀ σ, (A σ)ᴴ = A σ⁻¹) (a : Fin 4) :
    (certificateS3Projection A a).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (certificateS3Projection A a)
  rwa [certificateS3Projection_hermitian A hstar a,
    certificateS3Projection_mul A hmul a a, if_pos rfl] at h

/-- The actual permutation representation on three sites of the same local dimension. -/
def certificateS3SiteProjection {n : Type*} [Fintype n] [DecidableEq n]
    (a : Fin 4) : Matrix (Fin 3 → n) (Fin 3 → n) ℂ :=
  certificateS3Projection (fun σ => (certificateRegisterPerm σ).permMatrix ℂ) a

theorem certificateS3SiteProjection_mul {n : Type*} [Fintype n] [DecidableEq n]
    (a b : Fin 4) :
    certificateS3SiteProjection (n := n) a * certificateS3SiteProjection b =
      if a = b then certificateS3SiteProjection a else 0 :=
  certificateS3Projection_mul _ certificateRegisterMatrix_mul a b

theorem certificateS3SiteProjection_sum {n : Type*} [Fintype n] [DecidableEq n] :
    (∑ a : Fin 4, certificateS3SiteProjection (n := n) a) = 1 :=
  certificateS3Projection_sum _ certificateRegisterMatrix_one

theorem certificateS3SiteProjection_posSemidef {n : Type*} [Fintype n] [DecidableEq n]
    (a : Fin 4) : (certificateS3SiteProjection (n := n) a).PosSemidef := by
  apply certificateS3Projection_posSemidef _ certificateRegisterMatrix_mul
  intro σ
  rw [Matrix.conjTranspose_permMatrix, certificateRegisterPerm_inv]

end ThreeCopyQutritWerner
