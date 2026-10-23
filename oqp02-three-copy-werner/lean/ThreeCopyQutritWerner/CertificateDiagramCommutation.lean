module

public import ThreeCopyQutritWerner.CertificateSiteActions

@[expose] public section


/-!
# Physical diagram commutation with the signed local generators

Register permutations commute with the uniform matrix-unit action. Literal
partial transpose changes that action to the fundamental/dual signed action.
Consequently every physical diagram used by the local certificate commutes
with all the raising and lowering generators of the corresponding frames.
The complementary convention in sector 0 gives the same full commutant.
-/

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

section General

variable {k : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

theorem certificateSiteMatrixUnit_mulVec (s : Fin k) (i j : n)
    (v : (Fin k → n) → ℤ) (r : Fin k → n) :
    (certificateSiteMatrixUnit s i j *ᵥ v) r =
      if r s = i then v (Function.update r s j) else 0 := by
  simp only [Matrix.mulVec, dotProduct, certificateSiteMatrixUnit,
    certificateSiteTransition_iff]
  by_cases h : r s = i <;> simp [h, ite_mul]

/-- A whole-register permutation commutes with the uniform local generator. -/
theorem certificateRegisterPerm_commutes_uniform (σ : Equiv.Perm (Fin k)) (i j : n) :
    (certificateRegisterPerm (n := n) σ).permMatrix ℤ * certificateUniformGenerator i j =
      certificateUniformGenerator i j * (certificateRegisterPerm σ).permMatrix ℤ := by
  apply Matrix.mulVec_injective
  funext v
  ext r
  simp only [← Matrix.mulVec_mulVec, Matrix.permMatrix_mulVec,
    certificateUniformGenerator, Matrix.sum_mulVec, Finset.sum_apply,
    Function.comp_apply, certificateSiteMatrixUnit_mulVec]
  change (∑ s : Fin k, if r (σ s) = i then
      v (Function.update (r ∘ σ) s j) else 0) =
    ∑ t : Fin k, if r t = i then v (Function.update r t j ∘ σ) else 0
  apply Fintype.sum_equiv σ _ _
  intro s
  rw [Function.update_comp_equiv]
  simp

theorem certificateWordTranspose_sub (S : Finset (Fin k))
    (M N : Matrix (Fin k → n) (Fin k → n) ℤ) :
    certificateWordTranspose S (M - N) =
      certificateWordTranspose S M - certificateWordTranspose S N := rfl

/-- Exact partial-transpose identity for the uniform commutator. -/
theorem certificateWordTranspose_uniform_commutator (S : Finset (Fin k)) (i j : n)
    (M : Matrix (Fin k → n) (Fin k → n) ℤ) :
    certificateWordTranspose S
        (certificateUniformGenerator i j * M - M * certificateUniformGenerator i j) =
      certificateSignedGenerator Sᶜ i j * certificateWordTranspose S M -
        certificateWordTranspose S M * certificateSignedGenerator Sᶜ i j := by
  calc
    _ = ∑ s : Fin k, certificateWordTranspose S
        (certificateSiteMatrixUnit s i j * M - M * certificateSiteMatrixUnit s i j) := by
      rw [certificateUniformGenerator, Matrix.sum_mul, Matrix.mul_sum,
        ← Finset.sum_sub_distrib, certificateWordTranspose_sum]
    _ = ∑ s : Fin k, (
        (if s ∈ Sᶜ then certificateSiteMatrixUnit s i j
          else -certificateSiteMatrixUnit s j i) * certificateWordTranspose S M -
        certificateWordTranspose S M *
          (if s ∈ Sᶜ then certificateSiteMatrixUnit s i j
            else -certificateSiteMatrixUnit s j i)) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [certificateWordTranspose_sub]
      by_cases hs : s ∈ S
      · rw [certificateWordTranspose_site_mul_mem S s hs,
          certificateWordTranspose_mul_site_mem S s hs]
        simp only [Finset.mem_compl, hs, not_true_eq_false, if_false,
          Matrix.neg_mul, Matrix.mul_neg]
        abel
      · rw [certificateWordTranspose_site_mul_notMem S s hs,
          certificateWordTranspose_mul_site_notMem S s hs]
        simp only [Finset.mem_compl, hs, not_false_eq_true, if_true]
    _ = _ := by
      simp only [certificateSignedGenerator, Matrix.sum_mul, Matrix.mul_sum,
        Finset.sum_sub_distrib]

/-- Any uniformly commuting matrix acquires the literal signed commutation after PT. -/
theorem certificateWordTranspose_commutes_signed (S : Finset (Fin k)) (i j : n)
    (M : Matrix (Fin k → n) (Fin k → n) ℤ)
    (h : certificateUniformGenerator i j * M = M * certificateUniformGenerator i j) :
    certificateSignedGenerator Sᶜ i j * certificateWordTranspose S M =
      certificateWordTranspose S M * certificateSignedGenerator Sᶜ i j := by
  have hc := certificateWordTranspose_uniform_commutator S i j M
  rw [h, sub_self] at hc
  have hz : certificateWordTranspose S (0 : Matrix (Fin k → n) (Fin k → n) ℤ) = 0 := rfl
  rw [hz] at hc
  exact sub_eq_zero.mp hc.symm

/-- Every physical PT-permutation diagram commutes with the corresponding signed action. -/
theorem certificateLocalDiagram_commutes_signed (S : Finset (Fin k))
    (σ : Equiv.Perm (Fin k)) (i j : n) :
    certificateSignedGenerator Sᶜ i j * certificateLocalDiagram S σ =
      certificateLocalDiagram S σ * certificateSignedGenerator Sᶜ i j := by
  apply certificateWordTranspose_commutes_signed
  simpa only [certificateRegisterPerm_inv] using
    (certificateRegisterPerm_commutes_uniform (n := n) σ⁻¹ i j).symm

end General

/-- The same commutation for the source-bound sparse qutrit generators. -/
theorem certificateLocalDiagram_commutes_generator (S : Finset (Fin 6))
    (σ : Equiv.Perm (Fin 6)) (i j : Fin 3) :
    certificateLocalGenerator Sᶜ i j * certificateLocalDiagram S σ =
      certificateLocalDiagram S σ * certificateLocalGenerator Sᶜ i j := by
  simp only [certificateLocalGenerator_eq_signed]
  exact certificateLocalDiagram_commutes_signed S σ i j

/-- Complementing all fundamental/dual sites preserves commutation with every generator. -/
theorem certificateLocalDiagram_commutes_complement_generator (S : Finset (Fin 6))
    (σ : Equiv.Perm (Fin 6)) (i j : Fin 3) :
    certificateLocalGenerator S i j * certificateLocalDiagram S σ =
      certificateLocalDiagram S σ * certificateLocalGenerator S i j := by
  have h := certificateLocalDiagram_commutes_generator S σ j i
  rw [certificateLocalGenerator_compl, Matrix.neg_mul, Matrix.mul_neg] at h
  exact neg_injective h

/-- Sector 2 uses the one fundamental register {0}. -/
theorem certificateLocalDiagram2_commutes (σ : Equiv.Perm (Fin 6)) (i j : Fin 3) :
    certificateLocalGenerator {0} i j * certificateLocalDiagram {1, 2, 3, 4, 5} σ =
      certificateLocalDiagram {1, 2, 3, 4, 5} σ * certificateLocalGenerator {0} i j := by
  have h : ({1, 2, 3, 4, 5} : Finset (Fin 6))ᶜ = {0} := by decide
  simpa only [h] using certificateLocalDiagram_commutes_generator {1, 2, 3, 4, 5} σ i j

/-- Sector 1 uses the three fundamental registers {0,1,2}. -/
theorem certificateLocalDiagram1_commutes (σ : Equiv.Perm (Fin 6)) (i j : Fin 3) :
    certificateLocalGenerator {0, 1, 2} i j * certificateLocalDiagram {3, 4, 5} σ =
      certificateLocalDiagram {3, 4, 5} σ * certificateLocalGenerator {0, 1, 2} i j := by
  have h : ({3, 4, 5} : Finset (Fin 6))ᶜ = {0, 1, 2} := by decide
  simpa only [h] using certificateLocalDiagram_commutes_generator {3, 4, 5} σ i j

/-- Sector 0 source frames use the complementary one-register convention {5}. -/
theorem certificateLocalDiagram0_commutes (σ : Equiv.Perm (Fin 6)) (i j : Fin 3) :
    certificateLocalGenerator {5} i j * certificateLocalDiagram {5} σ =
      certificateLocalDiagram {5} σ * certificateLocalGenerator {5} i j :=
  certificateLocalDiagram_commutes_complement_generator {5} σ i j

end ThreeCopyQutritWerner
