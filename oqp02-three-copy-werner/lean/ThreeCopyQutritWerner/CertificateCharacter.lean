module

public import ThreeCopyQutritWerner.CertificateCarrier
public import ThreeCopyQutritWerner.CertificatePermutationTables

@[expose] public section


/-!
# Exact character sums for Appendix B

The character is the difference of the permutation characters on unordered
pairs and on singletons. If `a` is the number of fixed registers and `b` the
number fixed by the square, it is `(a*(a-4)+b)/2`; because `b=a+2*c₂`, this
is exactly the manuscript's `a*(a-3)/2+c₂`.

The two sums use the literal full symmetric groups, not sampled permutations.
The proofs expand only 24 or 120 register permutations and polynomial
identities. No array of dimension `27^6` is constructed.
-/

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

open scoped BigOperators

namespace ThreeCopyQutritWerner

/-- Exact number of fixed registers, regarded as a rational. -/
def certificateFixedCount {k : ℕ} (σ : Equiv.Perm (Fin k)) : ℚ :=
  ∑ i, if σ i = i then 1 else 0

/-- The character of shape `[k-2,2]` at `k=4,5`, in Appendix B's convention. -/
def certificateCharacter {k : ℕ} (σ : Equiv.Perm (Fin k)) : ℚ :=
  (certificateFixedCount σ * (certificateFixedCount σ - 4) +
    certificateFixedCount (σ * σ)) / 2

/-- Exact character values on the complete S4 enumeration. -/
def certificateCharacterTable4 : Fin 24 → ℚ :=
  ![2, 0, 0, -1, -1, 0, 0, 2, -1, 0, 0, -1, -1, 0, 0, -1, 2, 0, 0, -1, -1, 0, 0, 2]

theorem certificateCharacter_perm4 (i : Fin 24) :
    certificateCharacter (certificatePerm4 i) = certificateCharacterTable4 i := by
  fin_cases i <;>
    simp only [certificateCharacter, certificateFixedCount, Fin.sum_univ_succ,
      Fin.sum_univ_zero, Equiv.Perm.mul_apply, certificatePerm4_apply] <;>
    norm_num [certificatePerm4Images, certificateCharacterTable4]

/-- Exact character values on the complete S5 enumeration. -/
def certificateCharacterTable5 : Fin 120 → ℚ :=
  ![5, 1, 1, -1, -1, 1, 1, 1, -1, -1, -1, -1, -1, -1, 1, -1, 1, -1, -1, -1, -1, 1, -1, 1, 1, 1, 1, 1, 1, 1, -1, 1, -1, 0, 0, -1, -1, 0, -1, -1, 1, 0, 0, -1, -1, -1, 0, 1, -1, 1, -1, 0, 0, -1, 1, 1, -1, -1, -1, -1, 1, 1, -1, 0, 0, 1, 1, 1, 0, -1, 1, 0, -1, 0, -1, -1, 1, 0, -1, -1, 1, -1, 1, -1, -1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 1, -1, 0, -1, -1, -1, 0, 1, -1, -1, -1, 1, -1, 1, 0, -1, 1, 1, 0, 1, 1, 0, 0, 1, -1, 1]

theorem certificateCharacter_perm5 (i : Fin 120) :
    certificateCharacter (certificatePerm5 i) = certificateCharacterTable5 i := by
  fin_cases i <;>
    simp only [certificateCharacter, certificateFixedCount, Fin.sum_univ_succ,
      Fin.sum_univ_zero, Equiv.Perm.mul_apply, certificatePerm5_apply] <;>
    norm_num [certificatePerm5Images, certificateCharacterTable5]

/-- Sum over `S_(k+1)` by the image of register zero and a permutation of the
remaining registers. This is Mathlib's exact permutation equivalence. -/
theorem certificate_sum_perm_succ {M : Type*} [AddCommMonoid M] {k : ℕ}
    (f : Equiv.Perm (Fin (k + 1)) → M) :
    (∑ σ, f σ) = ∑ i : Fin (k + 1), ∑ τ : Equiv.Perm (Fin k),
      f (Equiv.Perm.decomposeFin.symm (i, τ)) := by
  calc
    _ = ∑ p : Fin (k + 1) × Equiv.Perm (Fin k),
        f (Equiv.Perm.decomposeFin.symm p) :=
      Fintype.sum_equiv Equiv.Perm.decomposeFin _ _ (fun σ => by simp)
    _ = _ := Fintype.sum_prod_type _

/-- The rational character sum acting on `k` whole registers. The divisors
are 24 for `[32]` and 12 for `[22]`, as in Appendix B. -/
def certificateCentralAction {k : ℕ} {n : Type*} (denominator : ℚ)
    (f : (Fin k → n) → ℂ) (r : Fin k → n) : ℂ :=
  (denominator : ℂ)⁻¹ * ∑ σ : Equiv.Perm (Fin k),
    (certificateCharacter σ : ℂ) * f (fun i => r (σ i))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
/-- The `[22]` character sum fixes two identical decomposable bivectors. -/
theorem certificateCentralAction_bivec_square {n : Type*} [Fintype n]
    (X : Matrix n (Fin 2) ℂ) (r : Fin 4 → n) :
    certificateCentralAction 12
      (fun s => bivecMat X (s 0) (s 1) * bivecMat X (s 2) (s 3)) r =
      bivecMat X (r 0) (r 1) * bivecMat X (r 2) (r 3) := by
  unfold certificateCentralAction
  rw [certificate_sum_perm4]
  simp only [certificateCharacter_perm4, certificatePerm4_apply]
  norm_num [certificateCharacterTable4, certificatePerm4Images,
    Fin.sum_univ_succ, bivecMat_apply]
  ring

/-- The same `[22]` character sum fixes the two conjugate minors in `z_a`. -/
theorem certificateCentralAction_conj_bivec_square {n : Type*} [Fintype n]
    (X : Matrix n (Fin 2) ℂ) (r : Fin 4 → n) :
    certificateCentralAction 12
      (fun s => star (bivecMat X (s 0) (s 1)) * star (bivecMat X (s 2) (s 3))) r =
      star (bivecMat X (r 0) (r 1)) * star (bivecMat X (r 2) (r 3)) := by
  simpa only [bivecMat_star] using
    certificateCentralAction_bivec_square (fun a b => star (X a b)) r

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
/-- The `[32]` character sum fixes a source column and its two identical
decomposable bivectors. This is Appendix B's holomorphic carrier identity. -/
theorem certificateCentralAction_column_bivec_square {n : Type*} [Fintype n]
    (X : Matrix n (Fin 2) ℂ) (B : Matrix (Fin 2) n ℂ) (q : n) (r : Fin 5 → n) :
    certificateCentralAction 24
      (fun s => (X * B) (s 0) q * bivecMat X (s 1) (s 2) * bivecMat X (s 3) (s 4)) r =
      (X * B) (r 0) q * bivecMat X (r 1) (r 2) * bivecMat X (r 3) (r 4) := by
  unfold certificateCentralAction
  rw [certificate_sum_perm5]
  simp only [certificateCharacter_perm5, certificatePerm5_apply]
  norm_num [certificateCharacterTable5, certificatePerm5Images,
    Fin.sum_univ_succ, Matrix.mul_apply, Fin.sum_univ_two, bivecMat_apply]
  ring

end ThreeCopyQutritWerner
