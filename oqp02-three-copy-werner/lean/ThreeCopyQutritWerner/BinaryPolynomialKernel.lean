module

public import ThreeCopyQutritWerner.BinaryPolynomialProducts
public import ThreeCopyQutritWerner.BinarySymmetricKernel

@[expose] public section


/-!
# Polynomial kernel of the actual finite binary symmetrizer

The operator is a product of the literal one-site symmetric projections.
Each output coordinate is a nonzero positive weight times the corresponding
coefficient of the original replica polynomial. The equivalence includes
all coefficients, including exponents not attained by any pair of words.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

/-- The literal binary one-site projection only depends on total occupation. -/
theorem psym_binary_occupation (a b c d : Fin 2) :
    psym (a, b) (c, d) =
      if a.val + b.val = c.val + d.val then
        (if a = b then 1 else 1 / 2 : ℂ) else 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [psym, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, swapOp]

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Literal tensor product in the original word coordinates. -/
def binaryReplicaSymmetrizer :
    Matrix ((σ → Fin 2) × (σ → Fin 2)) ((σ → Fin 2) × (σ → Fin 2)) ℂ :=
  fun p q => ∏ i, psym (p.1 i, p.2 i) (q.1 i, q.2 i)

def binaryReplicaWeight (a b : σ → Fin 2) : ℂ :=
  ∏ i, if a i = b i then 1 else 1 / 2

theorem binaryReplicaWeight_ne_zero (a b : σ → Fin 2) :
    binaryReplicaWeight a b ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  split_ifs <;> norm_num

/-- A projector entry is the same nonzero weight for every pair of words
with the same exponent sum, and is zero for every other pair. -/
theorem binaryReplicaSymmetrizer_apply (a b c d : σ → Fin 2) :
    binaryReplicaSymmetrizer (a, b) (c, d) =
      if binaryWordExponent a + binaryWordExponent b =
          binaryWordExponent c + binaryWordExponent d
      then binaryReplicaWeight a b else 0 := by
  classical
  by_cases h : binaryWordExponent a + binaryWordExponent b =
      binaryWordExponent c + binaryWordExponent d
  · rw [if_pos h]
    apply Finset.prod_congr rfl
    intro i _
    have hi : (a i).val + (b i).val = (c i).val + (d i).val :=
      congrArg (fun m : σ →₀ ℕ => m i) h
    rw [psym_binary_occupation, if_pos hi]
  · rw [if_neg h]
    have hex : ∃ i, (a i).val + (b i).val ≠ (c i).val + (d i).val := by
      by_contra! hn
      apply h
      ext i
      exact hn i
    obtain ⟨i, hi⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [psym_binary_occupation, if_neg hi]

/-- The actual projected coordinate is precisely a polynomial coefficient
times its nonzero tensor normalization. -/
theorem binaryReplicaSymmetrizer_mulVec
    (K : Matrix (σ → Fin 2) (σ → Fin 2) ℂ) (a b : σ → Fin 2) :
    (binaryReplicaSymmetrizer *ᵥ vec K) (a, b) =
      binaryReplicaWeight a b *
        (binaryReplicaPolynomial K).coeff (binaryWordExponent a + binaryWordExponent b) := by
  classical
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    binaryReplicaSymmetrizer_apply, vec, binaryReplicaPolynomial,
    MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  by_cases h : binaryWordExponent a + binaryWordExponent b =
      binaryWordExponent c + binaryWordExponent d
  · simp [h]
  · simp [h, Ne.symm h]

/-- The full literal tensor projection vanishes exactly when the original
replica polynomial vanishes. No rank or factorization premise is required. -/
theorem binaryReplicaSymmetrizer_kernel_iff
    (K : Matrix (σ → Fin 2) (σ → Fin 2) ℂ) :
    binaryReplicaSymmetrizer *ᵥ vec K = 0 ↔ binaryReplicaPolynomial K = 0 := by
  classical
  constructor
  · intro h
    ext m
    by_cases hm : ∃ a b, binaryWordExponent a + binaryWordExponent b = m
    · obtain ⟨a, b, rfl⟩ := hm
      have he := congrFun h (a, b)
      rw [binaryReplicaSymmetrizer_mulVec] at he
      exact (mul_eq_zero.mp he).resolve_left (binaryReplicaWeight_ne_zero a b)
    · have hn : ∀ a b, binaryWordExponent a + binaryWordExponent b ≠ m := by
        intro a b hab
        exact hm ⟨a, b, hab⟩
      simp [binaryReplicaPolynomial, MvPolynomial.coeff_sum,
        MvPolynomial.coeff_monomial, hn]
  · intro h
    funext p
    rcases p with ⟨a, b⟩
    rw [binaryReplicaSymmetrizer_mulVec, h]
    simp

end ThreeCopyQutritWerner
