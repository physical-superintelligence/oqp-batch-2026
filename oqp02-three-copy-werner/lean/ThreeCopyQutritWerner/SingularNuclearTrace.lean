module

public import ThreeCopyQutritWerner.SingularValueFamily
public import ThreeCopyQutritWerner.OrthonormalUnitaryExtension
public import ThreeCopyQutritWerner.NuclearTrace

@[expose] public section


/-!
# Singular-value sum for the literal variational nuclear trace

The supremum over actual square unitary tests equals the sum of the positive
Hermitian-dilation weights. The lower bound constructs a unitary attaining the
sum by extending the proved left/right orthonormal families.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

/-- Adjoint transport in the literal finite coordinate pairing. -/
theorem singular_braket_mulVec {m n : Type*} [Fintype m] [Fintype n]
    (W : Matrix m n ℂ) (v : n → ℂ) (u : m → ℂ) :
    braket (W *ᵥ v) u = braket v (Wᴴ *ᵥ u) := by
  simp only [braket, Matrix.mulVec, dotProduct, map_sum, map_mul,
    Matrix.conjTranspose_apply, Complex.star_def, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Every literal isometry preserves the conjugate-first pairing. -/
theorem singular_braket_isometry {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (W : Matrix m n ℂ) (hW : Wᴴ * W = 1) (u v : n → ℂ) :
    braket (W *ᵥ u) (W *ᵥ v) = braket u v := by
  rw [singular_braket_mulVec, Matrix.mulVec_mulVec, hW, Matrix.one_mulVec]

/-- Cauchy--Schwarz for two normalized coordinate vectors. -/
theorem singular_braket_norm_le_one {n : Type*} [Fintype n] (u v : n → ℂ)
    (hu : braket u u = 1) (hv : braket v v = 1) : ‖braket u v‖ ≤ 1 := by
  have hu' : vecNormSq u = 1 := by
    have h := congrArg Complex.re hu
    simpa only [braket_self, Complex.ofReal_re, Complex.one_re] using h
  have hv' : vecNormSq v = 1 := by
    have h := congrArg Complex.re hv
    simpa only [braket_self, Complex.ofReal_re, Complex.one_re] using h
  have h := normSq_sum_mul_le Finset.univ (fun i => conj (u i)) v
  change Complex.normSq (braket u v) ≤ _ at h
  simp only [Complex.normSq_conj] at h
  change Complex.normSq (braket u v) ≤ vecNormSq u * vecNormSq v at h
  rw [hu', hv', mul_one, Complex.normSq_eq_norm_sq] at h
  have hn := norm_nonneg (braket u v)
  nlinarith

/-- A rank-one trace test is the pairing with the image of its right vector. -/
theorem singular_trace_ketBra {n : Type*} [Fintype n]
    (W : Matrix n n ℂ) (u v : n → ℂ) :
    (Wᴴ * ketBra u v).trace = braket (W *ᵥ v) u := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.star_def, ketBra,
    braket, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Trace tests on an actual finite rank-one expansion. -/
theorem singular_trace_expansion {n k : Type*} [Fintype n] [Fintype k]
    (X W : Matrix n n ℂ) (a : k → ℝ) (u v : k → n → ℂ)
    (hX : ∀ i j, X i j = ∑ l, (a l : ℂ) * u l i * conj (v l j)) :
    (Wᴴ * X).trace = ∑ l, (a l : ℂ) * braket (W *ᵥ v l) (u l) := by
  have heq : X = ∑ l, (a l : ℂ) • ketBra (u l) (v l) := by
    ext i j
    simpa [Matrix.sum_apply, Matrix.smul_apply, ketBra, mul_assoc] using hX i j
  rw [heq]
  simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum,
    Matrix.trace_smul, smul_eq_mul, singular_trace_ketBra]

/-- The variational norm of an actual orthonormal singular expansion. -/
theorem nuclearTrace_eq_sum_of_orthonormal_expansion {n k : Type*}
    [Fintype n] [Fintype k] [DecidableEq n] [DecidableEq k]
    (X : Matrix n n ℂ) (a : k → ℝ) (u v : k → n → ℂ)
    (ha : ∀ j, 0 ≤ a j)
    (hu : ∀ i j, braket (u i) (u j) = if i = j then 1 else 0)
    (hv : ∀ i j, braket (v i) (v j) = if i = j then 1 else 0)
    (hX : ∀ i j, X i j = ∑ l, (a l : ℂ) * u l i * conj (v l j)) :
    nuclearTrace X = ∑ j, a j := by
  apply le_antisymm
  · apply csSup_le (nuclearTraceTests_nonempty X)
    rintro r ⟨W, hW, rfl⟩
    rw [singular_trace_expansion X W a u v hX]
    calc
      ‖∑ j, (a j : ℂ) * braket (W *ᵥ v j) (u j)‖
          ≤ ∑ j, ‖(a j : ℂ) * braket (W *ᵥ v j) (u j)‖ := norm_sum_le _ _
      _ ≤ ∑ j, a j := by
        apply Finset.sum_le_sum
        intro j _
        have hpair := singular_braket_norm_le_one (W *ᵥ v j) (u j)
          (by rw [singular_braket_isometry W hW]; simpa using hv j j)
          (by simpa using hu j j)
        rw [norm_mul, Complex.norm_of_nonneg (ha j)]
        simpa using mul_le_mul_of_nonneg_left hpair (ha j)
  · obtain ⟨W, hW, hmap⟩ := orthonormalFamilies_exists_unitary u v hu hv
    have htrace : (Wᴴ * X).trace = ((∑ j, a j : ℝ) : ℂ) := by
      rw [singular_trace_expansion X W a u v hX]
      simp only [hmap, hu, if_true, mul_one, Complex.ofReal_sum]
    have htest := nuclearTrace_test_le X W hW
    rw [htrace, Complex.norm_of_nonneg (Finset.sum_nonneg fun j _ => ha j)] at htest
    exact htest

/-- No decomposition hypothesis: the nuclear trace equals the sum of the actual
positive eigenvalues of the Hermitian dilation of the given square matrix. -/
theorem nuclearTrace_eq_sum_singularWeight {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) :
    nuclearTrace X = ∑ j : SingularPositiveIndex X, singularWeight X j := by
  classical
  exact nuclearTrace_eq_sum_of_orthonormal_expansion X
    (singularWeight X) (singularLeft X) (singularRight X)
    (fun j => (singularWeight_pos X j).le) (singularLeft_braket X)
    (singularRight_braket X) (singularFamily_reconstruct X)

end ThreeCopyQutritWerner
