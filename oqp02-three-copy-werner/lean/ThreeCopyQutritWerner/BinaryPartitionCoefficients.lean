module

public import ThreeCopyQutritWerner.BinaryPolynomialEncoding

@[expose] public section


/-!
# Literal coefficients across a partition of the binary sites

When two polynomials use disjoint site sets, the coefficient of an original
binary word is the product of their restricted-word coefficients. The proof
isolates the unique possible summand in the polynomial convolution; no tensor
factorization is assumed.
-/

noncomputable section

open scoped BigOperators

namespace ThreeCopyQutritWerner

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Retain the actual bits in I and put zero in the other sites. -/
def binaryPartitionWord (I : Finset σ) (w : σ → Fin 2) : σ → Fin 2 :=
  fun i => if i ∈ I then w i else 0

theorem binaryPartitionWord_exponents_add (I : Finset σ) (w : σ → Fin 2) :
    binaryWordExponent (binaryPartitionWord I w) +
      binaryWordExponent (binaryPartitionWord Iᶜ w) = binaryWordExponent w := by
  ext i
  by_cases hi : i ∈ I <;> simp [binaryPartitionWord, hi]

/-- Disjoint variable dependence makes the original coefficient convolution
have exactly one potentially nonzero term. -/
theorem binaryPartition_product_coeff (I : Finset σ)
    (p r : MvPolynomial σ ℂ)
    (hp : ∀ i, i ∉ I → p.degreeOf i = 0)
    (hr : ∀ i, i ∈ I → r.degreeOf i = 0) (w : σ → Fin 2) :
    (p * r).coeff (binaryWordExponent w) =
      p.coeff (binaryWordExponent (binaryPartitionWord I w)) *
        r.coeff (binaryWordExponent (binaryPartitionWord Iᶜ w)) := by
  classical
  rw [MvPolynomial.coeff_mul]
  apply Finset.sum_eq_single
    (binaryWordExponent (binaryPartitionWord I w),
      binaryWordExponent (binaryPartitionWord Iᶜ w))
  · intro uv huv hne
    by_cases hpu : p.coeff uv.1 = 0
    · simp [hpu]
    by_cases hrv : r.coeff uv.2 = 0
    · simp [hrv]
    exfalso
    apply hne
    have hsum := Finset.mem_antidiagonal.mp huv
    have hpbound (i : σ) : uv.1 i ≤ p.degreeOf i :=
      MvPolynomial.le_degreeOf_of_mem_support i (MvPolynomial.mem_support_iff.mpr hpu)
    have hrbound (i : σ) : uv.2 i ≤ r.degreeOf i :=
      MvPolynomial.le_degreeOf_of_mem_support i (MvPolynomial.mem_support_iff.mpr hrv)
    apply Prod.ext
    · ext i
      have hiadd := congrArg (fun m : σ →₀ ℕ => m i) hsum
      simp only [Finsupp.add_apply, binaryWordExponent_apply] at hiadd
      by_cases hi : i ∈ I
      · have hv : uv.2 i = 0 := Nat.eq_zero_of_le_zero (hr i hi ▸ hrbound i)
        simp [binaryPartitionWord, hi, hv] at hiadd ⊢
        exact hiadd
      · have hu : uv.1 i = 0 := Nat.eq_zero_of_le_zero (hp i hi ▸ hpbound i)
        simp [binaryPartitionWord, hi, hu]
    · ext i
      have hiadd := congrArg (fun m : σ →₀ ℕ => m i) hsum
      simp only [Finsupp.add_apply, binaryWordExponent_apply] at hiadd
      by_cases hi : i ∈ I
      · have hv : uv.2 i = 0 := Nat.eq_zero_of_le_zero (hr i hi ▸ hrbound i)
        simp [binaryPartitionWord, hi, hv]
      · have hu : uv.1 i = 0 := Nat.eq_zero_of_le_zero (hp i hi ▸ hpbound i)
        simp [binaryPartitionWord, hi, hu] at hiadd ⊢
        exact hiadd
  · intro hn
    exact False.elim (hn (Finset.mem_antidiagonal.mpr
      (binaryPartitionWord_exponents_add I w)))

/-- A separated polynomial factorization recovers every original tensor
entry, with the given site placement and without conjugating coefficients. -/
theorem binaryPartition_tensor_entry (I : Finset σ)
    (x : (σ → Fin 2) → ℂ) (p r : MvPolynomial σ ℂ)
    (hp : ∀ i, i ∉ I → p.degreeOf i = 0)
    (hr : ∀ i, i ∈ I → r.degreeOf i = 0)
    (hx : binaryTensorPolynomial x = p * r) (w : σ → Fin 2) :
    x w = p.coeff (binaryWordExponent (binaryPartitionWord I w)) *
      r.coeff (binaryWordExponent (binaryPartitionWord Iᶜ w)) := by
  rw [← binaryTensorPolynomial_coeff x w, hx]
  exact binaryPartition_product_coeff I p r hp hr w

end ThreeCopyQutritWerner
