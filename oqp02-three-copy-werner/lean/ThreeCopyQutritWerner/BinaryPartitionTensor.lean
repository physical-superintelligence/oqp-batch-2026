module

public import ThreeCopyQutritWerner.BinaryPartitionCoefficients
public import ThreeCopyQutritWerner.BinaryZeroPolynomialFactors

@[expose] public section


/-!
# The actual separated tensor of a binary endpoint zero

The factor vectors are indexed by the two complementary sets of physical
sites. The original spin-transformed matrix entries are a rank-one tensor
on the first set times a skew two-ray tensor on the second set. No site
permutation, complex conjugation, or normalization is suppressed.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Extend a word on a set of sites by zero at the other sites. -/
def binaryPartitionExtend (I : Finset σ) (w : I → Fin 2) : σ → Fin 2 :=
  fun i => if hi : i ∈ I then w ⟨i, hi⟩ else 0

/-- Coefficients on exactly the retained physical sites. -/
def binaryPartitionTensor (I : Finset σ) (p : MvPolynomial σ ℂ) :
    (I → Fin 2) → ℂ :=
  fun w => p.coeff (binaryWordExponent (binaryPartitionExtend I w))

theorem binaryPartitionExtend_restrict (I : Finset σ) (w : σ → Fin 2) :
    binaryPartitionExtend I (fun i : I => w i) = binaryPartitionWord I w := by
  funext i
  by_cases hi : i ∈ I <;> simp [binaryPartitionExtend, binaryPartitionWord, hi]

/-- The partition tensor in the unchanged, full computational-word coordinates. -/
def binaryPartitionMatrix (I : Finset σ)
    (p q : (I → Fin 2) → ℂ) (r s : (↥(Iᶜ) → Fin 2) → ℂ) :
    Matrix (σ → Fin 2) (σ → Fin 2) ℂ := fun a b =>
  p (fun i : I => a i) * q (fun i : I => b i) *
    (r (fun i : ↥(Iᶜ) => a i) * s (fun i : ↥(Iᶜ) => b i) -
      s (fun i : ↥(Iᶜ) => a i) * r (fun i : ↥(Iᶜ) => b i))

/-- All four separated polynomial factors assemble into the literal tensor
partition matrix, rather than only an isomorphic abstract tensor. -/
theorem binaryPartition_factor_grid_matrix (I : Finset σ)
    (x y z t : (σ → Fin 2) → ℂ) (p q r s : MvPolynomial σ ℂ)
    (hp : ∀ i, i ∉ I → p.degreeOf i = 0)
    (hq : ∀ i, i ∉ I → q.degreeOf i = 0)
    (hr : ∀ i, i ∈ I → r.degreeOf i = 0)
    (hs : ∀ i, i ∈ I → s.degreeOf i = 0)
    (hx : binaryTensorPolynomial x = p * r)
    (hy : binaryTensorPolynomial y = q * s)
    (hz : binaryTensorPolynomial z = p * s)
    (ht : binaryTensorPolynomial t = q * r) :
    (fun a b => x a * y b - z a * t b) =
      binaryPartitionMatrix I (binaryPartitionTensor I p) (binaryPartitionTensor I q)
        (binaryPartitionTensor Iᶜ r) (binaryPartitionTensor Iᶜ s) := by
  funext a b
  rw [binaryPartition_tensor_entry I x p r hp hr hx a,
    binaryPartition_tensor_entry I y q s hq hs hy b,
    binaryPartition_tensor_entry I z p s hp hs hz a,
    binaryPartition_tensor_entry I t q r hq hr ht b]
  simp only [binaryPartitionMatrix, binaryPartitionTensor, binaryPartitionExtend_restrict]
  ring

/-- The site partition and all its coefficient tensors are derived from each
original nonzero binary endpoint zero. -/
theorem binary_endpoint_zero_exists_partition_tensor
    (C : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ)
    (hC : C.rank ≤ 2) (hz : endpointEnergy C = 0) (hne : C ≠ 0) :
    ∃ I : Finset (Fin 3), ∃ p q : (I → Fin 2) → ℂ,
      ∃ r s : (↥(Iᶜ) → Fin 2) → ℂ,
        binaryThreeWordMatrix (C * epsJ₃ᵀ) = binaryPartitionMatrix I p q r s := by
  classical
  obtain ⟨x, y, z, t, p, q, r, s, hx, hy, hzz, ht, hrep,
    hp, hq, hr, hs, hxp, hyp, hzp, htp, hsep⟩ :=
    binary_endpoint_zero_exists_separated_polynomial_factors C hC hz hne
  let I : Finset (Fin 3) := Finset.univ.filter
    (fun i => ¬ (p.degreeOf i = 0 ∧ q.degreeOf i = 0))
  have hpi (i : Fin 3) (hi : i ∉ I) : p.degreeOf i = 0 := by
    have he : p.degreeOf i = 0 ∧ q.degreeOf i = 0 := by simpa [I] using hi
    exact he.1
  have hqi (i : Fin 3) (hi : i ∉ I) : q.degreeOf i = 0 := by
    have he : p.degreeOf i = 0 ∧ q.degreeOf i = 0 := by simpa [I] using hi
    exact he.2
  have hrs (i : Fin 3) (hi : i ∈ I) : r.degreeOf i = 0 ∧ s.degreeOf i = 0 := by
    have hnot : ¬ (p.degreeOf i = 0 ∧ q.degreeOf i = 0) := by simpa [I] using hi
    exact (hsep i).resolve_left hnot
  refine ⟨I, binaryPartitionTensor I p, binaryPartitionTensor I q,
    binaryPartitionTensor Iᶜ r, binaryPartitionTensor Iᶜ s, ?_⟩
  rw [hrep]
  exact binaryPartition_factor_grid_matrix I x y z t p q r s
    hpi hqi (fun i hi => (hrs i hi).1) (fun i hi => (hrs i hi).2)
    hxp hyp hzp htp

end ThreeCopyQutritWerner
