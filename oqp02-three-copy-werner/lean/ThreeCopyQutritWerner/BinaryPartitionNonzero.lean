module

public import ThreeCopyQutritWerner.BinaryPartitionTensor

@[expose] public section


/-!
# Proper partitions and nonzero factors for original binary zeros

The exact rank of the original spin transform excludes a vanishing tensor
factor and the partition containing every site. Thus exactly the cardinality
branches zero, one, and two remain, with no nondegeneracy assumption added to
the original endpoint zero.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem binaryPartitionMatrix_ne_zero_factors (I : Finset σ)
    (p q : (I → Fin 2) → ℂ) (r s : (↥(Iᶜ) → Fin 2) → ℂ)
    (hne : binaryPartitionMatrix I p q r s ≠ 0) :
    p ≠ 0 ∧ q ≠ 0 ∧ r ≠ 0 ∧ s ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> apply hne <;>
    ext a b <;> simp [binaryPartitionMatrix, h]

/-- The skew factor itself is nonzero, not merely its two vectors. -/
theorem binaryPartitionMatrix_ne_zero_skew (I : Finset σ)
    (p q : (I → Fin 2) → ℂ) (r s : (↥(Iᶜ) → Fin 2) → ℂ)
    (hne : binaryPartitionMatrix I p q r s ≠ 0) :
    (fun a b => r a * s b - s a * r b) ≠
      (0 : Matrix (↥(Iᶜ) → Fin 2) (↥(Iᶜ) → Fin 2) ℂ) := by
  intro h
  apply hne
  ext a b
  have he := congrFun (congrFun h (fun i : ↥(Iᶜ) => a i)) (fun i : ↥(Iᶜ) => b i)
  change r (fun i : ↥(Iᶜ) => a i) * s (fun i : ↥(Iᶜ) => b i) -
    s (fun i : ↥(Iᶜ) => a i) * r (fun i : ↥(Iᶜ) => b i) = 0 at he
  simp [binaryPartitionMatrix, he]

/-- With no site on the skew side, its scalar skew form is identically zero. -/
theorem binaryPartitionMatrix_univ_eq_zero
    (p q : (↥(Finset.univ : Finset σ) → Fin 2) → ℂ)
    (r s : (↥((Finset.univ : Finset σ)ᶜ) → Fin 2) → ℂ) :
    binaryPartitionMatrix Finset.univ p q r s = 0 := by
  ext a b
  have he : (fun i : ↥((Finset.univ : Finset σ)ᶜ) => a i) =
      (fun i : ↥((Finset.univ : Finset σ)ᶜ) => b i) := by
    funext i
    exact False.elim (by simpa using i.property)
  simp [binaryPartitionMatrix, he, mul_comm]

/-- Every actual nonzero binary endpoint zero has a proper partition with
all four tensor factors nonzero and a nonzero skew factor. -/
theorem binary_endpoint_zero_exists_proper_partition_tensor
    (C : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ)
    (hC : C.rank ≤ 2) (hz : endpointEnergy C = 0) (hne : C ≠ 0) :
    ∃ I : Finset (Fin 3), ∃ p q : (I → Fin 2) → ℂ,
      ∃ r s : (↥(Iᶜ) → Fin 2) → ℂ,
        (I.card = 0 ∨ I.card = 1 ∨ I.card = 2) ∧
        p ≠ 0 ∧ q ≠ 0 ∧ r ≠ 0 ∧ s ≠ 0 ∧
        (fun a b => r a * s b - s a * r b) ≠
          (0 : Matrix (↥(Iᶜ) → Fin 2) (↥(Iᶜ) → Fin 2) ℂ) ∧
        binaryThreeWordMatrix (C * epsJ₃ᵀ) = binaryPartitionMatrix I p q r s := by
  classical
  obtain ⟨I, p, q, r, s, he⟩ :=
    binary_endpoint_zero_exists_partition_tensor C hC hz hne
  have hrank : (binaryPartitionMatrix I p q r s).rank = 2 := by
    rw [← he, binaryThree_spin_word_rank]
    exact rank_eq_two_of_endpointEnergy_eq_zero C hC hz hne
  have hK : binaryPartitionMatrix I p q r s ≠ 0 := by
    intro h
    rw [h, Matrix.rank_zero] at hrank
    norm_num at hrank
  have hI : I ≠ Finset.univ := by
    intro h
    subst I
    exact hK (binaryPartitionMatrix_univ_eq_zero p q r s)
  have hcard : I.card < 3 := by
    have hlt := Finset.card_lt_card
      ((Finset.ssubset_iff_subset_ne).mpr ⟨Finset.subset_univ I, hI⟩)
    simpa using hlt
  obtain ⟨hp, hq, hr, hs⟩ := binaryPartitionMatrix_ne_zero_factors I p q r s hK
  exact ⟨I, p, q, r, s, by omega, hp, hq, hr, hs,
    binaryPartitionMatrix_ne_zero_skew I p q r s hK, he⟩

end ThreeCopyQutritWerner
