module

public import ThreeCopyQutritWerner.SingularValueRank

@[expose] public section


/-!
# Two actual nonzero replica rays at rank two

The original singular family has exactly two positive weights. Conjugates
are absorbed in the right vectors, so the resulting replica factors use
ordinary transpose and retain all original matrix entries.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

/-- Every actual rank-two rectangular matrix is a difference of two replica
rays with all four coefficient vectors nonzero. -/
theorem rank_two_exists_replica_ray_difference
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (X : Matrix m n ℂ) (hX : X.rank = 2) :
    ∃ x z : m → ℂ, ∃ y t : n → ℂ,
      x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ t ≠ 0 ∧
      X = fun i j => x i * y j - z i * t j := by
  classical
  let e : Fin 2 ≃ SingularPositiveIndex X :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, singularPositive_card_eq_rank, hX])
  have hl (k : SingularPositiveIndex X) : singularLeft X k ≠ 0 := by
    intro h
    have he := singularLeft_braket X k k
    simpa [h, braket] using he
  have hr (k : SingularPositiveIndex X) : singularRight X k ≠ 0 := by
    intro h
    have he := singularRight_braket X k k
    simpa [h, braket] using he
  let left (k : Fin 2) : m → ℂ := fun i =>
    (singularWeight X (e k) : ℂ) * singularLeft X (e k) i
  let right (k : Fin 2) : n → ℂ := fun j => conj (singularRight X (e k) j)
  have hleft (k : Fin 2) : left k ≠ 0 := by
    intro h
    apply hl (e k)
    funext i
    have hi := congrFun h i
    exact (mul_eq_zero.mp hi).resolve_left (singularWeight_complex_ne_zero X (e k))
  have hright (k : Fin 2) : right k ≠ 0 := by
    intro h
    apply hr (e k)
    funext j
    have hj := congrArg conj (congrFun h j)
    simpa [right] using hj
  refine ⟨left 0, left 1, right 0, -right 1,
    hleft 0, hright 0, hleft 1, neg_ne_zero.mpr (hright 1), ?_⟩
  ext i j
  calc
    X i j = ∑ k : SingularPositiveIndex X,
        (singularWeight X k : ℂ) * singularLeft X k i * conj (singularRight X k j) :=
      singularFamily_reconstruct X i j
    _ = ∑ k : Fin 2, (singularWeight X (e k) : ℂ) *
        singularLeft X (e k) i * conj (singularRight X (e k) j) :=
      (e.sum_comp _).symm
    _ = left 0 i * right 0 j - left 1 i * (-right 1) j := by
      simp [Fin.sum_univ_two, left, right]

end ThreeCopyQutritWerner
