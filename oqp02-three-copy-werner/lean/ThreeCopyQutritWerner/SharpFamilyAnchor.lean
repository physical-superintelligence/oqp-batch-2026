module

public import ThreeCopyQutritWerner.SharpFamilyRotation
public import ThreeCopyQutritWerner.SingularUnitaryCompletion
public import ThreeCopyQutritWerner.TwoPlane

@[expose] public section


/-!
# Placing an actual rank-two reshape combination in a family slot

A nonzero coefficient vector is normalized by an already proved finite
coordinate construction. The actual orthonormal extension theorem then
provides a coefficient unitary with that normalized vector as a prescribed
column. Reshape rank is preserved by the nonzero normalization scalar.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

/-- Any unit coefficient vector is an actual prescribed column of a unitary. -/
theorem sharpFamily_exists_unitary_column {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ι → ℂ) (hz : braket z z = 1) (i : ι) :
    ∃ W : Matrix ι ι ℂ, Wᴴ * W = 1 ∧ ∀ j, W j i = z j := by
  let e : Fin 1 ↪ ι := ⟨fun _ => i, fun _ _ _ => Subsingleton.elim _ _⟩
  have hg : ∀ a b : Fin 1, braket z z = if a = b then 1 else 0 := by
    intro a b
    rw [if_pos (Subsingleton.elim a b)]
    exact hz
  obtain ⟨W, hW, hc⟩ := orthonormalFamily_exists_unitary_columns e (fun _ => z) hg
  exact ⟨W, hW, fun j => hc 0 j⟩

/-- A prescribed coefficient column rotates the family to that exact common
linear combination, including every original complex coefficient. -/
theorem sharpRotateFamily_eq_combination_of_column
    {ι n : Type*} [Fintype ι] (W : Matrix ι ι ℂ) (u : ι → n → ℂ)
    (z : ι → ℂ) (i : ι) (hc : ∀ j, W j i = z j) :
    sharpRotateFamily W u i = fun r => ∑ j, z j * u j r := by
  funext r
  simp only [sharpRotateFamily, sharpFamilyMatrix, Matrix.mul_apply, hc, mul_comm]

/-- If an actual coefficient combination has reshape rank two, a constructed
unitary mixing places a rank-two reshape in any prescribed family slot.
No normalized combination or supplied unitary is an extra premise. -/
theorem sharpFamily_exists_rank_two_anchor
    {ι L R : Type*} [Fintype ι] [Fintype L] [Fintype R] [DecidableEq ι]
    (u : ι → L × R → ℂ) (z : ι → ℂ)
    (hr : (sharpReshape (fun r => ∑ j, z j * u j r)).rank = 2) (i : ι) :
    ∃ W : Matrix ι ι ℂ, Wᴴ * W = 1 ∧
      (sharpReshape (sharpRotateFamily W u i)).rank = 2 := by
  classical
  have hz : ∃ j, z j ≠ 0 := by
    by_contra h
    push_neg at h
    have he : sharpReshape (fun r => ∑ j, z j * u j r) = 0 := by
      ext a b
      simp [sharpReshape, h]
    rw [he, Matrix.rank_zero] at hr
    omega
  obtain ⟨w, t, hw, hzw⟩ := TwoPlane.exists_unit_factor z hz
  have ht : t ≠ 0 := by
    intro ht
    obtain ⟨j, hj⟩ := hz
    exact hj (by rw [hzw j, ht, zero_mul])
  have he : sharpReshape (fun r => ∑ j, z j * u j r) =
      t • sharpReshape (fun r => ∑ j, w j * u j r) := by
    ext a b
    simp only [sharpReshape, Matrix.smul_apply, smul_eq_mul, hzw, mul_assoc,
      Finset.mul_sum]
  rw [he, Matrix.rank_smul_of_mem_nonZeroDivisors _
    (mem_nonZeroDivisors_iff_ne_zero.mpr ht)] at hr
  have hww : braket w w = 1 := by rw [braket_self, hw, Complex.ofReal_one]
  obtain ⟨W, hW, hc⟩ := sharpFamily_exists_unitary_column w hww i
  refine ⟨W, hW, ?_⟩
  rw [sharpRotateFamily_eq_combination_of_column W u w i hc]
  exact hr

end ThreeCopyQutritWerner
