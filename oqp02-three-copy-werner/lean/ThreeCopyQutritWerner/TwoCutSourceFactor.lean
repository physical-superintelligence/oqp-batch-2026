module

public import ThreeCopyQutritWerner.TwoCutOutputCollapse

@[expose] public section


/-!
# Transporting an actual one-site source factor

A fixed physical output ray is a property of the original column range.
It therefore transports between blocks with the same source. Combined with
the proved cut-zero alternative, failure of input alignment forces the
same one-site source factor on the anchor itself.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

/-- Actual range inclusion transports every literal first-site output factor. -/
theorem firstSite_output_factor_of_range_le
    {a d m n : Type*} [Fintype a] [Fintype d] [Fintype m] [Fintype n]
    [DecidableEq m]
    (A : Matrix (a × d) m ℂ) (B : Matrix (a × d) n ℂ)
    (hR : LinearMap.range A.mulVecLin ≤ LinearMap.range B.mulVecLin)
    (i₀ : a) (x : a → ℂ)
    (hB : ∀ i r q, B (i, r) q = x i * B (i₀, r) q) :
    ∀ i r q, A (i, r) q = x i * A (i₀, r) q := by
  intro i r q
  have hcol : (fun p => A p q) ∈ LinearMap.range A.mulVecLin := by
    refine ⟨Pi.single q 1, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply']
  obtain ⟨v, hv⟩ := hR hcol
  have he (p : a × d) : (∑ j, B p j * v j) = A p q := by
    exact congrFun hv p
  calc
    A (i, r) q = ∑ j, B (i, r) j * v j := (he (i, r)).symm
    _ = x i * ∑ j, B (i₀, r) j * v j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [hB i r j]
      ring
    _ = x i * A (i₀, r) q := by rw [he]

/-- If an actual cut-zero block fails to align its missing output coordinate
on input, every anchor with range in that block has a single local output
factor. No fixed-factor premise is imposed on the original anchor. -/
theorem cutForm_zero_fixed_source_alignment_or_factor
    {a d : Type*} [Fintype a] [Fintype d] [DecidableEq a] [DecidableEq d]
    (A B : Matrix (a × d) (a × d) ℂ) (hB : B.rank ≤ 2) (hq : cutForm B = 0)
    (hR : LinearMap.range A.mulVecLin ≤ LinearMap.range B.mulVecLin)
    (k : a) (hrow : ∀ r q, B (k, r) q = 0) :
    (∀ p r, B p (k, r) = 0) ∨
      ∃ (i₀ : a) (x : a → ℂ), x i₀ = 1 ∧
        ∀ i r q, A (i, r) q = x i * A (i₀, r) q := by
  rcases cutForm_zero_missing_row_alignment_or_single_output B hB hq k hrow with h | h
  · exact Or.inl h
  · obtain ⟨i₀, x, hx, hf⟩ := h
    exact Or.inr ⟨i₀, x, hx, firstSite_output_factor_of_range_le A B hR i₀ x hf⟩

end ThreeCopyQutritWerner
