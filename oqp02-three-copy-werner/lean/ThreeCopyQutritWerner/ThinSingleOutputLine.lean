module

public import ThreeCopyQutritWerner.ThinSingleOutputRange
public import ThreeCopyQutritWerner.TwoCutFixedSourceLine
public import ThreeCopyQutritWerner.TwoCutTraceZeroNormal

@[expose] public section


/-!
# The nondegenerate source branch of a single-output endpoint zero

All nonzero original blocks share the anchor's actual rank-two range.
Outside the anchor's two single-local-output branches the fixed-source
line theorem makes every block a scalar multiple of that anchor. This is
a literal first-site ket-bra tensor, hence normalized family II.
-/

noncomputable section

open scoped Matrix Kronecker ComplexConjugate

namespace ThreeCopyQutritWerner

/-- The entire original single-output matrix factors through its actual
anchor block. Zero blocks remain included in the coefficient vector. -/
theorem endpoint_zero_single_output_nondegenerate_source_tensor
    (C : Matrix QutritSites QutritSites ℂ) (hC : C.rank ≤ 2)
    (hz : endpointEnergy C = 0) (k j₀ : Fin 3)
    (hrow : ∀ i, i ≠ k → ∀ r q, C (i, r) q = 0)
    (hne : firstSiteBlock C k j₀ ≠ 0) (a b : Fin 3)
    (hanchor : ∀ i j q, i = a ∨ j = b → firstSiteBlock C k j₀ (i, j) q = 0)
    (hfirst : ¬ HasSingleFirstOutput (firstSiteBlock C k j₀))
    (hsecond : ¬ HasSingleFirstOutput (twoCutSwap (firstSiteBlock C k j₀))) :
    ∃ v : Fin 3 → ℂ,
      C = ketBra (fun i => if i = k then 1 else 0) v ⊗ₖ firstSiteBlock C k j₀ := by
  have hq := firstSiteBlock_cutForm_zero_of_single_output_endpoint_zero C hC hz k hrow
  have hr (j : Fin 3) : (firstSiteBlock C k j).rank ≤ 2 :=
    (firstSiteBlock_rank_le C k j).trans hC
  have hall (j : Fin 3) : ∃ z : ℂ, firstSiteBlock C k j = z • firstSiteBlock C k j₀ := by
    by_cases hj : firstSiteBlock C k j = 0
    · exact ⟨0, by simp [hj]⟩
    have hR := (single_output_nonzero_blocks_same_range C hC hz k hrow j₀ j hne hj).2.2
    exact twoCut_fixed_source_eq_smul _ _ (hr j₀) (hq j₀) (hr j) (hq j)
      hR a b hanchor hfirst hsecond
  choose z hz' using hall
  refine ⟨fun j => conj (z j), ?_⟩
  ext ⟨i, r⟩ ⟨j, s⟩
  by_cases hi : i = k
  · subst i
    simpa only [firstSiteBlock, Matrix.submatrix_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.kroneckerMap_apply, ketBra, if_true, one_mul,
      Complex.conj_conj] using congrFun (congrFun (hz' j) r) s
  · simp [Matrix.kroneckerMap_apply, ketBra, hi, hrow i hi]

/-- The original normalized endpoint zero in this branch is a member of
the exact family union, with no carrier or input factor supplied. -/
theorem isQutritZeroFamilyMember_of_single_output_nondegenerate_source
    (C : Matrix QutritSites QutritSites ℂ) (hC : C.rank ≤ 2)
    (hz : endpointEnergy C = 0) (hN : frobSq C = 1) (k j₀ : Fin 3)
    (hrow : ∀ i, i ≠ k → ∀ r q, C (i, r) q = 0)
    (hne : firstSiteBlock C k j₀ ≠ 0) (a b : Fin 3)
    (hanchor : ∀ i j q, i = a ∨ j = b → firstSiteBlock C k j₀ (i, j) q = 0)
    (hfirst : ¬ HasSingleFirstOutput (firstSiteBlock C k j₀))
    (hsecond : ¬ HasSingleFirstOutput (twoCutSwap (firstSiteBlock C k j₀))) :
    IsQutritZeroFamilyMember C := by
  obtain ⟨v, he⟩ := endpoint_zero_single_output_nondegenerate_source_tensor
    C hC hz k j₀ hrow hne a b hanchor hfirst hsecond
  have hq := firstSiteBlock_cutForm_zero_of_single_output_endpoint_zero C hC hz k hrow j₀
  have ht := cutForm_zero_fixed_source_trace_zero (firstSiteBlock C k j₀)
    (firstSiteBlock C k j₀) ((firstSiteBlock_rank_le C k j₀).trans hC)
    hq le_rfl hfirst hsecond
  exact isQutritZeroFamilyMember_of_trace_zero_cut_tensor C hC hN _ v _ he hq ht

end ThreeCopyQutritWerner
