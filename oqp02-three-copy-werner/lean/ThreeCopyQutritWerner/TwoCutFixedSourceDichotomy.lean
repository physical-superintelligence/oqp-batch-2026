module

public import ThreeCopyQutritWerner.FirstSiteFactorLocalAction
public import ThreeCopyQutritWerner.TwoCutFixedSourceFamilyLine
public import ThreeCopyQutritWerner.TwoCutFixedSourceFactorRank
public import ThreeCopyQutritWerner.TwoCutZeroPlanes

@[expose] public section


/-!
# The actual fixed-source partner dichotomy in original coordinates

One nonzero cut-zero member constructs the local anchor planes. The three
branches are then transported back to the original rectangular partners:
a scalar family, or pointwise local rank one at either physical site.
No coordinate plane or fixed partner direction is an input hypothesis.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace ThreeCopyQutritWerner

theorem twoCut_fixed_source_partner_dichotomy
    {ι : Type*} (Z : Matrix (Fin 3 × Fin 3) (Fin 2) ℂ)
    (F : ι → Matrix (Fin 3 × Fin 3) (Fin 2) ℂ) (hZ : Z.rank = 2)
    (hq : ∀ i, cutForm (Z * (F i)ᴴ) = 0) (i₀ : ι) (hne : Z * (F i₀)ᴴ ≠ 0) :
    (∀ i, ∃ z : ℂ, F i = z • F i₀) ∨
      (∀ i, (twoSiteFactorFlatten (F i)).rank ≤ 1) ∨
      (∀ i, (twoSiteFactorFlatten (twoSiteFactorFlip (F i))).rank ≤ 1) := by
  classical
  have hr₀ : (Z * (F i₀)ᴴ).rank ≤ 2 := (Matrix.rank_mul_le_left _ _).trans hZ.le
  obtain ⟨U, V, a, b, hU, hV, hplane⟩ :=
    cutForm_zero_exists_output_planes (Z * (F i₀)ᴴ) hr₀ (hq i₀)
  let W := U ⊗ₖ V
  let Z' := W * Z
  let F' : ι → Matrix (Fin 3 × Fin 3) (Fin 2) ℂ := fun i => W * F i
  let A : ι → Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ := fun i => Z' * (F' i)ᴴ
  have hW : Wᴴ * W = 1 := kron_isometry U V hU hV
  have hZ' : Z'.rank = 2 := (factor_rank_left_isometry W Z hW).trans hZ
  have he (i : ι) : A i = W * (Z * (F i)ᴴ) * Wᴴ := by
    simp only [A, Z', F', Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hr (i : ι) : (A i).rank ≤ 2 := (Matrix.rank_mul_le_left _ _).trans hZ'.le
  have hq' (i : ι) : cutForm (A i) = 0 := by
    rw [he i]
    exact (cutForm_local_conj U V hU hV (Z * (F i)ᴴ)).trans (hq i)
  have hn : A i₀ ≠ 0 := by
    intro hz
    apply hne
    have hrec := twoCut_unitary_conj_recover W (Z * (F i₀)ᴴ) hW
    rw [← he i₀, hz, Matrix.mul_zero, Matrix.zero_mul] at hrec
    exact hrec.symm
  have hlocal (i j : Fin 3) (q : Fin 3 × Fin 3) (hij : i = a ∨ j = b) :
      A i₀ (i, j) q = 0 := by
    rw [he i₀, Matrix.mul_apply]
    simp only [show ∀ p, (W * (Z * (F i₀)ᴴ)) (i, j) p = 0 from
      fun p => hplane i j p hij, zero_mul, Finset.sum_const_zero]
  by_cases hf : HasSingleFirstOutput (A i₀)
  · have hs := twoCut_fixed_source_single_factor_partner_ranks Z' F' hZ' hq' i₀ hn hf
    refine Or.inr (Or.inl ?_)
    intro i
    simpa only [F', W, twoSiteFactorFlatten_local_unitary_rank U V (F i) hU hV] using hs i
  by_cases hs : HasSingleFirstOutput (twoCutSwap (A i₀))
  · have ht := twoCut_fixed_source_second_factor_partner_ranks Z' F' hZ' hq' i₀ hn hs
    refine Or.inr (Or.inr ?_)
    intro i
    simpa only [F', W, twoSiteFactorFlip_local_mul,
      twoSiteFactorFlatten_local_unitary_rank V U (twoSiteFactorFlip (F i)) hV hU] using ht i
  have hAr : (A i₀).rank = 2 := rank_two_of_nonzero_cutForm_zero _ (hr i₀) (hq' i₀) hn
  have hR₀ : LinearMap.range (A i₀).mulVecLin = LinearMap.range Z'.mulVecLin :=
    matrix_range_mul_eq_of_rank_eq Z' (F' i₀)ᴴ (hAr.trans hZ'.symm)
  have hR (i : ι) : LinearMap.range (A i).mulVecLin ≤ LinearMap.range (A i₀).mulVecLin := by
    rw [hR₀]
    rintro _ ⟨v, rfl⟩
    refine ⟨(F' i)ᴴ *ᵥ v, ?_⟩
    change Z' *ᵥ ((F' i)ᴴ *ᵥ v) = (Z' * (F' i)ᴴ) *ᵥ v
    exact Matrix.mulVec_mulVec v Z' (F' i)ᴴ
  have hline := twoCut_fixed_source_family_eq_smul A i₀ hr hq' hn hR a b hlocal hf hs
  obtain ⟨L, hL⟩ := exists_left_inverse_of_rank_eq_two Z' hZ'
  refine Or.inl ?_
  intro i
  obtain ⟨z, hz⟩ := hline i
  have hAdj : (F' i)ᴴ = z • (F' i₀)ᴴ := by
    have ht := congrArg (fun T => L * T) hz
    simpa only [A, Matrix.mul_smul, ← Matrix.mul_assoc, hL, Matrix.one_mul] using ht
  have hF : F' i = star z • F' i₀ := by
    simpa only [Matrix.conjTranspose_smul, Matrix.conjTranspose_conjTranspose] using
      congrArg Matrix.conjTranspose hAdj
  refine ⟨star z, ?_⟩
  have ht := congrArg (fun T => Wᴴ * T) hF
  simpa only [F', Matrix.mul_smul, ← Matrix.mul_assoc, hW, Matrix.one_mul] using ht

end ThreeCopyQutritWerner
