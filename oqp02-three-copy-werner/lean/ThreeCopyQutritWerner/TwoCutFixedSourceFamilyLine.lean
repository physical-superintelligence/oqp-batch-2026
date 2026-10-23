module

public import ThreeCopyQutritWerner.TwoCutFixedSourceLine

@[expose] public section


/-!
# Scalar-line rigidity for an actual fixed-source family

Zero members are included. Every nonzero member has rank two by the cut
inequality, so source inclusion becomes equality with the nonzero anchor.
The anchor's local factor exceptions remain explicit.
-/

noncomputable section

namespace ThreeCopyQutritWerner

theorem twoCut_fixed_source_family_eq_smul
    {ι : Type*} (F : ι → Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) (i₀ : ι)
    (hr : ∀ i, (F i).rank ≤ 2) (hq : ∀ i, cutForm (F i) = 0) (hne : F i₀ ≠ 0)
    (hR : ∀ i, LinearMap.range (F i).mulVecLin ≤ LinearMap.range (F i₀).mulVecLin)
    (a b : Fin 3) (hrow : ∀ i j q, i = a ∨ j = b → F i₀ (i, j) q = 0)
    (hfirst : ¬ HasSingleFirstOutput (F i₀))
    (hsecond : ¬ HasSingleFirstOutput (twoCutSwap (F i₀))) :
    ∀ i, ∃ z : ℂ, F i = z • F i₀ := by
  have hr₀ := rank_two_of_nonzero_cutForm_zero (F i₀) (hr i₀) (hq i₀) hne
  intro i
  by_cases hi : F i = 0
  · exact ⟨0, by simpa only [zero_smul] using hi⟩
  have hri := rank_two_of_nonzero_cutForm_zero (F i) (hr i) (hq i) hi
  have he : LinearMap.range (F i).mulVecLin = LinearMap.range (F i₀).mulVecLin := by
    apply Submodule.eq_of_le_of_finrank_le (hR i)
    change (F i₀).rank ≤ (F i).rank
    omega
  exact twoCut_fixed_source_eq_smul (F i₀) (F i) (hr i₀) (hq i₀) (hr i) (hq i)
    he.symm a b hrow hfirst hsecond

end ThreeCopyQutritWerner
