module

public import ThreeCopyQutritWerner.ThinFirstSiteSix
public import ThreeCopyQutritWerner.QutritThinInputReduction

@[expose] public section


/-!
# Unconditional endpoint positivity on an actual thin local output range

Coordinate reindexing transports the six-ray identity to any missing row.
The original local range rank then constructs such coordinates. No input
support or full three-copy endpoint inequality is assumed.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

/-- Reindex only the first physical register in both the output and input. -/
theorem endpointEnergy_firstSite_reindex
    {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (C : Matrix (a × b × c) (a × b × c) ℂ) (σ : Equiv.Perm a) :
    endpointEnergy (C.submatrix (Equiv.prodCongr σ (Equiv.refl (b × c)))
      (Equiv.prodCongr σ (Equiv.refl (b × c)))) = endpointEnergy C := by
  let e := Equiv.prodCongr σ (Equiv.refl (b × c))
  have hb (i j : a) : firstSiteBlock (C.submatrix e e) i j =
      firstSiteBlock C (σ i) (σ j) := rfl
  have ht : ptrace₁ (C.submatrix e e) = ptrace₁ C := by
    ext r s
    exact Equiv.sum_comp σ (fun i => C (i, r) (i, s))
  change endpointEnergy (C.submatrix e e) = endpointEnergy C
  rw [endpointEnergy_eq_sum_firstSiteBlock_cutForm,
    endpointEnergy_eq_sum_firstSiteBlock_cutForm, ht]
  congr 1
  simp only [hb]
  calc
    _ = ∑ i, ∑ j, cutForm (firstSiteBlock C (σ i) j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Equiv.sum_comp σ (fun j => cutForm (firstSiteBlock C (σ i) j))
    _ = _ := Equiv.sum_comp σ (fun i => ∑ j, cutForm (firstSiteBlock C i j))

/-- Any actual missing first-site output coordinate suffices for positivity. -/
theorem endpointEnergy_nonneg_of_missing_first_row
    {b c : Type*} [Fintype b] [Fintype c] [DecidableEq b] [DecidableEq c]
    (C : Matrix (Fin 3 × b × c) (Fin 3 × b × c) ℂ) (hC : C.rank ≤ 2)
    (k : Fin 3) (hrow : ∀ r q, C (k, r) q = 0) :
    0 ≤ endpointEnergy C := by
  let σ : Equiv.Perm (Fin 3) := Equiv.swap 2 k
  let e := Equiv.prodCongr σ (Equiv.refl (b × c))
  have hD : (C.submatrix e e).rank ≤ 2 := (Matrix.rank_submatrix_le C e e).trans hC
  have hr (r : b × c) (q : Fin 3 × b × c) : C.submatrix e e (2, r) q = 0 := by
    simpa [e, σ] using hrow r (e q)
  have hp := endpointEnergy_nonneg_of_missing_first_row_two (C.submatrix e e) hD hr
  rwa [endpointEnergy_firstSite_reindex C σ] at hp

/-- The manuscript's literal local range dimension gives unconditional
positivity, without any assumption on the input local range. -/
theorem endpointEnergy_nonneg_of_thin_first_localRange
    (C : Matrix QutritSites QutritSites ℂ) (hC : C.rank ≤ 2)
    (hthin : localRangeDim₁ C ≤ 2) : 0 ≤ endpointEnergy C := by
  obtain ⟨U, k, hU, hrow, hr, he, _⟩ :=
    qutrit_thin_first_exists_unitary_missing_row C hthin
  have hp := endpointEnergy_nonneg_of_missing_first_row (embed₃ U 1 1 C)
    (hr.trans_le hC) k hrow
  rwa [he] at hp

end ThreeCopyQutritWerner
