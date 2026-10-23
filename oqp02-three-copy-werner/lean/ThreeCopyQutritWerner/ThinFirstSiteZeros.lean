module

public import ThreeCopyQutritWerner.ThinFirstSitePositivity

@[expose] public section


/-!
# Unconditional input-split zero inheritance at a thin output

The input complement has the same missing output row and inherited rank.
The proved thin-site positivity therefore removes the full endpoint premise
from these consequences. All blocks refer to the original transformed C.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

variable {b c : Type*} [Fintype b] [Fintype c] [DecidableEq b] [DecidableEq c]

/-- Both actual input restrictions are zeros, without an endpoint premise. -/
theorem endpointEnergy_thin_first_inputSplit_zero
    (C : Matrix (Fin 3 × b × c) (Fin 3 × b × c) ℂ) (hC : C.rank ≤ 2)
    (hz : endpointEnergy C = 0) (k : Fin 3) (hrow : ∀ r q, C (k, r) q = 0) :
    endpointEnergy (firstSiteInputKeep C k) = 0 ∧
      endpointEnergy (firstSiteInputDrop C k) = 0 := by
  have hk := endpointEnergy_firstSiteInputKeep_nonneg C hC k hrow
  have hdrow (r : b × c) (q : Fin 3 × b × c) :
      firstSiteInputDrop C k (k, r) q = 0 := by
    simp [firstSiteInputDrop, hrow]
  have hd := endpointEnergy_nonneg_of_missing_first_row (firstSiteInputDrop C k)
    ((firstSiteInputSplit_rank_le C k).2.trans hC) k hdrow
  have he := endpointEnergy_firstSiteInputSplit C k hrow
  constructor <;> linarith

/-- Each literal off-plane input block is an actual two-site cut zero. -/
theorem firstSiteBlock_cutForm_zero_of_thin_endpoint_zero
    (C : Matrix (Fin 3 × b × c) (Fin 3 × b × c) ℂ) (hC : C.rank ≤ 2)
    (hz : endpointEnergy C = 0) (k : Fin 3) (hrow : ∀ r q, C (k, r) q = 0)
    (i : Fin 3) : cutForm (firstSiteBlock C i k) = 0 := by
  have hs := (endpointEnergy_thin_first_inputSplit_zero C hC hz k hrow).1
  rw [endpointEnergy_firstSiteInputKeep_eq_sum C k hrow] at hs
  exact congrFun ((Fintype.sum_eq_zero_iff_of_nonneg
    (fun j => firstSiteBlock_cutForm_nonneg C hC j k)).mp hs) i

/-- All six original binary ray contractions vanish individually. -/
theorem endpointEnergy_missing_first_row_two_six_zeros
    (C : Matrix (Fin 3 × b × c) (Fin 3 × b × c) ℂ) (hC : C.rank ≤ 2)
    (hz : endpointEnergy C = 0) (hrow : ∀ r q, C (2, r) q = 0) :
    cutForm (firstSiteBlock C 0 1) = 0 ∧
    cutForm (firstSiteBlock C 1 0) = 0 ∧
    cutForm (firstSiteContraction C ![1, 1, 0] ![1, -1, 0]) = 0 ∧
    cutForm (firstSiteContraction C ![1, -1, 0] ![1, 1, 0]) = 0 ∧
    cutForm (firstSiteContraction C ![1, -Complex.I, 0] ![1, Complex.I, 0]) = 0 ∧
    cutForm (firstSiteContraction C ![1, Complex.I, 0] ![1, -Complex.I, 0]) = 0 := by
  have he := endpointEnergy_missing_first_row_two_six C hrow
  have h₁ := firstSiteBlock_cutForm_nonneg C hC 0 2
  have h₂ := firstSiteBlock_cutForm_nonneg C hC 1 2
  have h₃ := firstSiteBlock_cutForm_nonneg C hC 0 1
  have h₄ := firstSiteBlock_cutForm_nonneg C hC 1 0
  have hc (x y : Fin 3 → ℂ) : 0 ≤ cutForm (firstSiteContraction C x y) :=
    cutForm_nonneg_of_rank_le_two _ ((firstSiteContraction_rank_le C x y).trans hC)
  have h₅ := hc ![1, 1, 0] ![1, -1, 0]
  have h₆ := hc ![1, -1, 0] ![1, 1, 0]
  have h₇ := hc ![1, -Complex.I, 0] ![1, Complex.I, 0]
  have h₈ := hc ![1, Complex.I, 0] ![1, -Complex.I, 0]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- Original thin qutrit zeros construct the unitary and all off-plane cut
zeros unconditionally. This does not assert a common input/output carrier. -/
theorem qutrit_thin_first_offplane_cut_zeros_unconditional
    (C : Matrix QutritSites QutritSites ℂ) (hC : C.rank ≤ 2)
    (hz : endpointEnergy C = 0) (hthin : localRangeDim₁ C ≤ 2) :
    ∃ (U : Matrix (Fin 3) (Fin 3) ℂ) (k : Fin 3), Uᴴ * U = 1 ∧
      (∀ r q, (embed₃ (b' := Fin 3) (c' := Fin 3) U 1 1 C) (k, r) q = 0) ∧
      (∀ i, cutForm (firstSiteBlock (embed₃ (b' := Fin 3) (c' := Fin 3) U 1 1 C) i k) = 0) ∧
      endpointEnergy (firstSiteInputDrop (embed₃ (b' := Fin 3) (c' := Fin 3) U 1 1 C) k) = 0 := by
  obtain ⟨U, k, hU, hrow, hr, he, _⟩ :=
    qutrit_thin_first_exists_unitary_missing_row C hthin
  have hD : (embed₃ (b' := Fin 3) (c' := Fin 3) U 1 1 C).rank ≤ 2 := hr.trans_le hC
  have hDz : endpointEnergy (embed₃ (b' := Fin 3) (c' := Fin 3) U 1 1 C) = 0 := he.trans hz
  exact ⟨U, k, hU, hrow,
    firstSiteBlock_cutForm_zero_of_thin_endpoint_zero _ hD hDz k hrow,
    (endpointEnergy_thin_first_inputSplit_zero _ hD hDz k hrow).2⟩

end ThreeCopyQutritWerner
