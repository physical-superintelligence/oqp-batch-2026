module

public import CGLMPBounds.Circulation.JointCuts
public import CGLMPBounds.Defs.ScalarForm

@[expose] public section


/-! Actual vanishing total forbidden mass implies the cut decomposition. -/

namespace CGLMPBounds.Circulation
noncomputable section
open scoped Matrix

theorem forbidden_zero_of_total_zero {d r : ℕ} [NeZero r]
    (V : Fin d → Mat r) (hunit : ∀ j, (V j)ᴴ * V j = 1) (hfour : ∀ j, V j ^ 4 = 1)
    (hzero : scalarForbiddenTotal V = 0) :
    ∀ i j, i < j → forbidden (V i) (V j) = 0 := by
  have hp (i j : Fin d) : 0 ≤ if i < j then forbidden (V i) (V j) else 0 := by
    split_ifs
    · exact fourth_root_forbidden_nonneg _ _ (hunit i) (hunit j) (hfour i) (hfour j)
    · rfl
  have hrow (i : Fin d) : 0 ≤ ∑ j, if i < j then forbidden (V i) (V j) else 0 :=
    Finset.sum_nonneg (fun j _ => hp i j)
  unfold scalarForbiddenTotal at hzero
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hrow i)).mp hzero
  intro i j hij
  have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hp i j)).mp
    (hi i (Finset.mem_univ i)) j (Finset.mem_univ j)
  simpa only [if_pos hij] using hj

/-- The scalar-cut spanning conclusion from the literal F_d=0. -/
theorem fourth_root_cut_spaces_span_of_total_zero {d r : ℕ} [NeZero d] [NeZero r]
    (V : Fin d → Mat r) (hunit : ∀ j, (V j)ᴴ * V j = 1) (hfour : ∀ j, V j ^ 4 = 1)
    (hzero : scalarForbiddenTotal V = 0) :
    (⨆ a : Fin 4, ⨆ j₀ : Fin d, fourthRootCutSpace V a j₀) = ⊤ :=
  fourth_root_cut_spaces_span V hunit hfour (forbidden_zero_of_total_zero V hunit hfour hzero)

end
end CGLMPBounds.Circulation
