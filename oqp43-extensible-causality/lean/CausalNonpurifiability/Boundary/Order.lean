module

public import CausalNonpurifiability.Definitions.Process

@[expose] public section


/-!
# `CausalNonpurifiability.Boundary.Order`

One-dimensional ports force a definite order (manuscript §9, first half of
`thm:main` (iii)): if one of `m, d, n, e` equals `1` then every valid process is ordered
and hence causally separable.

* `d = 1`: `R_{A_O}` is the identity (replacement on a one-point factor), so `W ∈ O_{B≺A}`.
* `e = 1`: symmetric, `R_{B_O} = id`, so `W ∈ O_{A≺B}`.
* `m = 1`: `A_I` is trivial, so `R_{A_I A_O} = R_{A_O}`; `eq:LV-b` becomes
  `R_{A_O} W = R_{B_O} R_{A_O} W`, and `eq:LV-c` then collapses to `W = R_{B_O} W`, i.e.
  `W ∈ O_{A≺B}`.
* `n = 1`: symmetric, `W ∈ O_{B≺A}`.

The zero operator lies in both cones, so an ordered valid process is causally separable
(`W = W + 0 = 0 + W`).

All facts are proved generically for a `[Subsingleton _]` factor of `Op (LabIdx AI AO BI BO)`
and specialised to `Fin` coordinates through `Fin.subsingleton_iff_le_one`.

Manuscript anchors: §9 `sec:boundary` (dimension dichotomy, `thm:main` (iii)), `eq:LV`,
`eq:ordered-cones`, `eq:replacement`.
-/

set_option autoImplicit false

open scoped Kronecker ComplexOrder

namespace CausalNonpurifiability

/-! ### Replacement on a one-point factor is the identity -/

section Subsingleton

theorem card_eq_one_of_subsingleton (Y : Type) [Fintype Y] [Nonempty Y] [Subsingleton Y] :
    Fintype.card Y = 1 :=
  Fintype.card_eq_one_iff.2 ⟨Classical.arbitrary Y, fun y => Subsingleton.elim y _⟩

theorem invCard_eq_one_of_subsingleton (Y : Type) [Fintype Y] [Nonempty Y] [Subsingleton Y] :
    invCard Y = 1 := by
  rw [invCard, card_eq_one_of_subsingleton]
  simp

/-- `1/|X × Y| = 1/|Y|` when `X` is a one-point type. -/
theorem invCard_prod_left_of_subsingleton (X Y : Type) [Fintype X] [Fintype Y] [Nonempty X]
    [Subsingleton X] : invCard (X × Y) = invCard Y := by
  rw [invCard, invCard, Fintype.card_prod, card_eq_one_of_subsingleton X, one_mul]

variable {ι I Y : Type} [Fintype ι] [DecidableEq ι] [Fintype I] [Fintype Y] [DecidableEq I]
  [DecidableEq Y]

omit [Fintype ι] in
/-- Replacement along a coordinate equivalence whose singled-out factor `Y` is a one-point type
is the identity (`eq:replacement` with `dim Y = 1`). -/
theorem replaceVia_of_subsingleton [Nonempty Y] [Subsingleton Y] (e : ι ≃ I × Y) (T : Op ι) :
    replaceVia e T = T := by
  ext x y
  rw [replaceVia_apply_entry, if_pos (Subsingleton.elim _ _), invCard_eq_one_of_subsingleton,
    one_mul, Fintype.sum_subsingleton _ (e x).2]
  have h1 : e.symm ((e x).1, (e x).2) = x := by simp
  have h2 : e.symm ((e y).1, (e x).2) = y := by
    rw [Subsingleton.elim (e x).2 (e y).2]
    simp
  rw [h1, h2]

end Subsingleton

section Generic

variable {AI AO BI BO : Type} [Fintype AI] [Fintype AO] [Fintype BI] [Fintype BO]
  [DecidableEq AI] [DecidableEq AO] [DecidableEq BI] [DecidableEq BO]
  (W : Op (LabIdx AI AO BI BO))

/-- `dim A_O = 1 ⇒ R_{A_O} = id`. -/
theorem R_AO_of_subsingleton [Nonempty AO] [Subsingleton AO] : R_AO W = W :=
  replaceVia_of_subsingleton _ W

/-- `dim B_O = 1 ⇒ R_{B_O} = id`. -/
theorem R_BO_of_subsingleton [Nonempty BO] [Subsingleton BO] : R_BO W = W :=
  replaceVia_of_subsingleton _ W

/-- `dim A_I = 1 ⇒ R_{A_I A_O} = R_{A_O}`. -/
theorem R_AIAO_eq_R_AO_of_subsingleton [Nonempty AI] [Subsingleton AI] : R_AIAO W = R_AO W := by
  ext ⟨⟨a, o⟩, ⟨b, t⟩⟩ ⟨⟨a', o'⟩, ⟨b', t'⟩⟩
  obtain rfl : a = a' := Subsingleton.elim a a'
  by_cases h : o = o'
  · subst h
    simp only [R_AIAO_apply, R_AO_apply, if_true, Fintype.sum_prod_type,
      Fintype.sum_subsingleton _ a, invCard_prod_left_of_subsingleton]
  · simp [R_AIAO_apply, R_AO_apply, h]

/-- `dim B_I = 1 ⇒ R_{B_I B_O} = R_{B_O}`. -/
theorem R_BIBO_eq_R_BO_of_subsingleton [Nonempty BI] [Subsingleton BI] : R_BIBO W = R_BO W := by
  ext ⟨⟨a, o⟩, ⟨b, t⟩⟩ ⟨⟨a', o'⟩, ⟨b', t'⟩⟩
  obtain rfl : b = b' := Subsingleton.elim b b'
  by_cases h : t = t'
  · subst h
    simp only [R_BIBO_apply, R_BO_apply, if_true, Fintype.sum_prod_type,
      Fintype.sum_subsingleton _ b, invCard_prod_left_of_subsingleton]
  · simp [R_BIBO_apply, R_BO_apply, h]

/-- With `A_I` trivial, `eq:LV-b` and `eq:LV-c` force `R_{B_O} W = W`. -/
theorem GenLV.R_BO_eq_of_subsingleton_AI [Nonempty AI] [Subsingleton AI] {W : Op (LabIdx AI AO BI BO)}
    (hW : GenLV W) : R_BO W = W := by
  obtain ⟨-, -, hb, hc⟩ := hW
  rw [R_AIAO_eq_R_AO_of_subsingleton, sub_eq_zero] at hb
  rw [R_AO_R_BO_comm, ← hb] at hc
  have h0 : W - R_BO W = 0 := by
    calc W - R_BO W = W - R_AO W - R_BO W + R_AO W := by abel
      _ = 0 := hc
  exact (sub_eq_zero.1 h0).symm

/-- With `B_I` trivial, `eq:LV-a` and `eq:LV-c` force `R_{A_O} W = W`. -/
theorem GenLV.R_AO_eq_of_subsingleton_BI [Nonempty BI] [Subsingleton BI] {W : Op (LabIdx AI AO BI BO)}
    (hW : GenLV W) : R_AO W = W := by
  obtain ⟨-, ha, -, hc⟩ := hW
  rw [R_BIBO_eq_R_BO_of_subsingleton, sub_eq_zero] at ha
  rw [← ha] at hc
  have h0 : W - R_AO W = 0 := by
    calc W - R_AO W = W - R_AO W - R_BO W + R_BO W := by abel
      _ = 0 := hc
  exact (sub_eq_zero.1 h0).symm

end Generic

/-! ### `Fin`-coordinate interface -/

section Ports

variable {D : Ports} {W : PMat D}

theorem subsingleton_fin_of_eq_one {k : ℕ} (h : k = 1) : Subsingleton (Fin k) :=
  Fin.subsingleton_iff_le_one.2 h.le

/-- `d = 1 ⇒ R_{A_O} W = W` (`eq:replacement` on a one-point factor). -/
theorem ordered_of_d_eq_one (h : D.d = 1) (_hW : InLV D W) : R_AO W = W := by
  have := subsingleton_fin_of_eq_one h
  exact R_AO_of_subsingleton W

/-- `e = 1 ⇒ R_{B_O} W = W`. -/
theorem ordered_of_e_eq_one (h : D.e = 1) (_hW : InLV D W) : R_BO W = W := by
  have := subsingleton_fin_of_eq_one h
  exact R_BO_of_subsingleton W

/-- `m = 1 ⇒ R_{B_O} W = W` (`eq:LV-b` collapses to `R_{A_O} W = R_{B_O} R_{A_O} W`, then
`eq:LV-c`). -/
theorem ordered_of_m_eq_one (h : D.m = 1) (hW : InLV D W) : R_BO W = W := by
  have := subsingleton_fin_of_eq_one h
  exact GenLV.R_BO_eq_of_subsingleton_AI hW

/-- `n = 1 ⇒ R_{A_O} W = W` (symmetric). -/
theorem ordered_of_n_eq_one (h : D.n = 1) (hW : InLV D W) : R_AO W = W := by
  have := subsingleton_fin_of_eq_one h
  exact GenLV.R_AO_eq_of_subsingleton_BI hW

theorem orderedBA_of_d_eq_one (h : D.d = 1) (hW : Valid D W) : OrderedBA D W :=
  ⟨hW.1, hW.2.1, ordered_of_d_eq_one h hW.1⟩

theorem orderedAB_of_e_eq_one (h : D.e = 1) (hW : Valid D W) : OrderedAB D W :=
  ⟨hW.1, hW.2.1, ordered_of_e_eq_one h hW.1⟩

theorem orderedAB_of_m_eq_one (h : D.m = 1) (hW : Valid D W) : OrderedAB D W :=
  ⟨hW.1, hW.2.1, ordered_of_m_eq_one h hW.1⟩

theorem orderedBA_of_n_eq_one (h : D.n = 1) (hW : Valid D W) : OrderedBA D W :=
  ⟨hW.1, hW.2.1, ordered_of_n_eq_one h hW.1⟩

/-- **One-dimensional ports force an order** (§9, `thm:main` (iii), first half). -/
theorem one_dimensional_ordered (h1 : D.m = 1 ∨ D.d = 1 ∨ D.n = 1 ∨ D.e = 1) (hW : Valid D W) :
    OrderedAB D W ∨ OrderedBA D W := by
  rcases h1 with hm | hd | hn | he
  · exact Or.inl (orderedAB_of_m_eq_one hm hW)
  · exact Or.inr (orderedBA_of_d_eq_one hd hW)
  · exact Or.inr (orderedBA_of_n_eq_one hn hW)
  · exact Or.inl (orderedAB_of_e_eq_one he hW)

/-! ### Zero lies in both cones -/

theorem inLV_zero (D : Ports) : InLV D (0 : PMat D) := by
  refine ⟨Matrix.isHermitian_zero, ?_, ?_, ?_⟩ <;> simp [map_zero]

theorem orderedAB_zero (D : Ports) : OrderedAB D (0 : PMat D) :=
  ⟨inLV_zero D, Matrix.PosSemidef.zero, map_zero _⟩

theorem orderedBA_zero (D : Ports) : OrderedBA D (0 : PMat D) :=
  ⟨inLV_zero D, Matrix.PosSemidef.zero, map_zero _⟩

/-- An ordered valid process is causally separable: pad with `0`, which lies in both cones. -/
theorem causallySeparable_of_ordered (hW : Valid D W) (h : OrderedAB D W ∨ OrderedBA D W) :
    CausallySeparable D W := by
  rcases h with hAB | hBA
  · exact ⟨hW, W, 0, hAB, orderedBA_zero D, (add_zero W).symm⟩
  · exact ⟨hW, 0, W, orderedAB_zero D, hBA, (zero_add W).symm⟩

/-- **Every valid process with a one-dimensional port is causally separable** (§9). -/
theorem one_dimensional_causallySeparable (h1 : D.m = 1 ∨ D.d = 1 ∨ D.n = 1 ∨ D.e = 1)
    (hW : Valid D W) : CausallySeparable D W :=
  causallySeparable_of_ordered hW (one_dimensional_ordered h1 hW)

end Ports

end CausalNonpurifiability
