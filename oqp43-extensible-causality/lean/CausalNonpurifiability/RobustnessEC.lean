module

public import CausalNonpurifiability.Robustness
public import CausalNonpurifiability.EC.Bridge
public import CausalNonpurifiability.Linear.OpNorm

@[expose] public section


/-!
# `CausalNonpurifiability.RobustnessEC`

The extensible-causality half of the closed relative ball (manuscript §7, `thm:main` (ii)):
for all ports `≥ 2` and every `H` in the ball `eq:ball` (`InBall`),
`W_c + H` is extensibly causal.

## Route (§7, in PSD form)

* `eq:perturbation-split`: `H_A := R_{B_O} H − ½ R_{A_O} R_{B_O} H`,
  `H_B := R_{A_O} H − ½ R_{A_O} R_{B_O} H`; `H_A + H_B = H` by `eq:LV-c`.  Both summands lie in
  `L_V` (the replacement maps commute and *absorb*: `R_{B_I B_O} R_{B_O} = R_{B_I B_O}`,
  `R_{A_I A_O} R_{A_O} = R_{A_I A_O}`; `GenLV.R_BO_mem`, `GenLV.R_AO_mem`), have the respective
  ordered output invariances, and are traceless.
* `eq:split-norm` / `eq:white-ordered` via PSD bounds instead of operator norms: from
  `r I ± H ≥ 0`, positivity and unitality of the replacements give `r I + R_{B_O} H ≥ 0` and
  `r I − R_{A_O} R_{B_O} H ≥ 0`, hence `(r + r/2) I + H_A ≥ 0` (`splitA_psd`); with
  `r = 1/(300mn)` this is `T_A := I/(200mn) + H_A ≥ 0` (the manuscript's `T_A/100`), and
  `T_A ∈ O_{A≺B}`, `T_B ∈ O_{B≺A}`.
* `eq:ball-mixture`: `W_c + H = U' + V' + 2 Q_{C'}` with `U' := (99/100) U + T_A ∈ O_{A≺B}`,
  `V' := (99/100) V + T_B ∈ O_{B≺A}`, `C' := (99/100) C` (`ball_decomp`).
* **Primary proof = the manuscript's** (§7, l. 933–943; section `PaperRoute`): each white-ordered
  summand stays ordered under every shared-input extension (`ordered_extended_A/B`), so
  `2 p_{T_A}` and `2 p_{T_B}` are normalized one-way no-signalling distributions
  (`twice_ordered_A/B`, masses from `pT_ordered_mass`, no-signalling from
  `pT_ordered_nsAB/nsBA`); mixing them with the causal components of `p_{W_0}` in weights
  `99/100, 1/100` (`halfCausal_mix`, `bornExtended_ball_decomp`) gives `ball_halfCausal_mixture`
  and `ball_extensiblyCausal_mixture` — "the final order weights are again `1/2, 1/2`".
* Alternative proof (`ball_extensiblyCausal_rect`): the generic rectangle machinery
  (`EC/Rectangles`, `rectangle_interface_of_dc`) applies with
  the reference states `χ'_A := ω_A(U') + Tr_{B_I} C'`, `χ'_B := ω_B(V') + Tr_{A_I} C'`, which
  are positive and of trace `(99/100)(1/5) + 1/200 + (99/100)(3/10) = 1/2` (`ballChiA_trace`) —
  the "final order weights are again `1/2, 1/2`" of §7 — and with `D_{C'} = (99/100) D_C ≥ 0`
  (`DC_rat_smul`).  Then `ec_of_rectangles` with `ball_valid`.

Manuscript anchors: `eq:ball`, `eq:perturbation-split`, `eq:split-norm`, `eq:white-ordered`,
`eq:ball-mixture`, `eq:signed-decomposition`, `eq:reference-states`.
-/

set_option autoImplicit false

open Matrix
open scoped ComplexOrder Kronecker

namespace CausalNonpurifiability

noncomputable section

/-! ### Replacement algebra: absorption and closure of `L_V` -/

section Absorb

variable {AI AO BI BO : Type} [Fintype AI] [Fintype AO] [Fintype BI] [Fintype BO]
  [DecidableEq AI] [DecidableEq AO] [DecidableEq BI] [DecidableEq BO]

/-- Nested composition `R_{B_I B_O} ∘ R_{B_O} = R_{B_I B_O}` — the case `Z ⊆ Y` of the general
rule `R_Y ∘ R_Z = R_{Y ∪ Z}` for replacement maps (`eq:replacement`): replacing `B_O` does not
change the partial trace over `B_I B_O`. -/
theorem R_BIBO_R_BO [Nonempty BO] (T : Op (LabIdx AI AO BI BO)) : R_BIBO (R_BO T) = R_BIBO T := by
  ext x y
  rw [R_BIBO_apply, R_BIBO_apply]
  by_cases h : x.2 = y.2
  · rw [if_pos h, if_pos h]
    congr 1
    simp only [R_BO_apply, if_true, Fintype.sum_prod_type, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← mul_assoc, card_mul_invCard, one_mul]
  · rw [if_neg h, if_neg h]

/-- Nested composition `R_{A_I A_O} ∘ R_{A_O} = R_{A_I A_O}` (`R_Y ∘ R_Z = R_{Y ∪ Z}`,
`eq:replacement`). -/
theorem R_AIAO_R_AO [Nonempty AO] (T : Op (LabIdx AI AO BI BO)) : R_AIAO (R_AO T) = R_AIAO T := by
  ext x y
  rw [R_AIAO_apply, R_AIAO_apply]
  by_cases h : x.1 = y.1
  · rw [if_pos h, if_pos h]
    congr 1
    simp only [R_AO_apply, if_true, Fintype.sum_prod_type, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← mul_assoc, card_mul_invCard, one_mul]
  · rw [if_neg h, if_neg h]

/-- Nested composition the other way round, `R_{B_O} ∘ R_{B_I B_O} = R_{B_I B_O}`
(`R_Y ∘ R_Z = R_{Y ∪ Z}`): `R_{B_I B_O} T` already carries `I_{B_O}` on `B_O`. -/
theorem R_BO_R_BIBO [Nonempty BO] (T : Op (LabIdx AI AO BI BO)) : R_BO (R_BIBO T) = R_BIBO T := by
  ext ⟨⟨a, o⟩, ⟨b, t⟩⟩ ⟨⟨a', o'⟩, ⟨b', t'⟩⟩
  simp only [R_BO_apply, R_BIBO_apply, Prod.mk.injEq]
  by_cases ht : t = t'
  · subst ht
    by_cases hb : b = b'
    · subst hb
      simp only [and_self, if_true, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      rw [← mul_assoc, invCard_mul_card, one_mul]
    · simp [hb]
  · simp [ht]

/-- `R_{A_O} ∘ R_{A_I A_O} = R_{A_I A_O}` (`R_Y ∘ R_Z = R_{Y ∪ Z}`). -/
theorem R_AO_R_AIAO [Nonempty AO] (T : Op (LabIdx AI AO BI BO)) : R_AO (R_AIAO T) = R_AIAO T := by
  ext ⟨⟨a, o⟩, ⟨b, t⟩⟩ ⟨⟨a', o'⟩, ⟨b', t'⟩⟩
  simp only [R_AO_apply, R_AIAO_apply, Prod.mk.injEq]
  by_cases ho : o = o'
  · subst ho
    by_cases ha : a = a'
    · subst ha
      simp only [and_self, if_true, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      rw [← mul_assoc, invCard_mul_card, one_mul]
    · simp [ha]
  · simp [ho]

/-- **"All replacement maps commute"** (§7), nested case: `R_{B_I B_O}` and `R_{B_O}` commute
(both composites equal `R_{B_I B_O}`). -/
theorem R_BIBO_comm_R_BO [Nonempty BO] (T : Op (LabIdx AI AO BI BO)) :
    R_BIBO (R_BO T) = R_BO (R_BIBO T) := by
  rw [R_BIBO_R_BO, R_BO_R_BIBO]

/-- Nested commutation on Alice's side: `R_{A_I A_O}` and `R_{A_O}` commute. -/
theorem R_AIAO_comm_R_AO [Nonempty AO] (T : Op (LabIdx AI AO BI BO)) :
    R_AIAO (R_AO T) = R_AO (R_AIAO T) := by
  rw [R_AIAO_R_AO, R_AO_R_AIAO]

/-- `L_V` is closed under differences. -/
theorem genLV_sub {W W' : Op (LabIdx AI AO BI BO)} (h : GenLV W) (h' : GenLV W') :
    GenLV (W - W') := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ W']
  exact genLV_add h (genLV_smul (isSelfAdjoint_iff.mpr (by simp)) h')

/-- `L_V` is closed under `R_{B_O}` (§7: "the summands remain in `L_V`"). -/
theorem GenLV.R_BO_mem [Nonempty BO] {X : Op (LabIdx AI AO BI BO)} (hX : GenLV X) :
    GenLV (R_BO X) := by
  obtain ⟨hH, ha, -, -⟩ := hX
  refine ⟨R_BO_isHermitian hH, ?_, ?_, ?_⟩
  · rw [R_BIBO_R_BO]
    exact ha
  · rw [← R_BO_R_AIAO_comm, R_BO_idem, sub_self]
  · rw [R_BO_idem]
    abel

/-- `L_V` is closed under `R_{A_O}` (§7). -/
theorem GenLV.R_AO_mem [Nonempty AO] {X : Op (LabIdx AI AO BI BO)} (hX : GenLV X) :
    GenLV (R_AO X) := by
  obtain ⟨hH, -, hb, -⟩ := hX
  refine ⟨R_AO_isHermitian hH, ?_, ?_, ?_⟩
  · rw [← R_AO_R_BIBO_comm, R_AO_idem, sub_self]
  · rw [R_AIAO_R_AO]
    exact hb
  · rw [R_AO_R_BO_comm, R_AO_idem]
    abel

/-- **The manuscript's justification, literally** (§7: "All replacement maps commute, so the
summands remain in `L_V`"): `eq:LV-a` for `R_{B_O} X` is `R_{B_O}` of `eq:LV-a` for `X`, by
commuting `R_{B_O}` past `R_{B_I B_O}` (`R_BIBO_comm_R_BO`) and past `R_{A_O}`
(`R_AO_R_BO_comm`); `eq:LV-b` is `(R_{B_O} − R_{B_O}²) R_{A_I A_O} X = 0` by commutation and
idempotence; `eq:LV-c` is idempotence.  Same statement as `GenLV.R_BO_mem`, different proof. -/
theorem GenLV.R_BO_mem' [Nonempty BO] {X : Op (LabIdx AI AO BI BO)} (hX : GenLV X) :
    GenLV (R_BO X) := by
  obtain ⟨hH, ha, -, -⟩ := hX
  refine ⟨R_BO_isHermitian hH, ?_, ?_, ?_⟩
  · rw [R_BIBO_comm_R_BO, R_AO_R_BO_comm, ← map_sub, ha, map_zero]
  · rw [← R_BO_R_AIAO_comm, R_BO_idem, sub_self]
  · rw [R_BO_idem]
    abel

/-- The manuscript's justification for `R_{A_O} X ∈ L_V` (commutation + idempotence + `eq:LV-b`
of `X`). -/
theorem GenLV.R_AO_mem' [Nonempty AO] {X : Op (LabIdx AI AO BI BO)} (hX : GenLV X) :
    GenLV (R_AO X) := by
  obtain ⟨hH, -, hb, -⟩ := hX
  refine ⟨R_AO_isHermitian hH, ?_, ?_, ?_⟩
  · rw [← R_AO_R_BIBO_comm, R_AO_idem, sub_self]
  · rw [R_AIAO_comm_R_AO, ← R_AO_R_BO_comm, ← map_sub, hb, map_zero]
  · rw [R_AO_R_BO_comm, R_AO_idem]
    abel

end Absorb

/-! ### Scalar helpers -/

lemma isSelfAdjoint_half : IsSelfAdjoint (1 / 2 : ℂ) := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℚ) : ℂ) by norm_num]
  exact isSelfAdjoint_ratCast _

lemma half_nonneg_complex : (0 : ℂ) ≤ 1 / 2 := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℚ) : ℂ) by norm_num]
  exact ratCast_nonneg_complex (by norm_num)

/-! ### The perturbation split (`eq:perturbation-split`) -/

section Split

variable (D : Ports)

/-- `X_A = R_{B_O} X − ½ R_{A_O B_O} X` (`eq:perturbation-split`). -/
def splitA (X : PMat D) : PMat D := R_BO X - (1 / 2 : ℂ) • R_AO (R_BO X)

/-- `X_B = R_{A_O} X − ½ R_{A_O B_O} X` (`eq:perturbation-split`). -/
def splitB (X : PMat D) : PMat D := R_AO X - (1 / 2 : ℂ) • R_AO (R_BO X)

/-- `X_A + X_B = X` for `X ∈ L_V` (`eq:LV-c`). -/
theorem splitA_add_splitB {X : PMat D} (hX : InLV D X) : splitA D X + splitB D X = X := by
  apply eq_of_sub_eq_zero
  rw [show splitA D X + splitB D X - X = -(X - R_AO X - R_BO X + R_AO (R_BO X)) by
    unfold splitA splitB; module, hX.lv_c, neg_zero]

theorem R_BO_splitA (X : PMat D) : R_BO (splitA D X) = splitA D X := by
  unfold splitA
  rw [map_sub, map_smul, R_BO_idem, ← R_AO_R_BO_comm, R_BO_idem]

theorem R_AO_splitB (X : PMat D) : R_AO (splitB D X) = splitB D X := by
  unfold splitB
  rw [map_sub, map_smul, R_AO_idem, R_AO_idem]

theorem splitA_inLV {X : PMat D} (hX : InLV D X) : InLV D (splitA D X) :=
  genLV_sub (GenLV.R_BO_mem hX) (genLV_smul isSelfAdjoint_half (GenLV.R_AO_mem (GenLV.R_BO_mem hX)))

theorem splitB_inLV {X : PMat D} (hX : InLV D X) : InLV D (splitB D X) :=
  genLV_sub (GenLV.R_AO_mem hX) (genLV_smul isSelfAdjoint_half (GenLV.R_AO_mem (GenLV.R_BO_mem hX)))

/-- §7, literally: "All replacement maps commute, so the summands remain in `L_V` and have the
respective ordered output invariances" — `X_A ∈ L_V` by `GenLV.R_BO_mem'`/`GenLV.R_AO_mem'`
(commutation + idempotence + `eq:LV` of `X`) and linearity; the output invariance is
`R_BO_splitA`. -/
theorem splitA_inLV' {X : PMat D} (hX : InLV D X) : InLV D (splitA D X) :=
  genLV_sub (GenLV.R_BO_mem' hX)
    (genLV_smul isSelfAdjoint_half (GenLV.R_AO_mem' (GenLV.R_BO_mem' hX)))

/-- §7, literally, for `X_B` (output invariance: `R_AO_splitB`). -/
theorem splitB_inLV' {X : PMat D} (hX : InLV D X) : InLV D (splitB D X) :=
  genLV_sub (GenLV.R_AO_mem' hX)
    (genLV_smul isSelfAdjoint_half (GenLV.R_AO_mem' (GenLV.R_BO_mem' hX)))

/-- The split summands are traceless ("replacement preserves trace", §7). -/
theorem trace_splitA {X : PMat D} (hX : X.trace = 0) : (splitA D X).trace = 0 := by
  unfold splitA
  rw [Matrix.trace_sub, Matrix.trace_smul, R_AO_trace, R_BO_trace, hX, smul_zero, sub_zero]

theorem trace_splitB {X : PMat D} (hX : X.trace = 0) : (splitB D X).trace = 0 := by
  unfold splitB
  rw [Matrix.trace_sub, Matrix.trace_smul, R_AO_trace, R_AO_trace, R_BO_trace, hX, smul_zero,
    sub_zero]

/-- **PSD form of `eq:split-norm` / `eq:white-ordered`**: `r I ± X ≥ 0` gives
`(r + r/2) I + X_A ≥ 0`, because `r I + R_{B_O} X = R_{B_O}(r I + X) ≥ 0` and
`r I − R_{A_O B_O} X = R_{A_O} R_{B_O}(r I − X) ≥ 0` (positivity and unitality of replacement). -/
theorem splitA_psd {X : PMat D} {r : ℂ} (h1 : (r • (1 : PMat D) + X).PosSemidef)
    (h2 : (r • (1 : PMat D) - X).PosSemidef) :
    ((r + r / 2) • (1 : PMat D) + splitA D X).PosSemidef := by
  have hA : (r • (1 : PMat D) + R_BO X).PosSemidef := by
    have := R_BO_posSemidef h1
    rwa [map_add, map_smul, R_BO_one] at this
  have hB : (r • (1 : PMat D) - R_AO (R_BO X)).PosSemidef := by
    have := R_AO_posSemidef (R_BO_posSemidef h2)
    rwa [map_sub, map_smul, R_BO_one, map_sub, map_smul, R_AO_one] at this
  have e : (r + r / 2) • (1 : PMat D) + splitA D X
      = (r • (1 : PMat D) + R_BO X) + (1 / 2 : ℂ) • (r • (1 : PMat D) - R_AO (R_BO X)) := by
    unfold splitA
    module
  rw [e]
  exact hA.add (posSemidef_complex_smul hB half_nonneg_complex)

theorem splitB_psd {X : PMat D} {r : ℂ} (h1 : (r • (1 : PMat D) + X).PosSemidef)
    (h2 : (r • (1 : PMat D) - X).PosSemidef) :
    ((r + r / 2) • (1 : PMat D) + splitB D X).PosSemidef := by
  have hA : (r • (1 : PMat D) + R_AO X).PosSemidef := by
    have := R_AO_posSemidef h1
    rwa [map_add, map_smul, R_AO_one] at this
  have hB : (r • (1 : PMat D) - R_AO (R_BO X)).PosSemidef := by
    have := R_AO_posSemidef (R_BO_posSemidef h2)
    rwa [map_sub, map_smul, R_BO_one, map_sub, map_smul, R_AO_one] at this
  have e : (r + r / 2) • (1 : PMat D) + splitB D X
      = (r • (1 : PMat D) + R_AO X) + (1 / 2 : ℂ) • (r • (1 : PMat D) - R_AO (R_BO X)) := by
    unfold splitB
    module
  rw [e]
  exact hA.add (posSemidef_complex_smul hB half_nonneg_complex)

end Split

/-! ### Partial trace over the first factor: linearity and trace -/

section PtraceFst

variable {I O : Type} [Fintype I] [Fintype O]

omit [Fintype O] in
theorem ptraceFst_smul (c : ℂ) (T : Op (I × O)) : ptraceFst (c • T) = c • ptraceFst T := by
  ext o o'
  simp only [ptraceFst_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]

theorem trace_ptraceFst (T : Op (I × O)) : (ptraceFst T).trace = T.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, ptraceFst_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]

end PtraceFst

/-! ### Ordered cones: algebra and marginals -/

section Cones

variable (D : Ports)

theorem orderedAB_add {U T : PMat D} (hU : OrderedAB D U) (hT : OrderedAB D T) :
    OrderedAB D (U + T) :=
  ⟨genLV_add hU.1 hT.1, hU.2.1.add hT.2.1, by rw [map_add, hU.2.2, hT.2.2]⟩

theorem orderedBA_add {V T : PMat D} (hV : OrderedBA D V) (hT : OrderedBA D T) :
    OrderedBA D (V + T) :=
  ⟨genLV_add hV.1 hT.1, hV.2.1.add hT.2.1, by rw [map_add, hV.2.2, hT.2.2]⟩

theorem orderedAB_ratSmul {q : ℚ} (hq : 0 ≤ q) {U : PMat D} (hU : OrderedAB D U) :
    OrderedAB D ((q : ℂ) • U) :=
  ⟨genLV_smul (isSelfAdjoint_ratCast q) hU.1,
    posSemidef_complex_smul hU.2.1 (ratCast_nonneg_complex hq), by rw [map_smul, hU.2.2]⟩

theorem orderedBA_ratSmul {q : ℚ} (hq : 0 ≤ q) {V : PMat D} (hV : OrderedBA D V) :
    OrderedBA D ((q : ℂ) • V) :=
  ⟨genLV_smul (isSelfAdjoint_ratCast q) hV.1,
    posSemidef_complex_smul hV.2.1 (ratCast_nonneg_complex hq), by rw [map_smul, hV.2.2]⟩

/-- `Tr ω_A(T) = Tr T / (de)` (sentence after `eq:ordered-marginal`). -/
theorem trace_omegaA' (T : PMat D) :
    (omegaA D T).trace = (((D.d * D.e : ℕ) : ℂ))⁻¹ * T.trace := by
  unfold omegaA
  rw [Matrix.trace_smul, smul_eq_mul, trace_ptraceOut, Matrix.reindex_apply,
    trace_submatrix_equiv']

theorem trace_omegaB' (T : PMat D) :
    (omegaB D T).trace = (((D.d * D.e : ℕ) : ℂ))⁻¹ * T.trace := by
  unfold omegaB
  rw [Matrix.trace_smul, smul_eq_mul, trace_ptraceOut, Matrix.reindex_apply,
    trace_submatrix_equiv']

theorem invNatCast_nonneg (k : ℕ) : (0 : ℂ) ≤ ((k : ℂ))⁻¹ := by
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
  exact Complex.zero_le_real.mpr (inv_nonneg.mpr (Nat.cast_nonneg _))

/-- `ω_A(T) ≥ 0` for `T ≥ 0` ("the positive operator `ω_A(T)`", §2.1). -/
theorem omegaA_posSemidef' {T : PMat D} (hT : T.PosSemidef) : (omegaA D T).PosSemidef := by
  unfold omegaA
  refine posSemidef_complex_smul (ptraceOut_posSemidef ?_) (invNatCast_nonneg _)
  rw [Matrix.reindex_apply]
  exact hT.submatrix _

theorem omegaB_posSemidef' {T : PMat D} (hT : T.PosSemidef) : (omegaB D T).PosSemidef := by
  unfold omegaB
  refine posSemidef_complex_smul (ptraceOut_posSemidef ?_) (invNatCast_nonneg _)
  rw [Matrix.reindex_apply]
  exact hT.submatrix _

/-- `Q_C` is linear in `C` (`eq:QC`). -/
theorem QC_smul (c : ℂ) (Cm : Op (Fin D.m × Fin D.n)) : QC D (c • Cm) = c • QC D Cm := by
  ext x y
  simp only [QC, Matrix.smul_apply, smul_eq_mul, mul_assoc]

end Cones

/-! ### The white-ordered pieces and the ball decomposition (`eq:white-ordered`, `eq:ball-mixture`) -/

section BallEC

variable (D : Ports)

/-- `T_A/100 = I/(200mn) + H_A` (`eq:white-ordered` for `X = 100 H`, divided by `100`). -/
def ballTA (H : PMat D) : PMat D := (1 / (200 * D.m * D.n) : ℂ) • (1 : PMat D) + splitA D H

/-- `T_B/100 = I/(200mn) + H_B` (`eq:white-ordered`). -/
def ballTB (H : PMat D) : PMat D := (1 / (200 * D.m * D.n) : ℂ) • (1 : PMat D) + splitB D H

lemma ball_scalar_eq : (1 / (200 * D.m * D.n) : ℂ) = ballRadius D + ballRadius D / 2 := by
  rw [ballRadius]
  ring

lemma ball_scalar_isSelfAdjoint : IsSelfAdjoint (1 / (200 * D.m * D.n) : ℂ) := by
  rw [show (1 / (200 * D.m * D.n) : ℂ) = ((1 / (200 * D.m * D.n) : ℚ) : ℂ) by push_cast; ring]
  exact isSelfAdjoint_ratCast _

theorem ballTA_posSemidef {H : PMat D} (hH : InBall D H) : (ballTA D H).PosSemidef := by
  rw [ballTA, ball_scalar_eq]
  exact splitA_psd D hH.2.2.1 hH.2.2.2

theorem ballTB_posSemidef {H : PMat D} (hH : InBall D H) : (ballTB D H).PosSemidef := by
  rw [ballTB, ball_scalar_eq]
  exact splitB_psd D hH.2.2.1 hH.2.2.2

/-- `T_A ∈ O_{A≺B}` (`eq:white-ordered`). -/
theorem ballTA_orderedAB {H : PMat D} (hH : InBall D H) : OrderedAB D (ballTA D H) :=
  ⟨genLV_add (genLV_smul (ball_scalar_isSelfAdjoint D) genLV_one) (splitA_inLV D hH.1),
    ballTA_posSemidef D hH, by rw [ballTA, map_add, map_smul, R_BO_one, R_BO_splitA]⟩

/-- `T_B ∈ O_{B≺A}` (`eq:white-ordered`). -/
theorem ballTB_orderedBA {H : PMat D} (hH : InBall D H) : OrderedBA D (ballTB D H) :=
  ⟨genLV_add (genLV_smul (ball_scalar_isSelfAdjoint D) genLV_one) (splitB_inLV D hH.1),
    ballTB_posSemidef D hH, by rw [ballTB, map_add, map_smul, R_AO_one, R_AO_splitB]⟩

/-- `U' = (99/100) U + T_A` (`eq:ball-mixture`). -/
def ballU (H : PMat D) : PMat D := ((99 / 100 : ℚ) : ℂ) • toC (U D.m D.d D.n D.e) + ballTA D H

/-- `V' = (99/100) V + T_B` (`eq:ball-mixture`). -/
def ballV (H : PMat D) : PMat D := ((99 / 100 : ℚ) : ℂ) • toC (V D.m D.d D.n D.e) + ballTB D H

/-- `C' = (99/100) C` (`eq:ball-mixture`, `eq:C`). -/
def ballC : Op (Fin D.m × Fin D.n) := ((99 / 100 : ℚ) : ℂ) • toC (C D.m D.n)

theorem ballU_orderedAB (h : AllPortsGE2 D) {H : PMat D} (hH : InBall D H) :
    OrderedAB D (ballU D H) :=
  orderedAB_add D (orderedAB_ratSmul D (by norm_num) (u_orderedAB D h)) (ballTA_orderedAB D hH)

theorem ballV_orderedBA (h : AllPortsGE2 D) {H : PMat D} (hH : InBall D H) :
    OrderedBA D (ballV D H) :=
  orderedBA_add D (orderedBA_ratSmul D (by norm_num) (v_orderedBA D h)) (ballTB_orderedBA D hH)

/-- **`eq:ball-mixture` in signed form**: `W_c + H = U' + V' + 2 Q_{C'}`. -/
theorem ball_decomp {H : PMat D} (hH : InBall D H) :
    WcC D + H = ballU D H + ballV D H + (2 : ℂ) • QC D (ballC D) := by
  conv_lhs => rw [← splitA_add_splitB D hH.1]
  rw [WcC_eq, W0_signed D]
  unfold ballU ballV ballC ballTA ballTB
  rw [QC_smul]
  module

/-- `χ'_A = ω_A(U') + Tr_{B_I} C'` (`eq:reference-states` for the perturbed decomposition). -/
def ballChiA (H : PMat D) : Op (Fin D.m) := omegaA D (ballU D H) + ptraceOut (ballC D)

/-- `χ'_B = ω_B(V') + Tr_{A_I} C'`. -/
def ballChiB (H : PMat D) : Op (Fin D.n) := omegaB D (ballV D H) + ptraceFst (ballC D)

/-- `Tr_{B_I} C ≥ 0` (`C_A = diag(44,4)/160`, `eq:reference-states`). -/
theorem ptraceOut_toC_C_posSemidef (hn : 2 ≤ D.n) : (ptraceOut (toC (C D.m D.n))).PosSemidef := by
  rw [← toC_ptrB, ptrB_C hn]
  exact diagonal_nonneg_sound _ fun i => by split_ifs <;> norm_num

/-- `Tr_{A_I} C ≥ 0` (`C_B = diag(44,4)/160`). -/
theorem ptraceFst_toC_C_posSemidef (hm : 2 ≤ D.m) : (ptraceFst (toC (C D.m D.n))).PosSemidef := by
  rw [← toC_ptrA, ptrA_C hm]
  exact diagonal_nonneg_sound _ fun i => by split_ifs <;> norm_num

theorem ballChiA_posSemidef (h : AllPortsGE2 D) {H : PMat D} (hH : InBall D H) :
    (ballChiA D H).PosSemidef := by
  unfold ballChiA ballC
  rw [ptraceOut_smul]
  exact (omegaA_posSemidef' D (ballU_orderedAB D h hH).2.1).add
    (posSemidef_complex_smul (ptraceOut_toC_C_posSemidef D h.2.2.1)
      (ratCast_nonneg_complex (by norm_num)))

theorem ballChiB_posSemidef (h : AllPortsGE2 D) {H : PMat D} (hH : InBall D H) :
    (ballChiB D H).PosSemidef := by
  unfold ballChiB ballC
  rw [ptraceFst_smul]
  exact (omegaB_posSemidef' D (ballV_orderedBA D h hH).2.1).add
    (posSemidef_complex_smul (ptraceFst_toC_C_posSemidef D h.1)
      (ratCast_nonneg_complex (by norm_num)))

/-- **Mass of the perturbed reference state**: `Tr χ'_A = (99/100)(1/5) + 1/200 + (99/100)(3/10)
= 1/2` ("the final order weights are again `1/2, 1/2`", §7). -/
theorem ballChiA_trace (h : AllPortsGE2 D) {H : PMat D} (hH : InBall D H) :
    (ballChiA D H).trace = ((1 / 2 : ℝ) : ℂ) := by
  have hm : (D.m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr D.m_ne_zero
  have hd : (D.d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr D.d_ne_zero
  have hn : (D.n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr D.n_ne_zero
  have he : (D.e : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr D.e_ne_zero
  unfold ballChiA ballU ballTA ballC
  simp only [Matrix.trace_add, Matrix.trace_smul, smul_eq_mul, trace_omegaA', trace_ptraceOut,
    trace_toC, Matrix.trace_one, Fintype.card_prod, Fintype.card_fin]
  rw [trace_U h.1 h.2.2.1, trace_C h.1 h.2.2.1, trace_splitA D hH.2.1]
  push_cast
  field_simp
  ring

theorem ballChiB_trace (h : AllPortsGE2 D) {H : PMat D} (hH : InBall D H) :
    (ballChiB D H).trace = ((1 / 2 : ℝ) : ℂ) := by
  have hm : (D.m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr D.m_ne_zero
  have hd : (D.d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr D.d_ne_zero
  have hn : (D.n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr D.n_ne_zero
  have he : (D.e : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr D.e_ne_zero
  unfold ballChiB ballV ballTB ballC
  simp only [Matrix.trace_add, Matrix.trace_smul, smul_eq_mul, trace_omegaB', trace_ptraceFst,
    trace_toC, Matrix.trace_one, Fintype.card_prod, Fintype.card_fin]
  rw [trace_V h.1 h.2.2.1, trace_C h.1 h.2.2.1, trace_splitB D hH.2.1]
  push_cast
  field_simp
  ring

/-- `D_{C'} = (99/100) D_C ≥ 0` for effects (`eq:DC`, positive scaling). -/
theorem ballDC_nonneg (h : AllPortsGE2 D) {RA RB : Type} [Fintype RA] [Fintype RB]
    [DecidableEq RA] [DecidableEq RB] {σ : Op (RA × RB)} (hσ : σ.PosSemidef)
    (E : Op (Fin D.m × RA)) (H : Op (Fin D.n × RB)) (hE : Effect E) (hH : Effect H) :
    0 ≤ DC D (ballC D) σ E H := by
  rw [ballC, DC_rat_smul]
  exact mul_nonneg (by norm_num) (DC_nonneg D (toC_C_eq_diagonal_cDC h.1 h.2.2.1) hσ hE hH)

variable {RA RB X Y A B : Type} [Fintype RA] [Fintype RB] [DecidableEq RA] [DecidableEq RB]
  [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- **Rectangle interface throughout the ball**: endpoint arrays for `W_c + H` with reference
states `χ'_A`, `χ'_B` (nonnegative, mass `1/2`, every rectangle). -/
theorem ball_rectangle_interface (h : AllPortsGE2 D) {H : PMat D} (hH : InBall D H)
    {σ : Op (RA × RB)} (hσ : Density σ) (M : Instrument (Fin D.m × RA) (Fin D.d) X A)
    (N : Instrument (Fin D.n × RB) (Fin D.e) Y B) :
    (∀ x a, 0 ≤ rA D σ (ballChiA D H) M x a) ∧ (∀ y b, 0 ≤ rB D σ (ballChiB D H) N y b) ∧
    (∀ x, ∑ a, rA D σ (ballChiA D H) M x a = 1 / 2) ∧
    (∀ y, ∑ b, rB D σ (ballChiB D H) N y b = 1 / 2) ∧
    (∀ x y (S : Finset A) (T : Finset B),
      ∑ a ∈ S, ∑ b ∈ T, bornExtended D (WcC D + H) σ M N x y a b
        ≤ ∑ a ∈ S, rA D σ (ballChiA D H) M x a + ∑ b ∈ T, rB D σ (ballChiB D H) N y b) :=
  rectangle_interface_of_dc D (ball_decomp D hH) (ballU_orderedAB D h hH) (ballV_orderedBA D h hH)
    hσ (fun E H' hE hH' => ballDC_nonneg D h hσ.1 E H' hE hH') rfl (ballChiA_posSemidef D h hH)
    (ballChiA_trace D h hH) rfl (ballChiB_posSemidef D h hH) (ballChiB_trace D h hH) M N

/-- Rectangle data for `W_c + H` in the `hrect` shape of `ec_of_rectangles`. -/
theorem ball_rectangles (h : AllPortsGE2 D) {H : PMat D} (hH : InBall D H) :
    ∀ (r s nx ny na nb : ℕ) (σ : Op (Fin (r + 1) × Fin (s + 1))), Density σ →
      ∀ (M : Instrument (Fin D.m × Fin (r + 1)) (Fin D.d) (Fin (nx + 1)) (Fin (na + 1)))
        (N : Instrument (Fin D.n × Fin (s + 1)) (Fin D.e) (Fin (ny + 1)) (Fin (nb + 1))),
        ∃ (eA : Fin (nx + 1) → Fin (na + 1) → ℝ) (eB : Fin (ny + 1) → Fin (nb + 1) → ℝ),
          (∀ x a, 0 ≤ eA x a) ∧ (∀ y b, 0 ≤ eB y b) ∧
          (∀ x, ∑ a, eA x a = 1 / 2) ∧ (∀ y, ∑ b, eB y b = 1 / 2) ∧
          ∀ x y (S : Finset (Fin (na + 1))) (T : Finset (Fin (nb + 1))),
            (∑ a ∈ S, ∑ b ∈ T, bornExtended D (WcC D + H) σ M N x y a b) ≤
              (∑ a ∈ S, eA x a) + ∑ b ∈ T, eB y b := by
  intro r s nx ny na nb σ hσ M N
  obtain ⟨h1, h2, h3, h4, h5⟩ := ball_rectangle_interface D h hH hσ M N
  exact ⟨rA D σ (ballChiA D H) M, rB D σ (ballChiB D H) N, h1, h2, h3, h4, h5⟩

/-- Extensible causality throughout the closed ball by the **rectangle route**: the perturbed
process is again of the signed form `U' + V' + 2 Q_{C'}` (`ball_decomp`), so the generic
endpoint-array/transport argument of §5 applies verbatim.  The manuscript's own §7 argument is
`ball_extensiblyCausal_mixture` below, which is the primary proof (`ball_extensiblyCausal`). -/
theorem ball_extensiblyCausal_rect (h : AllPortsGE2 D) {H : PMat D} (hH : InBall D H) :
    ExtensiblyCausal D (WcC D + H) :=
  ec_of_rectangles (ball_valid h hH) (ball_rectangles D h hH)

/-- **"The final order weights are again `1/2, 1/2`"** (§7): for every finite extension the
Born distribution of `W_c + H` is half-causal — an equal mixture of an `A ≺ B` and a `B ≺ A`
no-signalling distribution — by the transport construction on the ball's rectangle data. -/
theorem ball_halfCausal (h : AllPortsGE2 D) {H : PMat D} (hH : InBall D H)
    {σ : Op (RA × RB)} (hσ : Density σ) (M : Instrument (Fin D.m × RA) (Fin D.d) X A)
    (N : Instrument (Fin D.n × RB) (Fin D.e) Y B) :
    HalfCausal (bornExtended D (WcC D + H) σ M N) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := ball_rectangle_interface D h hH hσ M N
  have hc := valid_born_extended D (ball_valid h hH) hσ M N
  exact halfCausal_of_rectangles _ _ _ hc.1 h1 h2 hc.2 h3 h4 h5

end BallEC

/-! ### Manuscript-scale statements (§7 verbatim: `eq:split-norm`, `eq:white-ordered`,
`eq:ball-mixture`) -/

section ManuscriptScale

variable (D : Ports)

theorem splitA_isHermitian {X : PMat D} (hX : X.IsHermitian) : (splitA D X).IsHermitian :=
  (R_BO_isHermitian hX).sub ((R_AO_isHermitian (R_BO_isHermitian hX)).smul isSelfAdjoint_half)

theorem splitB_isHermitian {X : PMat D} (hX : X.IsHermitian) : (splitB D X).IsHermitian :=
  (R_AO_isHermitian hX).sub ((R_AO_isHermitian (R_BO_isHermitian hX)).smul isSelfAdjoint_half)

theorem splitA_neg (X : PMat D) : splitA D (-X) = -splitA D X := by
  unfold splitA
  simp only [map_neg, smul_neg]
  abel

theorem splitB_neg (X : PMat D) : splitB D (-X) = -splitB D X := by
  unfold splitB
  simp only [map_neg, smul_neg]
  abel

theorem splitA_smul (c : ℂ) (X : PMat D) : splitA D (c • X) = c • splitA D X := by
  unfold splitA
  simp only [map_smul]
  module

theorem splitB_smul (c : ℂ) (X : PMat D) : splitB D (c • X) = c • splitB D X := by
  unfold splitB
  simp only [map_smul]
  module

/-- **`eq:split-norm`**: `‖X_A‖_∞ ≤ (3/2) ‖X‖_∞` for Hermitian `X` ("positivity and unitality of
replacement imply contraction in operator norm"), via the PSD bounds `splitA_psd` and
`opNorm_le_iff_psd_bounds`. -/
theorem splitA_opNorm_le {X : PMat D} (hX : X.IsHermitian) :
    opNorm (splitA D X) ≤ 3 / 2 * opNorm X := by
  have hr : 0 ≤ opNorm X := opNorm_nonneg X
  obtain ⟨h1, h2⟩ := psd_bounds_of_opNorm_le hX hr le_rfl
  have hp := splitA_psd D h1 h2
  have hn := splitA_psd D (X := -X) (by rw [← sub_eq_add_neg]; exact h2)
    (by rw [sub_neg_eq_add]; exact h1)
  rw [splitA_neg] at hn
  have e : ((3 / 2 * opNorm X : ℝ) : ℂ) = (opNorm X : ℂ) + (opNorm X : ℂ) / 2 := by
    push_cast; ring
  refine (opNorm_le_iff_psd_bounds (splitA_isHermitian D hX)
    (mul_nonneg (by norm_num) hr)).mpr ⟨?_, ?_⟩
  · rw [e]; exact hp
  · rw [e, sub_eq_add_neg]; exact hn

theorem splitB_opNorm_le {X : PMat D} (hX : X.IsHermitian) :
    opNorm (splitB D X) ≤ 3 / 2 * opNorm X := by
  have hr : 0 ≤ opNorm X := opNorm_nonneg X
  obtain ⟨h1, h2⟩ := psd_bounds_of_opNorm_le hX hr le_rfl
  have hp := splitB_psd D h1 h2
  have hn := splitB_psd D (X := -X) (by rw [← sub_eq_add_neg]; exact h2)
    (by rw [sub_neg_eq_add]; exact h1)
  rw [splitB_neg] at hn
  have e : ((3 / 2 * opNorm X : ℝ) : ℂ) = (opNorm X : ℂ) + (opNorm X : ℂ) / 2 := by
    push_cast; ring
  refine (opNorm_le_iff_psd_bounds (splitB_isHermitian D hX)
    (mul_nonneg (by norm_num) hr)).mpr ⟨?_, ?_⟩
  · rw [e]; exact hp
  · rw [e, sub_eq_add_neg]; exact hn

lemma white_scalar_isSelfAdjoint : IsSelfAdjoint (1 / ((D.m : ℂ) * D.n) / 2) := by
  rw [show (1 / ((D.m : ℂ) * D.n) / 2) = ((1 / (D.m * D.n) / 2 : ℚ) : ℂ) by push_cast; ring]
  exact isSelfAdjoint_ratCast _

/-- `I/(2mn) + X_A ≥ 0` whenever `‖X‖_∞ ≤ 1/(3mn)` (`eq:white-ordered`, positivity). -/
theorem white_ordered_psd_A {X : PMat D} (hX : X.IsHermitian)
    (hnorm : opNorm X ≤ 1 / (3 * D.m * D.n)) :
    ((1 / ((D.m : ℂ) * D.n) / 2) • (1 : PMat D) + splitA D X).PosSemidef := by
  have hr : (0 : ℝ) ≤ 1 / (3 * D.m * D.n) := by positivity
  obtain ⟨h1, h2⟩ := psd_bounds_of_opNorm_le hX hr hnorm
  have e : (1 / ((D.m : ℂ) * D.n) / 2)
      = ((1 / (3 * D.m * D.n) : ℝ) : ℂ) + ((1 / (3 * D.m * D.n) : ℝ) : ℂ) / 2 := by
    push_cast; ring
  rw [e]
  exact splitA_psd D h1 h2

theorem white_ordered_psd_B {X : PMat D} (hX : X.IsHermitian)
    (hnorm : opNorm X ≤ 1 / (3 * D.m * D.n)) :
    ((1 / ((D.m : ℂ) * D.n) / 2) • (1 : PMat D) + splitB D X).PosSemidef := by
  have hr : (0 : ℝ) ≤ 1 / (3 * D.m * D.n) := by positivity
  obtain ⟨h1, h2⟩ := psd_bounds_of_opNorm_le hX hr hnorm
  have e : (1 / ((D.m : ℂ) * D.n) / 2)
      = ((1 / (3 * D.m * D.n) : ℝ) : ℂ) + ((1 / (3 * D.m * D.n) : ℝ) : ℂ) / 2 := by
    push_cast; ring
  rw [e]
  exact splitB_psd D h1 h2

/-- **`eq:white-ordered`, Alice's summand**: for `X ∈ L_V` with `‖X‖_∞ ≤ 1/(3mn)`,
`I/(2mn) + X_A ∈ O_{A≺B}`. -/
theorem white_ordered_A {X : PMat D} (hX : InLV D X) (hnorm : opNorm X ≤ 1 / (3 * D.m * D.n)) :
    OrderedAB D ((1 / ((D.m : ℂ) * D.n) / 2) • (1 : PMat D) + splitA D X) :=
  ⟨genLV_add (genLV_smul (white_scalar_isSelfAdjoint D) genLV_one) (splitA_inLV D hX),
    white_ordered_psd_A D hX.1 hnorm, by rw [map_add, map_smul, R_BO_one, R_BO_splitA]⟩

/-- **`eq:white-ordered`, Bob's summand**: `I/(2mn) + X_B ∈ O_{B≺A}`. -/
theorem white_ordered_B {X : PMat D} (hX : InLV D X) (hnorm : opNorm X ≤ 1 / (3 * D.m * D.n)) :
    OrderedBA D ((1 / ((D.m : ℂ) * D.n) / 2) • (1 : PMat D) + splitB D X) :=
  ⟨genLV_add (genLV_smul (white_scalar_isSelfAdjoint D) genLV_one) (splitB_inLV D hX),
    white_ordered_psd_B D hX.1 hnorm, by rw [map_add, map_smul, R_AO_one, R_AO_splitB]⟩

/-- **`eq:white-ordered`, the identity**: `I/(mn) + X = (I/(2mn) + X_A) + (I/(2mn) + X_B)` for
`X ∈ L_V` (`eq:LV-c` gives `X_A + X_B = X`). -/
theorem white_ordered_sum {X : PMat D} (hX : InLV D X) :
    (1 / ((D.m : ℂ) * D.n)) • (1 : PMat D) + X
      = ((1 / ((D.m : ℂ) * D.n) / 2) • (1 : PMat D) + splitA D X)
        + ((1 / ((D.m : ℂ) * D.n) / 2) • (1 : PMat D) + splitB D X) := by
  conv_lhs => rw [← splitA_add_splitB D hX]
  module

/-- "Both summands … have trace `de/2`" (`eq:white-ordered`), Alice's summand. -/
theorem white_ordered_trace_A {X : PMat D} (htr : X.trace = 0) :
    ((1 / ((D.m : ℂ) * D.n) / 2) • (1 : PMat D) + splitA D X).trace = (D.d : ℂ) * D.e / 2 := by
  have hm : (D.m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr D.m_ne_zero
  have hn : (D.n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr D.n_ne_zero
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, trace_splitA D htr, add_zero,
    smul_eq_mul]
  simp only [Fintype.card_prod, Fintype.card_fin]
  push_cast
  field_simp

theorem white_ordered_trace_B {X : PMat D} (htr : X.trace = 0) :
    ((1 / ((D.m : ℂ) * D.n) / 2) • (1 : PMat D) + splitB D X).trace = (D.d : ℂ) * D.e / 2 := by
  have hm : (D.m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr D.m_ne_zero
  have hn : (D.n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr D.n_ne_zero
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, trace_splitB D htr, add_zero,
    smul_eq_mul]
  simp only [Fintype.card_prod, Fintype.card_fin]
  push_cast
  field_simp

/-- The ball's `T_A/100` (`ballTA`) is the manuscript's `T_A` of `eq:white-ordered` at
`X = 100 H`, divided by `100`. -/
theorem ballTA_eq (H : PMat D) :
    ballTA D H
      = (1 / 100 : ℂ) • ((1 / ((D.m : ℂ) * D.n) / 2) • (1 : PMat D) + splitA D ((100 : ℂ) • H)) := by
  unfold ballTA
  rw [splitA_smul]
  module

theorem ballTB_eq (H : PMat D) :
    ballTB D H
      = (1 / 100 : ℂ) • ((1 / ((D.m : ℂ) * D.n) / 2) • (1 : PMat D) + splitB D ((100 : ℂ) • H)) := by
  unfold ballTB
  rw [splitB_smul]
  module

/-- **`eq:ball-mixture` verbatim**: `W_c + H = (99/100) W_0 + (1/100)(I/(mn) + 100 H)`. -/
theorem ball_mixture (H : PMat D) :
    WcC D + H
      = (99 / 100 : ℂ) • toC (W0 D.m D.d D.n D.e)
        + (1 / 100 : ℂ) • ((1 / ((D.m : ℂ) * D.n)) • (1 : PMat D) + (100 : ℂ) • H) := by
  rw [WcC_eq]
  push_cast
  module

end ManuscriptScale

/-! ### Mixtures of half-causal and one-way distributions (distribution level) -/

section Mixture

variable {X Y A B : Type} [Fintype A] [Fintype B]

/-- **Mixing lemma** (§7, "mix the two components `eq:causal-components` with the normalized
ordered distributions … in weights `99/100, 1/100`; the final order weights are again `1/2, 1/2`"):
if `p = ½ p^{AB} + ½ p^{BA}` is half-causal and `q = ½ q_A + ½ q_B` with `q_A` (resp. `q_B`) a
normalized `A≺B` (resp. `B≺A`) no-signalling distribution, then for `α, β ≥ 0`, `α + β = 1`,
`α p + β q = ½[α p^{AB} + β q_A] + ½[α p^{BA} + β q_B]` is half-causal. -/
theorem halfCausal_mix {p q : Prob X Y A B} {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hαβ : α + β = 1) (hp : HalfCausal p) (qA qB : Prob X Y A B)
    (hqA : Conditional qA ∧ NS_AB qA) (hqB : Conditional qB ∧ NS_BA qB)
    (hq : ∀ x y a b, q x y a b = (1 / 2) * qA x y a b + (1 / 2) * qB x y a b) :
    HalfCausal (fun x y a b => α * p x y a b + β * q x y a b) := by
  obtain ⟨pAB, pBA, hAB, hBA, nsAB, nsBA, hpeq⟩ := hp
  refine ⟨fun x y a b => α * pAB x y a b + β * qA x y a b,
    fun x y a b => α * pBA x y a b + β * qB x y a b, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro x y a b
    exact add_nonneg (mul_nonneg hα (hAB.1 x y a b)) (mul_nonneg hβ (hqA.1.1 x y a b))
  · intro x y
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hAB.2 x y, hqA.1.2 x y, mul_one, mul_one, hαβ]
  · intro x y a b
    exact add_nonneg (mul_nonneg hα (hBA.1 x y a b)) (mul_nonneg hβ (hqB.1.1 x y a b))
  · intro x y
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hBA.2 x y, hqB.1.2 x y, mul_one, mul_one, hαβ]
  · intro x y y' a
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [nsAB x y y' a, hqA.2 x y y' a]
  · intro x x' y b
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [nsBA x x' y b, hqB.2 x x' y b]
  · intro x y a b
    simp only [hpeq x y a b, hq x y a b]
    ring

end Mixture

/-! ### The manuscript's proof of extensible causality on the ball (§7, paper.tex l. 933–943) -/

section PaperRoute

variable (D : Ports) {RA RB : Type} [Fintype RA] [Fintype RB] [DecidableEq RA] [DecidableEq RB]

/-- "Each ordered summand in `eq:white-ordered` remains ordered under every shared-input
extension" (§7): for `T ∈ O_{A≺B}` and a positive Hermitian shared state `σ`, the extension
`T ⊗ σ` lies in `L_V`, is positive, and is `R_{B_O}`-invariant. -/
theorem ordered_extended_A {T : PMat D} (hT : OrderedAB D T) {σ : Op (RA × RB)}
    (hσ : σ.PosSemidef) (hσh : σ.IsHermitian) :
    GenLV (extended T σ) ∧ (extended T σ).PosSemidef ∧ R_BO (extended T σ) = extended T σ :=
  ⟨GenLV.extended hT.1 hσh, posSemidef_extended hT.2.1 hσ, by rw [R_BO_extended, hT.2.2]⟩

/-- The `B ≺ A` counterpart of `ordered_extended_A`. -/
theorem ordered_extended_B {T : PMat D} (hT : OrderedBA D T) {σ : Op (RA × RB)}
    (hσ : σ.PosSemidef) (hσh : σ.IsHermitian) :
    GenLV (extended T σ) ∧ (extended T σ).PosSemidef ∧ R_AO (extended T σ) = extended T σ :=
  ⟨GenLV.extended hT.1 hσh, posSemidef_extended hT.2.1 hσ, by rw [R_AO_extended, hT.2.2]⟩

omit [DecidableEq RA] [DecidableEq RB] in
/-- Real scalars pass through the Born pairing. -/
theorem pT_ofReal_smul (r : ℝ) (T : PMat D) (σ : Op (RA × RB))
    (F : Op ((Fin D.m × RA) × Fin D.d)) (G : Op ((Fin D.n × RB) × Fin D.e)) :
    pT D ((r : ℂ) • T) σ F G = r * pT D T σ F G := by
  unfold pT
  rw [extendInput_smul', Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

variable {X Y A B : Type} [Fintype A] [Fintype B]

/-- The Born distribution of a positive process is nonnegative (`p_T ≥ 0`). -/
theorem pT_ordered_nonneg {T : PMat D} (hT : T.PosSemidef) {σ : Op (RA × RB)} (hσ : σ.PosSemidef)
    (M : Instrument (Fin D.m × RA) (Fin D.d) X A) (N : Instrument (Fin D.n × RB) (Fin D.e) Y B)
    (x : X) (y : Y) (a : A) (b : B) : 0 ≤ bornExtended D T σ M N x y a b :=
  bornExtended_nonneg D hT hσ M N x y a b

/-- **Total mass of the Born distribution of an `L_V` element**: `∑_{a,b} p_T(a,b|x,y) = Tr T/(de)`
(`GenLV.trace_mul_kronecker` on the extended `L_V` element); `= 1/2` for the white-ordered
summands, whose trace is `de/2`. -/
theorem pT_ordered_mass {T : PMat D} (hT : InLV D T) {σ : Op (RA × RB)} (hσ : Density σ)
    (M : Instrument (Fin D.m × RA) (Fin D.d) X A) (N : Instrument (Fin D.n × RB) (Fin D.e) Y B)
    (x : X) (y : Y) :
    ∑ a, ∑ b, bornExtended D T σ M N x y a b = (T.trace / ((D.d : ℂ) * D.e)).re := by
  rw [bornExtended_sum]
  have hLV : GenLV (extendInput D T σ) := GenLV.extended hT hσ.1.1
  rw [GenLV.trace_mul_kronecker hLV (M.normalized x) (N.normalized y), extendInput_trace, hσ.2,
    mul_one]
  congr 1
  simp only [invCard, Fintype.card_fin]
  ring

/-- Alice's marginal of the Born distribution of `T ∈ O_{A≺B}` is the ordered first-party marginal
`a_T(M_{a|x}) = Tr[(ω_A(T) ⊗ σ_{R_A}) E_{a|x}]`, independent of Bob's setting and of Bob's
instrument (`ordered_completed_pairing`). -/
theorem bornExtended_sum_b_ordered {T : PMat D} (hT : OrderedAB D T) (σ : Op (RA × RB))
    (M : Instrument (Fin D.m × RA) (Fin D.d) X A) (N : Instrument (Fin D.n × RB) (Fin D.e) Y B)
    (x : X) (y : Y) (a : A) :
    ∑ b, bornExtended D T σ M N x y a b = aU D T σ (M.elem x a) := by
  have h := pT_coarse D T σ M N x y {a} Finset.univ
  rw [Finset.sum_singleton] at h
  rw [h]
  unfold pT aU
  rw [completed_pairing_A D hT σ _ (ptraceOut_coarse_univ N y)]
  simp only [coarse, Finset.sum_singleton]

/-- Bob's marginal of the Born distribution of `T ∈ O_{B≺A}` is `b_T(N_{b|y})`, independent of
Alice's setting and instrument. -/
theorem bornExtended_sum_a_ordered {T : PMat D} (hT : OrderedBA D T) (σ : Op (RA × RB))
    (M : Instrument (Fin D.m × RA) (Fin D.d) X A) (N : Instrument (Fin D.n × RB) (Fin D.e) Y B)
    (x : X) (y : Y) (b : B) :
    ∑ a, bornExtended D T σ M N x y a b = bV D T σ (N.elem y b) := by
  have h := pT_coarse D T σ M N x y Finset.univ {b}
  simp only [Finset.sum_singleton] at h
  rw [h]
  unfold pT bV
  rw [completed_pairing_B D hT σ _ (ptraceOut_coarse_univ M x)]
  simp only [coarse, Finset.sum_singleton]

/-- **`A ≺ B` no-signalling of ordered Born distributions**: for `T ∈ O_{A≺B}` and every shared
state and instruments, `∑_b p_T(a,b|x,y)` does not depend on `y`. -/
theorem pT_ordered_nsAB {T : PMat D} (hT : OrderedAB D T) (σ : Op (RA × RB))
    (M : Instrument (Fin D.m × RA) (Fin D.d) X A) (N : Instrument (Fin D.n × RB) (Fin D.e) Y B) :
    NS_AB (bornExtended D T σ M N) := fun x y y' a => by
  rw [bornExtended_sum_b_ordered D hT σ M N x y a, bornExtended_sum_b_ordered D hT σ M N x y' a]

/-- **`B ≺ A` no-signalling of ordered Born distributions**. -/
theorem pT_ordered_nsBA {T : PMat D} (hT : OrderedBA D T) (σ : Op (RA × RB))
    (M : Instrument (Fin D.m × RA) (Fin D.d) X A) (N : Instrument (Fin D.n × RB) (Fin D.e) Y B) :
    NS_BA (bornExtended D T σ M N) := fun x x' y b => by
  rw [bornExtended_sum_a_ordered D hT σ M N x y b, bornExtended_sum_a_ordered D hT σ M N x' y b]

/-- "The normalized ordered distributions `2 p_{T_A}`" (§7): for `T ∈ O_{A≺B}` of trace `de/2`,
`2 p_T` is a normalized `A ≺ B` no-signalling distribution. -/
theorem twice_ordered_A {T : PMat D} (hT : OrderedAB D T) (htr : T.trace = (D.d : ℂ) * D.e / 2)
    {σ : Op (RA × RB)} (hσ : Density σ) (M : Instrument (Fin D.m × RA) (Fin D.d) X A)
    (N : Instrument (Fin D.n × RB) (Fin D.e) Y B) :
    Conditional (fun x y a b => 2 * bornExtended D T σ M N x y a b) ∧
      NS_AB (fun x y a b => 2 * bornExtended D T σ M N x y a b) := by
  have hd : (D.d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr D.d_ne_zero
  have he : (D.e : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr D.e_ne_zero
  have hhalf : T.trace / ((D.d : ℂ) * D.e) = ((1 / 2 : ℝ) : ℂ) := by
    rw [htr]; push_cast; field_simp
  refine ⟨⟨fun x y a b => mul_nonneg (by norm_num) (bornExtended_nonneg D hT.2.1 hσ.1 M N x y a b),
    fun x y => ?_⟩, fun x y y' a => ?_⟩
  · simp only [← Finset.mul_sum]
    rw [pT_ordered_mass D hT.1 hσ M N x y, hhalf, Complex.ofReal_re]
    norm_num
  · simp only [← Finset.mul_sum, bornExtended_sum_b_ordered D hT σ M N x y a,
      bornExtended_sum_b_ordered D hT σ M N x y' a]

/-- "The normalized ordered distributions `2 p_{T_B}`" (§7): the `B ≺ A` counterpart. -/
theorem twice_ordered_B {T : PMat D} (hT : OrderedBA D T) (htr : T.trace = (D.d : ℂ) * D.e / 2)
    {σ : Op (RA × RB)} (hσ : Density σ) (M : Instrument (Fin D.m × RA) (Fin D.d) X A)
    (N : Instrument (Fin D.n × RB) (Fin D.e) Y B) :
    Conditional (fun x y a b => 2 * bornExtended D T σ M N x y a b) ∧
      NS_BA (fun x y a b => 2 * bornExtended D T σ M N x y a b) := by
  have hd : (D.d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr D.d_ne_zero
  have he : (D.e : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr D.e_ne_zero
  have hhalf : T.trace / ((D.d : ℂ) * D.e) = ((1 / 2 : ℝ) : ℂ) := by
    rw [htr]; push_cast; field_simp
  refine ⟨⟨fun x y a b => mul_nonneg (by norm_num) (bornExtended_nonneg D hT.2.1 hσ.1 M N x y a b),
    fun x y => ?_⟩, fun x x' y b => ?_⟩
  · simp only [← Finset.mul_sum]
    rw [pT_ordered_mass D hT.1 hσ M N x y, hhalf, Complex.ofReal_re]
    norm_num
  · simp only [← Finset.mul_sum, bornExtended_sum_a_ordered D hT σ M N x y b,
      bornExtended_sum_a_ordered D hT σ M N x' y b]

/-! #### The manuscript's `T_A`, `T_B` (`eq:white-ordered` at `X = 100 H`) -/

/-- Manuscript `T_A = I/(2mn) + X_A` with `X = 100 H` (`eq:white-ordered`). -/
def whiteA (H : PMat D) : PMat D :=
  (1 / ((D.m : ℂ) * D.n) / 2) • (1 : PMat D) + splitA D ((100 : ℂ) • H)

/-- Manuscript `T_B = I/(2mn) + X_B` with `X = 100 H` (`eq:white-ordered`). -/
def whiteB (H : PMat D) : PMat D :=
  (1 / ((D.m : ℂ) * D.n) / 2) • (1 : PMat D) + splitB D ((100 : ℂ) • H)

theorem whiteA_eq (H : PMat D) : whiteA D H = (100 : ℂ) • ballTA D H := by
  unfold whiteA ballTA
  rw [splitA_smul]
  module

theorem whiteB_eq (H : PMat D) : whiteB D H = (100 : ℂ) • ballTB D H := by
  unfold whiteB ballTB
  rw [splitB_smul]
  module

lemma isSelfAdjoint_hundred : IsSelfAdjoint (100 : ℂ) := by
  rw [show (100 : ℂ) = ((100 : ℚ) : ℂ) by norm_num]
  exact isSelfAdjoint_ratCast _

/-- `T_A ∈ O_{A≺B}` (`eq:white-ordered`, "`T_A ∈ O_{A≺B}`"). -/
theorem whiteA_orderedAB {H : PMat D} (hH : InBall D H) : OrderedAB D (whiteA D H) := by
  rw [whiteA_eq, show (100 : ℂ) = ((100 : ℚ) : ℂ) by norm_num]
  exact orderedAB_ratSmul D (by norm_num) (ballTA_orderedAB D hH)

/-- `T_B ∈ O_{B≺A}` (`eq:white-ordered`). -/
theorem whiteB_orderedBA {H : PMat D} (hH : InBall D H) : OrderedBA D (whiteB D H) := by
  rw [whiteB_eq, show (100 : ℂ) = ((100 : ℚ) : ℂ) by norm_num]
  exact orderedBA_ratSmul D (by norm_num) (ballTB_orderedBA D hH)

/-- "Both summands … have trace `de/2`" (§7). -/
theorem whiteA_trace {H : PMat D} (hH : InBall D H) : (whiteA D H).trace = (D.d : ℂ) * D.e / 2 :=
  white_ordered_trace_A D (by rw [Matrix.trace_smul, hH.2.1, smul_zero])

theorem whiteB_trace {H : PMat D} (hH : InBall D H) : (whiteB D H).trace = (D.d : ℂ) * D.e / 2 :=
  white_ordered_trace_B D (by rw [Matrix.trace_smul, hH.2.1, smul_zero])

/-- `eq:white-ordered` applied to `X = 100 H`: `I/(mn) + 100 H = T_A + T_B`. -/
theorem whiteA_add_whiteB {H : PMat D} (hH : InBall D H) :
    (1 / ((D.m : ℂ) * D.n)) • (1 : PMat D) + (100 : ℂ) • H = whiteA D H + whiteB D H :=
  white_ordered_sum D (genLV_smul isSelfAdjoint_hundred hH.1)

/-- `eq:ball-mixture` combined with `eq:white-ordered`:
`W_c + H = (99/100) W_0 + (1/100)(T_A + T_B)`. -/
theorem ball_mixture_white {H : PMat D} (hH : InBall D H) :
    WcC D + H
      = (99 / 100 : ℂ) • toC (W0 D.m D.d D.n D.e) + (1 / 100 : ℂ) • (whiteA D H + whiteB D H) := by
  rw [ball_mixture, whiteA_add_whiteB D hH]

/-- **`eq:ball-mixture` at the level of distributions**: the Born rule is linear in the process, so
`p_{W_c+H} = (99/100) p_{W_0} + (1/100)(p_{T_A} + p_{T_B})` for every shared state and instruments. -/
theorem bornExtended_ball_decomp {H : PMat D} (hH : InBall D H) (σ : Op (RA × RB))
    (M : Instrument (Fin D.m × RA) (Fin D.d) X A) (N : Instrument (Fin D.n × RB) (Fin D.e) Y B)
    (x : X) (y : Y) (a : A) (b : B) :
    bornExtended D (WcC D + H) σ M N x y a b
      = 99 / 100 * bornExtended D (toC (W0 D.m D.d D.n D.e)) σ M N x y a b
        + 1 / 100 * (bornExtended D (whiteA D H) σ M N x y a b
          + bornExtended D (whiteB D H) σ M N x y a b) := by
  simp only [bornExtended_eq_pT]
  rw [ball_mixture_white D hH, pT_add_process,
    show (99 / 100 : ℂ) = ((99 / 100 : ℝ) : ℂ) by norm_num,
    show (1 / 100 : ℂ) = ((1 / 100 : ℝ) : ℂ) by norm_num,
    pT_ofReal_smul, pT_ofReal_smul, pT_add_process]

variable [DecidableEq A] [DecidableEq B]

/-- The causal components `eq:causal-components` of `W_0`: for every finite extension,
`p_{W_0} = ½ p^{A≺B} + ½ p^{B≺A}` (the §5 transport construction on `rectangles_W0`). -/
theorem w0_halfCausal (h : AllPortsGE2 D) {σ : Op (RA × RB)} (hσ : Density σ)
    (M : Instrument (Fin D.m × RA) (Fin D.d) X A) (N : Instrument (Fin D.n × RB) (Fin D.e) Y B) :
    HalfCausal (bornExtended D (toC (W0 D.m D.d D.n D.e)) σ M N) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rectangle_interface_W0 D h hσ M N
  have hc := valid_born_extended D (w0_valid (D := D) h) hσ M N
  exact halfCausal_of_rectangles _ _ _ hc.1 h1 h2 hc.2 h3 h4 h5

/-- **The manuscript's proof** (§7, l. 933–943): "each ordered summand in `eq:white-ordered`
remains ordered under every shared-input extension. For an explicit distribution decomposition,
mix the two components `eq:causal-components` with the normalized ordered distributions `2p_{T_A}`
and `2p_{T_B}`, respectively, in weights `99/100, 1/100`. The final order weights are again
`1/2, 1/2`." -/
theorem ball_halfCausal_mixture (h : AllPortsGE2 D) {H : PMat D} (hH : InBall D H)
    {σ : Op (RA × RB)} (hσ : Density σ) (M : Instrument (Fin D.m × RA) (Fin D.d) X A)
    (N : Instrument (Fin D.n × RB) (Fin D.e) Y B) :
    HalfCausal (bornExtended D (WcC D + H) σ M N) := by
  have hdec : bornExtended D (WcC D + H) σ M N
      = fun x y a b => 99 / 100 * bornExtended D (toC (W0 D.m D.d D.n D.e)) σ M N x y a b
        + 1 / 100 * (bornExtended D (whiteA D H) σ M N x y a b
          + bornExtended D (whiteB D H) σ M N x y a b) := by
    funext x y a b
    exact bornExtended_ball_decomp D hH σ M N x y a b
  rw [hdec]
  exact halfCausal_mix (p := bornExtended D (toC (W0 D.m D.d D.n D.e)) σ M N)
    (q := fun x y a b => bornExtended D (whiteA D H) σ M N x y a b
      + bornExtended D (whiteB D H) σ M N x y a b)
    (by norm_num) (by norm_num) (by norm_num) (w0_halfCausal D h hσ M N)
    (fun x y a b => 2 * bornExtended D (whiteA D H) σ M N x y a b)
    (fun x y a b => 2 * bornExtended D (whiteB D H) σ M N x y a b)
    (twice_ordered_A D (whiteA_orderedAB D hH) (whiteA_trace D hH) hσ M N)
    (twice_ordered_B D (whiteB_orderedBA D hH) (whiteB_trace D hH) hσ M N)
    (fun x y a b => by ring)

end PaperRoute

section BallMain

variable (D : Ports)

/-- **Extensible causality throughout the closed ball by the manuscript's argument**
(`thm:main` (ii), §7): validity from `ball_valid` and, for every finite extension, the
half-causal mixture `ball_halfCausal_mixture`. -/
theorem ball_extensiblyCausal_mixture (h : AllPortsGE2 D) {H : PMat D} (hH : InBall D H) :
    ExtensiblyCausal D (WcC D + H) :=
  ⟨ball_valid h hH, fun _ _ _ _ _ _ _ hσ M N =>
    halfCausal_causal (ball_halfCausal_mixture D h hH hσ M N)⟩

/-- **Extensible causality throughout the closed ball** (`thm:main` (ii), §7, `eq:ball-mixture`):
for all ports `≥ 2` and every `H` with `H ∈ L_V`, `Tr H = 0`, `‖H‖_∞ ≤ 1/(300mn)` (PSD form),
`W_c + H` is extensibly causal.  Primary proof: the manuscript's mixture argument
(`ball_extensiblyCausal_mixture`); the rectangle route is `ball_extensiblyCausal_rect`. -/
theorem ball_extensiblyCausal (h : AllPortsGE2 D) {H : PMat D} (hH : InBall D H) :
    ExtensiblyCausal D (WcC D + H) :=
  ball_extensiblyCausal_mixture D h hH

/-- `ball_extensiblyCausal` with the center spelled out as `toC W_c`. -/
theorem ball_extensiblyCausal' (h : AllPortsGE2 D) {H : PMat D} (hH : InBall D H) :
    ExtensiblyCausal D (toC (Wc D.m D.d D.n D.e) + H) :=
  ball_extensiblyCausal D h hH

end BallMain

end

end CausalNonpurifiability
