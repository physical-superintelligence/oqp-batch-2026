module

public import CausalNonpurifiability.Definitions.ProcessCore
public import CausalNonpurifiability.Linear.Replacement

@[expose] public section


/-!
# `CausalNonpurifiability.Definitions.Process`

Process matrices: the three homogeneous equations `GenLV`/`InLV` (`eq:LV-a,b,c`, with
Hermiticity), normalized validity `Valid` (`eq:valid`), the subnormalized ordered
cones `OrderedAB`/`OrderedBA` (`eq:ordered-cones`), `CausallySeparable`, the input
embedding `QC` (`eq:QC`, by its entries), the ordered marginals
`omegaA`/`omegaB` and the `B_O`-stripped operator `hatAB` with the marginal identity
`ordered_marginal` (`eq:ordered-marginal`), and the ancilla-extension lemma
`GenLV.extended` (paragraph after `eq:valid`).

`GenLV` is generic in the four finite factor types; `InLV D`, `Valid D`,
`OrderedAB D`, … are its `Fin`-coordinate interface on `PMat D`.

Manuscript anchors: `eq:LV`, `eq:valid`, `eq:ordered-cones`, `eq:ordered-marginal`,
`eq:QC`.

Conventions: all three `eq:LV` equations in the replacement forms
`(1-R_AO) R_BIBO T = 0`, `(1-R_BO) R_AIAO T = 0`, `(1-R_AO)(1-R_BO) T = 0`; the
ordered cones carry no trace normalization.
-/

set_option autoImplicit false

open scoped Kronecker ComplexOrder

namespace CausalNonpurifiability

noncomputable section

/-! ### Generic homogeneous process equations -/

section GenLV

variable {AI AO BI BO : Type} [Fintype AI] [Fintype AO] [Fintype BI] [Fintype BO]
  [DecidableEq AI] [DecidableEq AO] [DecidableEq BI] [DecidableEq BO]

variable {RA RB : Type} [Fintype RA] [Fintype RB] [DecidableEq RA] [DecidableEq RB]

/-- Validity includes arbitrary shared-input extensions (paragraph after `eq:valid`):
`W ∈ L_V` and `σ` Hermitian give `W ⊗ σ ∈ L_V` on the enlarged inputs — the output
replacements act on `W`, the input partial traces factor through `σ`. -/
theorem GenLV.extended {W : Op (LabIdx AI AO BI BO)} (hW : GenLV W) {σ : Op (RA × RB)}
    (hσ : σ.IsHermitian) : GenLV (extended W σ) := by
  obtain ⟨hH, ha, hb, hc⟩ := hW
  refine ⟨extended_isHermitian hH hσ, ?_, ?_, ?_⟩
  · rw [R_BIBO_extended, R_AO_extended, ← extended_sub, ha, extended_zero]
  · rw [R_AIAO_extended, R_BO_extended, ← extended_sub, hb, extended_zero]
  · rw [R_AO_extended, R_BO_extended, R_AO_extended, ← extended_sub, ← extended_sub,
      ← extended_add, hc, extended_zero]

end GenLV

/-! ### `Fin`-coordinate interface -/

variable (D : Ports)

theorem InLV.isHermitian {W : PMat D} (h : InLV D W) : W.IsHermitian := h.1
theorem InLV.lv_a {W : PMat D} (h : InLV D W) : R_BIBO W - R_AO (R_BIBO W) = 0 := h.2.1
theorem InLV.lv_b {W : PMat D} (h : InLV D W) : R_AIAO W - R_BO (R_AIAO W) = 0 := h.2.2.1
theorem InLV.lv_c {W : PMat D} (h : InLV D W) : W - R_AO W - R_BO W + R_AO (R_BO W) = 0 :=
  h.2.2.2

/-! ### The input embedding `Q_C` -/

theorem QC_apply (C : Op (Fin D.m × Fin D.n)) (a a' : Fin D.m) (o o' : Fin D.d) (b b' : Fin D.n)
    (t t' : Fin D.e) :
    QC D C ((a, o), (b, t)) ((a', o'), (b', t')) =
      C (a, b) (a', b') * (if o = o' ∧ t = t' then 1 else 0) := rfl

/-- `Q_C` in Kronecker form: `Q_C = reindex eqQC (C ⊗ I_{A_O B_O})` (`eq:QC`). -/
theorem QC_eq_reindex_kronecker (C : Op (Fin D.m × Fin D.n)) :
    QC D C = Matrix.reindex (eqQC _ _ _ _) (eqQC _ _ _ _) (C ⊗ₖ (1 : Op (Fin D.d × Fin D.e))) := by
  ext ⟨⟨a, o⟩, ⟨b, t⟩⟩ ⟨⟨a', o'⟩, ⟨b', t'⟩⟩
  simp only [QC_apply, Matrix.reindex_apply, Matrix.submatrix_apply, eqQC_symm_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.mk.injEq]

/-! ### Ordered marginals -/

theorem omegaA_apply (T : PMat D) (a a' : Fin D.m) :
    omegaA D T a a' =
      (((D.d * D.e : ℕ) : ℂ))⁻¹ * ∑ o, ∑ b, ∑ t, T ((a, o), (b, t)) ((a', o), (b, t)) := by
  simp only [omegaA, Matrix.smul_apply, smul_eq_mul, ptraceOut_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply, Fintype.sum_prod_type, eqAI_symm_apply]

theorem omegaB_apply (T : PMat D) (b b' : Fin D.n) :
    omegaB D T b b' =
      (((D.d * D.e : ℕ) : ℂ))⁻¹ * ∑ a, ∑ o, ∑ t, T ((a, o), (b, t)) ((a, o), (b', t)) := by
  simp only [omegaB, Matrix.smul_apply, smul_eq_mul, ptraceOut_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply, Fintype.sum_prod_type, eqBI_symm_apply]

theorem hatAB_apply (T : PMat D) (a a' : Fin D.m) (o o' : Fin D.d) (b b' : Fin D.n) :
    hatAB D T ((a, o), b) ((a', o'), b') =
      ((D.e : ℂ))⁻¹ * ∑ t, T ((a, o), (b, t)) ((a', o'), (b', t)) := by
  simp only [hatAB, Matrix.smul_apply, smul_eq_mul, ptraceOut_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply, eqBO_symm_apply]

/-- For `R_{B_O} T = T` the process factorizes as `T = T̂ ⊗ I_{B_O}` (first identity of
`eq:ordered-marginal`). -/
theorem eq_hatAB_kronecker {T : PMat D} (h : R_BO T = T) :
    T = Matrix.reindex (eqBO _ _ _ _).symm (eqBO _ _ _ _).symm
      (hatAB D T ⊗ₖ (1 : Op (Fin D.e))) := by
  conv_lhs => rw [← h]
  rw [R_BO, replaceVia_apply, replaceLast, hatAB, Matrix.smul_kronecker, invCard,
    Fintype.card_fin]

/-- The entry form of `eq:LV-a` used for the ordered marginal: for every `a a' o o'`,
`∑_{b,t} T_{(a,o,b,t),(a',o',b,t)} = δ_{oo'} (1/d) ∑_{u,b,t} T_{(a,u,b,t),(a',u,b,t)}`. -/
theorem LVa_entry {T : PMat D} (hLVa : R_BIBO T - R_AO (R_BIBO T) = 0)
    (a a' : Fin D.m) (o o' : Fin D.d) :
    ∑ b, ∑ t, T ((a, o), (b, t)) ((a', o'), (b, t)) =
      if o = o' then
        ((D.d : ℂ))⁻¹ * ∑ u, ∑ b, ∑ t, T ((a, u), (b, t)) ((a', u), (b, t))
      else 0 := by
  have hc : invCard (Fin D.n × Fin D.e) ≠ 0 := invCard_ne_zero _
  have key := congrFun (congrFun hLVa ((a, o), (⟨0, D.n_pos⟩, ⟨0, D.e_pos⟩)))
    ((a', o'), (⟨0, D.n_pos⟩, ⟨0, D.e_pos⟩))
  simp only [Matrix.sub_apply, Matrix.zero_apply, R_AO_apply, R_BIBO_apply,
    if_true, Fintype.sum_prod_type, sub_eq_zero] at key
  by_cases ho : o = o'
  · subst ho
    simp only [if_true] at key ⊢
    rw [← Finset.mul_sum, ← mul_left_comm] at key
    have key' := mul_left_cancel₀ hc key
    rw [key']
    simp only [invCard, Fintype.card_fin]
  · simp only [ho, if_false] at key ⊢
    rcases mul_eq_zero.mp key with h0 | h0
    · exact absurd h0 hc
    · exact h0

/-- `eq:ordered-marginal`: for `T ∈ O_{A≺B}`, `Tr_{B_I} T̂ = ω_A(T) ⊗ I_{A_O}`, with the
exact normalization `ω_A(T) = Tr_{A_O B_I B_O} T / (d·e)`. -/
theorem ordered_marginal {T : PMat D} (hT : OrderedAB D T) :
    ptraceOut (hatAB D T) = omegaA D T ⊗ₖ (1 : Op (Fin D.d)) := by
  obtain ⟨⟨-, hLVa, -, -⟩, -, -⟩ := hT
  ext ⟨a, o⟩ ⟨a', o'⟩
  rw [ptraceOut_apply, Matrix.kroneckerMap_apply, omegaA_apply, Matrix.one_apply]
  simp only [hatAB_apply]
  rw [← Finset.mul_sum, LVa_entry D hLVa a a' o o']
  by_cases ho : o = o'
  · subst ho
    simp only [if_true, mul_one]
    push_cast
    ring
  · simp only [ho, if_false, mul_zero]

/-! ### Completed-channel pairing (§5.3)

For `U ∈ O_{A≺B}` and Bob's *completed* channel (`Tr_{B_O} N_tot = I_{B_I R_B}`),
`Tr[(U ⊗ σ)(F ⊗ N_tot)] = Tr[(ω_A(U) ⊗ σ^{R_A}) E]` with `E = Tr_{A_O} F`, `σ^{R_A} = Tr_{R_B} σ`
(for `N' = ∑_b N_{b|y}`, `Tr_{B_O} N' = I_{B_I R_B}`, and
`eq:ordered-marginal` gives the equality). Symmetrically for `V ∈ O_{B≺A}`. -/

section CompletedPairing

variable {A O B T : Type} [Fintype A] [Fintype O] [Fintype B] [Fintype T]
  [DecidableEq A] [DecidableEq O] [DecidableEq B] [DecidableEq T]

/-- `R_{B_O}` of a Kronecker product acts on the second factor. -/
theorem kron_R_BO (M : Op (A × O)) (N : Op (B × T)) :
    R_BO (M ⊗ₖ N) = M ⊗ₖ replaceLast N := by
  ext ⟨⟨a, o⟩, ⟨b, t⟩⟩ ⟨⟨a', o'⟩, ⟨b', t'⟩⟩
  simp only [R_BO_apply, Matrix.kroneckerMap_apply, replaceLast_apply, ptraceOut_apply]
  by_cases h : t = t'
  · subst h
    simp only [if_true, Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => by ring
  · simp only [h, if_false, mul_zero]

/-- `R_{A_O}` of a Kronecker product acts on the first factor. -/
theorem kron_R_AO (M : Op (A × O)) (N : Op (B × T)) :
    R_AO (M ⊗ₖ N) = replaceLast M ⊗ₖ N := by
  ext ⟨⟨a, o⟩, ⟨b, t⟩⟩ ⟨⟨a', o'⟩, ⟨b', t'⟩⟩
  simp only [R_AO_apply, Matrix.kroneckerMap_apply, replaceLast_apply, ptraceOut_apply]
  by_cases h : o = o'
  · subst h
    simp only [if_true, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun z _ => by ring
  · simp only [h, if_false, zero_mul]

omit [Fintype B] in
/-- A completed channel (`Tr_O N = I`) is replaced by the normalized identity. -/
theorem replaceLast_of_ptraceOut_eq_one {N : Op (B × T)} (hN : ptraceOut N = 1) :
    replaceLast N = invCard T • (1 : Op (B × T)) := by
  unfold replaceLast
  rw [hN, Matrix.one_kronecker_one]

omit [DecidableEq T] in
/-- `Tr((I ⊗ N) B) = Tr(N · Tr_I B)`: first-factor version of `trace_kronecker_one_mul`. -/
theorem trace_one_kronecker_mul (N : Op T) (X : Op (B × T)) :
    (((1 : Op B) ⊗ₖ N) * X).trace = (N * ptraceFst X).trace := by
  have hK : ((1 : Op B) ⊗ₖ N) =
      Matrix.reindex (Equiv.prodComm B T).symm (Equiv.prodComm B T).symm (N ⊗ₖ (1 : Op B)) := by
    ext ⟨i, y⟩ ⟨j, y'⟩
    by_cases h : i = j <;>
      simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply, h]
  rw [hK, ptraceFst]
  conv_lhs => rw [← reindex_symm_reindex (Equiv.prodComm B T) X]
  rw [trace_reindex_mul, trace_kronecker_one_mul]

end CompletedPairing

section CompletedPairingPorts

variable {RA RB : Type} [Fintype RA] [Fintype RB] [DecidableEq RA] [DecidableEq RB]

omit [Fintype RA] [DecidableEq RA] [DecidableEq RB] in
/-- `Tr_{B_I R_B B_O}(U ⊗ σ) = e · (ω_A(U) ⊗ Tr_{R_B} σ) ⊗ I_{A_O}` from `eq:LV-a`
(`eq:ordered-marginal` on the extended process). -/
theorem ptraceOut_extended_of_lv_a {U : PMat D} (hLVa : R_BIBO U - R_AO (R_BIBO U) = 0)
    (σ : Op (RA × RB)) :
    ptraceOut (extended U σ) =
      (D.e : ℂ) • ((omegaA D U ⊗ₖ ptraceOut σ) ⊗ₖ (1 : Op (Fin D.d))) := by
  have hd : (D.d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 D.d_ne_zero
  have he : (D.e : ℂ) ≠ 0 := Nat.cast_ne_zero.2 D.e_ne_zero
  ext ⟨⟨ai, ra⟩, ao⟩ ⟨⟨ai', ra'⟩, ao'⟩
  simp only [ptraceOut_apply, extended_apply, Fintype.sum_prod_type, Matrix.smul_apply,
    smul_eq_mul, Matrix.kroneckerMap_apply, Matrix.one_apply, omegaA_apply]
  have hS : ∑ bi, ∑ rb, ∑ bo, U ((ai, ao), (bi, bo)) ((ai', ao'), (bi, bo)) * σ (ra, rb) (ra', rb)
      = (∑ bi, ∑ bo, U ((ai, ao), (bi, bo)) ((ai', ao'), (bi, bo))) *
          ∑ rb, σ (ra, rb) (ra', rb) := by
    rw [Finset.sum_mul_sum]
    simp only [Finset.sum_mul]
  rw [hS, LVa_entry D hLVa ai ai' ao ao']
  by_cases h : ao = ao'
  · subst h
    simp only [if_true, mul_one]
    push_cast
    field_simp
  · simp only [h, if_false, zero_mul, mul_zero]

/-- **Completed-channel pairing, Alice's order** (§5.3): for `U ∈ O_{A≺B}`, a shared state `σ`,
an arbitrary `F` on `A_I R_A A_O`, and Bob's completed channel `N_tot` (`Tr_{B_O} N_tot = I`),
`Tr[(U ⊗ σ)(F ⊗ N_tot)] = Tr[(ω_A(U) ⊗ Tr_{R_B} σ) · Tr_{A_O} F]`. -/
theorem ordered_completed_pairing {U : PMat D} (hU : OrderedAB D U) (σ : Op (RA × RB))
    (F : Op ((Fin D.m × RA) × Fin D.d)) (Ntot : Op ((Fin D.n × RB) × Fin D.e))
    (hN : ptraceOut Ntot = 1) :
    Matrix.trace (extended U σ * (F ⊗ₖ Ntot)) =
      Matrix.trace ((omegaA D U ⊗ₖ ptraceOut σ) * ptraceOut F) := by
  obtain ⟨⟨-, hLVa, -, -⟩, -, hBO⟩ := hU
  have he : (D.e : ℂ) ≠ 0 := Nat.cast_ne_zero.2 D.e_ne_zero
  have h1 : extended U σ = R_BO (extended U σ) := by rw [R_BO_extended, hBO]
  rw [h1, R_BO_pairing, kron_R_BO, replaceLast_of_ptraceOut_eq_one hN,
    Matrix.kronecker_smul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
    Matrix.trace_mul_comm (extended U σ), trace_kronecker_one_mul,
    ptraceOut_extended_of_lv_a D hLVa σ, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
    ← mul_assoc, invCard, Fintype.card_fin, inv_mul_cancel₀ he, one_mul,
    Matrix.trace_mul_comm F, trace_kronecker_one_mul]

/-- The entry form of `eq:LV-b` (mirror of `LVa_entry`): for every `bi bi' bo bo'`,
`∑_{a,o} V_{(a,o,bi,bo),(a,o,bi',bo')} = δ_{bo bo'} (1/e) ∑_{a,o,t} V_{(a,o,bi,t),(a,o,bi',t)}`. -/
theorem LVb_entry {V : PMat D} (hLVb : R_AIAO V - R_BO (R_AIAO V) = 0)
    (bi bi' : Fin D.n) (bo bo' : Fin D.e) :
    ∑ a, ∑ o, V ((a, o), (bi, bo)) ((a, o), (bi', bo')) =
      if bo = bo' then
        ((D.e : ℂ))⁻¹ * ∑ a, ∑ o, ∑ t, V ((a, o), (bi, t)) ((a, o), (bi', t))
      else 0 := by
  have hc : invCard (Fin D.m × Fin D.d) ≠ 0 := invCard_ne_zero _
  have key := congrFun (congrFun hLVb ((⟨0, D.m_pos⟩, ⟨0, D.d_pos⟩), (bi, bo)))
    ((⟨0, D.m_pos⟩, ⟨0, D.d_pos⟩), (bi', bo'))
  simp only [Matrix.sub_apply, Matrix.zero_apply, R_BO_apply, R_AIAO_apply,
    if_true, Fintype.sum_prod_type, sub_eq_zero] at key
  have hcomm : ∀ f : Fin D.e → Fin D.m → Fin D.d → ℂ,
      ∑ t, ∑ a, ∑ o, f t a o = ∑ a, ∑ o, ∑ t, f t a o := by
    intro f
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  by_cases h : bo = bo'
  · subst h
    simp only [if_true] at key ⊢
    rw [← Finset.mul_sum, ← mul_left_comm] at key
    have key' := mul_left_cancel₀ hc key
    rw [key', hcomm]
    simp only [invCard, Fintype.card_fin]
  · simp only [h, if_false] at key ⊢
    rcases mul_eq_zero.mp key with h0 | h0
    · exact absurd h0 hc
    · exact h0

omit [Fintype RB] [DecidableEq RA] [DecidableEq RB] in
/-- `Tr_{A_I R_A A_O}(V ⊗ σ) = d · (ω_B(V) ⊗ Tr_{R_A} σ) ⊗ I_{B_O}` from `eq:LV-b`. -/
theorem ptraceFst_extended_of_lv_b {V : PMat D} (hLVb : R_AIAO V - R_BO (R_AIAO V) = 0)
    (σ : Op (RA × RB)) :
    ptraceFst (extended V σ) =
      (D.d : ℂ) • ((omegaB D V ⊗ₖ ptraceFst σ) ⊗ₖ (1 : Op (Fin D.e))) := by
  have hd : (D.d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 D.d_ne_zero
  have he : (D.e : ℂ) ≠ 0 := Nat.cast_ne_zero.2 D.e_ne_zero
  ext ⟨⟨bi, rb⟩, bo⟩ ⟨⟨bi', rb'⟩, bo'⟩
  simp only [ptraceFst_apply, extended_apply, Fintype.sum_prod_type, Matrix.smul_apply,
    smul_eq_mul, Matrix.kroneckerMap_apply, Matrix.one_apply, omegaB_apply]
  have hS : ∑ ai, ∑ ra, ∑ ao, V ((ai, ao), (bi, bo)) ((ai, ao), (bi', bo')) * σ (ra, rb) (ra, rb')
      = (∑ ai, ∑ ao, V ((ai, ao), (bi, bo)) ((ai, ao), (bi', bo'))) *
          ∑ ra, σ (ra, rb) (ra, rb') := by
    rw [Finset.sum_mul_sum]
    simp only [Finset.sum_mul]
  rw [hS, LVb_entry D hLVb bi bi' bo bo']
  by_cases h : bo = bo'
  · subst h
    simp only [if_true, mul_one]
    push_cast
    field_simp
  · simp only [h, if_false, zero_mul, mul_zero]

/-- **Completed-channel pairing, Bob's order** (§5.3): for `V ∈ O_{B≺A}`, Alice's completed
channel `M_tot` (`Tr_{A_O} M_tot = I`) and arbitrary `G` on `B_I R_B B_O`,
`Tr[(V ⊗ σ)(M_tot ⊗ G)] = Tr[(ω_B(V) ⊗ Tr_{R_A} σ) · Tr_{B_O} G]`. -/
theorem ordered_completed_pairing_B {V : PMat D} (hV : OrderedBA D V) (σ : Op (RA × RB))
    (Mtot : Op ((Fin D.m × RA) × Fin D.d)) (G : Op ((Fin D.n × RB) × Fin D.e))
    (hM : ptraceOut Mtot = 1) :
    Matrix.trace (extended V σ * (Mtot ⊗ₖ G)) =
      Matrix.trace ((omegaB D V ⊗ₖ ptraceFst σ) * ptraceOut G) := by
  obtain ⟨⟨-, -, hLVb, -⟩, -, hAO⟩ := hV
  have hd : (D.d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 D.d_ne_zero
  have h1 : extended V σ = R_AO (extended V σ) := by rw [R_AO_extended, hAO]
  rw [h1, R_AO_pairing, kron_R_AO, replaceLast_of_ptraceOut_eq_one hM,
    Matrix.smul_kronecker, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
    Matrix.trace_mul_comm (extended V σ), trace_one_kronecker_mul,
    ptraceFst_extended_of_lv_b D hLVb σ, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
    ← mul_assoc, invCard, Fintype.card_fin, inv_mul_cancel₀ hd, one_mul,
    Matrix.trace_mul_comm G, trace_kronecker_one_mul]

end CompletedPairingPorts

end

end CausalNonpurifiability
