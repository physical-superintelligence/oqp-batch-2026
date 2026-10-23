module

public import CausalNonpurifiability.Certificates.Witness
public import CausalNonpurifiability.Boundary.Dilation
public import CausalNonpurifiability.RobustnessEC
public import CausalNonpurifiability.Boundary.Transpose
public import CausalNonpurifiability.Definitions.OrderedMarginal

@[expose] public section


/-!
# `CausalNonpurifiability.Propositions`

Lemma 2.5 (`lem:ordered`) and Proposition 7.1 (`prop:witness`) of the manuscript, assembled
from the library.

* `lemma_2_5` — for `T ∈ O_{A≺B}`: `T = T̂ ⊗ I_{B_O}` with `T̂ ≥ 0`,
  `Tr_{B_I} T̂ = ω_A(T) ⊗ I_{A_O}`, `ω_A(T) ≥ 0` and `Tr ω_A(T) = Tr T/(de)`
  `lemma_2_5_B` is the same statement for `T ∈ O_{B≺A}` ("with the two parties exchanged");
* `lemma_2_1` — the properties of the replacement maps `R_{A_O}`, `R_{B_O}`, `R_{B_I B_O}`,
  `R_{A_I A_O}` stated in Lemma 2.1 (positive, unital, trace preserving, self-adjoint for the trace
  pairing, idempotent, commuting);
* `proposition_7_1_a` — `R_{B_O} S_0 ≥ 0`, `R_{A_O} S_0 ≥ 0`, and `Tr(S_0 T) ≥ 0` for every
  `T ∈ O_{A≺B} + O_{B≺A}`;
* `appendix_B` — the transposition invariances and the transposed recovery formula of
  Appendix B (`app:transpose`);
* `proposition_7_1_c_trace` — the trace statement of (c): `Tr S_0 = 4(n+8)`.
-/

set_option autoImplicit false

open Matrix
open scoped ComplexOrder Kronecker

namespace CausalNonpurifiability

/-- **Lemma 2.5** (`lem:ordered`, `eq:ordered-marginal`), for the order `A ≺ B`. -/
theorem lemma_2_5 (D : Ports) {T : PMat D} (hT : OrderedAB D T) :
    T = Matrix.reindex (eqBO _ _ _ _).symm (eqBO _ _ _ _).symm
        (hatAB D T ⊗ₖ (1 : Op (Fin D.e))) ∧
      (hatAB D T).PosSemidef ∧
      ptraceOut (hatAB D T) = omegaA D T ⊗ₖ (1 : Op (Fin D.d)) ∧
      (omegaA D T).PosSemidef ∧
      (omegaA D T).trace = (((D.d * D.e : ℕ) : ℂ))⁻¹ * T.trace :=
  ⟨eq_hatAB_kronecker D hT.2.2, hatAB_posSemidef (D := D) hT.2.1, ordered_marginal D hT,
    omegaA_posSemidef' (D := D) hT.2.1, trace_omegaA' (D := D) T⟩

/-- **Proposition 7.1(a)** (`prop:witness`, `eq:witness-replacements`). -/
theorem proposition_7_1_a (D : Ports) (hD : AllPortsGE2 D) :
    (R_BO (toC (S0 D.m D.d D.n D.e))).PosSemidef ∧
      (R_AO (toC (S0 D.m D.d D.n D.e))).PosSemidef ∧
      ∀ U V : PMat D, OrderedAB D U → OrderedBA D V →
        0 ≤ Matrix.trace (toC (S0 D.m D.d D.n D.e) * (U + V)) := by
  have hB : (R_BO (toC (S0 D.m D.d D.n D.e))).PosSemidef := by
    rw [← toC_RBOq]
    exact RBOq_S0_psd hD.2.2.2
  have hA : (R_AO (toC (S0 D.m D.d D.n D.e))).PosSemidef := by
    rw [← toC_RAOq]
    exact RAOq_S0_psd hD.2.1
  refine ⟨hB, hA, fun U V hU hV => ?_⟩
  rw [Matrix.mul_add, trace_add]
  refine add_nonneg ?_ ?_
  · exact witness_nonneg_of_replacement _ _ (fun A => R_BO A) (fun A B => R_BO_pairing A B)
      hB hU.2.1 hU.2.2
  · exact witness_nonneg_of_replacement _ _ (fun A => R_AO A) (fun A B => R_AO_pairing A B)
      hA hV.2.1 hV.2.2

/-- **Proposition 7.1(c)**, first half: `Tr S_0 = 4(n+8)`. -/
theorem proposition_7_1_c_trace {m d n e : ℕ} (hm : 2 ≤ m) (hd : 2 ≤ d) (hn : 2 ≤ n)
    (he : 2 ≤ e) : Matrix.trace (S0 m d n e) = 4 * (n + 8) :=
  trace_S0 hm hd hn he

/-- **Appendix B** (`app:transpose`): the transposition `W ↦ Wᵀ` preserves processes, the cones
`O_{A≺B}` and `O_{B≺A}`, causal separability and extensible causality; it maps pure processes to
pure processes and preserves purifiability; and the recovery formula with a transposed operator
defines the same purifiable processes. -/
theorem appendix_B (D : Ports) (W : PMat D) :
    (Valid D Wᵀ ↔ Valid D W) ∧ (OrderedAB D Wᵀ ↔ OrderedAB D W) ∧
      (OrderedBA D Wᵀ ↔ OrderedBA D W) ∧ (CausallySeparable D Wᵀ ↔ CausallySeparable D W) ∧
      (ExtensiblyCausal D Wᵀ ↔ ExtensiblyCausal D W) ∧
      (∀ (p f : ℕ) (S : HigherOp D p f), Pure D S → Pure D Sᵀ) ∧
      (Purifiable D Wᵀ ↔ Purifiable D W) ∧
      (Purifiable D W ↔
        ∃ (p f : ℕ) (S : HigherOp D p f), Pure D S ∧ (reducePastFuture D S)ᵀ = W) :=
  ⟨valid_transpose_iff (D := D) W, orderedAB_transpose_iff (D := D) W,
    orderedBA_transpose_iff (D := D) W, causallySeparable_transpose_iff (D := D) W,
    extensiblyCausal_transpose_iff (D := D) W, fun _ _ _ h => Pure.transpose (D := D) h,
    purifiable_transpose_iff (D := D) W, purifiable_iff_transpose_convention (D := D) W⟩

/-- For `R_{A_O} T = T` the operator factorizes as `T = T̂ ⊗ I_{A_O}`. -/
theorem eq_hatBA_kronecker (D : Ports) {T : PMat D} (h : R_AO T = T) :
    T = Matrix.reindex (eqAO _ _ _ _).symm (eqAO _ _ _ _).symm
      (hatBA D T ⊗ₖ (1 : Op (Fin D.d))) := by
  conv_lhs => rw [← h]
  rw [R_AO, replaceVia_apply, replaceLast, hatBA, Matrix.smul_kronecker, invCard,
    Fintype.card_fin]

theorem hatBA_posSemidef (D : Ports) {T : PMat D} (hT : T.PosSemidef) :
    (hatBA D T).PosSemidef := by
  unfold hatBA
  refine Matrix.PosSemidef.smul ?_ ?_
  · rw [Matrix.reindex_apply]
    exact ptraceOut_posSemidef (hT.submatrix _)
  · have h : (0 : ℝ) ≤ ((D.d : ℕ) : ℝ)⁻¹ := by positivity
    simp

/-- `eq:ordered-marginal` for the order `B ≺ A`: `Tr_{A_I} T̂ = ω_B(T) ⊗ I_{B_O}`. -/
theorem ordered_marginal_B (D : Ports) {T : PMat D} (hT : OrderedBA D T) :
    ptraceFst (hatBA D T) = omegaB D T ⊗ₖ (1 : Op (Fin D.e)) := by
  obtain ⟨⟨-, -, hLVb, -⟩, -, -⟩ := hT
  ext ⟨b, t⟩ ⟨b', t'⟩
  rw [ptraceFst_apply, Matrix.kroneckerMap_apply, omegaB_apply, Matrix.one_apply]
  simp only [hatBA_apply]
  rw [← Finset.mul_sum, LVb_entry D hLVb b b' t t']
  by_cases ht : t = t'
  · subst ht
    simp only [if_true, mul_one]
    push_cast
    ring
  · simp only [ht, if_false, mul_zero]

/-- **Lemma 2.5** (`lem:ordered`, `eq:ordered-marginal`), for the order `B ≺ A`. -/
theorem lemma_2_5_B (D : Ports) {T : PMat D} (hT : OrderedBA D T) :
    T = Matrix.reindex (eqAO _ _ _ _).symm (eqAO _ _ _ _).symm
        (hatBA D T ⊗ₖ (1 : Op (Fin D.d))) ∧
      (hatBA D T).PosSemidef ∧
      ptraceFst (hatBA D T) = omegaB D T ⊗ₖ (1 : Op (Fin D.e)) ∧
      (omegaB D T).PosSemidef ∧
      (omegaB D T).trace = (((D.d * D.e : ℕ) : ℂ))⁻¹ * T.trace :=
  ⟨eq_hatBA_kronecker D hT.2.2, hatBA_posSemidef D hT.2.1, ordered_marginal_B D hT,
    omegaB_posSemidef' (D := D) hT.2.1, trace_omegaB' (D := D) T⟩

/-- **Lemma 2.1** (`lem:replacement`) for the replacement maps of the paper: positive, unital,
trace preserving, self-adjoint for the trace pairing, idempotent, and commuting. -/
theorem lemma_2_1 (D : Ports) (T A B : PMat D) :
    (T.PosSemidef → (R_AO T).PosSemidef ∧ (R_BO T).PosSemidef ∧ (R_BIBO T).PosSemidef ∧
        (R_AIAO T).PosSemidef) ∧
      (R_AO (1 : PMat D) = 1 ∧ R_BO (1 : PMat D) = 1 ∧ R_BIBO (1 : PMat D) = 1 ∧
        R_AIAO (1 : PMat D) = 1) ∧
      ((R_AO T).trace = T.trace ∧ (R_BO T).trace = T.trace ∧ (R_BIBO T).trace = T.trace ∧
        (R_AIAO T).trace = T.trace) ∧
      ((R_AO A * B).trace = (A * R_AO B).trace ∧ (R_BO A * B).trace = (A * R_BO B).trace ∧
        (R_BIBO A * B).trace = (A * R_BIBO B).trace ∧
        (R_AIAO A * B).trace = (A * R_AIAO B).trace) ∧
      (R_AO (R_AO T) = R_AO T ∧ R_BO (R_BO T) = R_BO T ∧ R_BIBO (R_BIBO T) = R_BIBO T ∧
        R_AIAO (R_AIAO T) = R_AIAO T) ∧
      (R_AO (R_BO T) = R_BO (R_AO T) ∧ R_AO (R_BIBO T) = R_BIBO (R_AO T) ∧
        R_BO (R_AIAO T) = R_AIAO (R_BO T)) :=
  ⟨fun h => ⟨R_AO_posSemidef h, R_BO_posSemidef h, R_BIBO_posSemidef h, R_AIAO_posSemidef h⟩,
    ⟨R_AO_one, R_BO_one, R_BIBO_one, R_AIAO_one⟩,
    ⟨R_AO_trace T, R_BO_trace T, R_BIBO_trace T, R_AIAO_trace T⟩,
    ⟨R_AO_pairing A B, R_BO_pairing A B, R_BIBO_pairing A B, R_AIAO_pairing A B⟩,
    ⟨R_AO_idem T, R_BO_idem T, R_BIBO_idem T, R_AIAO_idem T⟩,
    ⟨R_AO_R_BO_comm T, R_AO_R_BIBO_comm T, R_BO_R_AIAO_comm T⟩⟩

/-- **Lemma 8.1** (`lem:white`, `eq:split-norm`, `eq:white-ordered`) for `Ξ = Xi ∈ L_V` with
`Tr Xi = 0`: `Xi = X_A + X_B` with `X_A = R_{B_O} Xi - ½ R_{A_O B_O} Xi` (`splitA`) and
`X_B = R_{A_O} Xi - ½ R_{A_O B_O} Xi` (`splitB`), where `R_{A_O B_O} = R_{A_O} R_{B_O}`
(Lemma 2.1); `‖X_A‖_∞, ‖X_B‖_∞ ≤ (3/2) ‖Xi‖_∞`; and if `‖Xi‖_∞ ≤ 1/(3mn)`, then
`I/(mn) + Xi = T_A + T_B` with `T_A = I/(2mn) + X_A ∈ O_{A≺B}` and
`T_B = I/(2mn) + X_B ∈ O_{B≺A}`, and `Tr T_A = Tr T_B = de/2`. -/
theorem lemma_8_1 (D : Ports) {Xi : PMat D} (hLV : InLV D Xi) (htr : Xi.trace = 0) :
    Xi = (R_BO Xi - (1 / 2 : ℂ) • R_AO (R_BO Xi)) + (R_AO Xi - (1 / 2 : ℂ) • R_AO (R_BO Xi)) ∧
      opNorm (R_BO Xi - (1 / 2 : ℂ) • R_AO (R_BO Xi)) ≤ 3 / 2 * opNorm Xi ∧
      opNorm (R_AO Xi - (1 / 2 : ℂ) • R_AO (R_BO Xi)) ≤ 3 / 2 * opNorm Xi ∧
      (opNorm Xi ≤ 1 / (3 * D.m * D.n) →
        (1 / ((D.m : ℂ) * D.n)) • (1 : PMat D) + Xi =
            ((1 / ((D.m : ℂ) * D.n) / 2) • (1 : PMat D) +
                (R_BO Xi - (1 / 2 : ℂ) • R_AO (R_BO Xi))) +
              ((1 / ((D.m : ℂ) * D.n) / 2) • (1 : PMat D) +
                (R_AO Xi - (1 / 2 : ℂ) • R_AO (R_BO Xi))) ∧
          OrderedAB D ((1 / ((D.m : ℂ) * D.n) / 2) • (1 : PMat D) +
            (R_BO Xi - (1 / 2 : ℂ) • R_AO (R_BO Xi))) ∧
          OrderedBA D ((1 / ((D.m : ℂ) * D.n) / 2) • (1 : PMat D) +
            (R_AO Xi - (1 / 2 : ℂ) • R_AO (R_BO Xi))) ∧
          ((1 / ((D.m : ℂ) * D.n) / 2) • (1 : PMat D) +
            (R_BO Xi - (1 / 2 : ℂ) • R_AO (R_BO Xi))).trace = (D.d : ℂ) * D.e / 2 ∧
          ((1 / ((D.m : ℂ) * D.n) / 2) • (1 : PMat D) +
            (R_AO Xi - (1 / 2 : ℂ) • R_AO (R_BO Xi))).trace = (D.d : ℂ) * D.e / 2) :=
  ⟨(splitA_add_splitB D hLV).symm, splitA_opNorm_le D hLV.1, splitB_opNorm_le D hLV.1,
    fun hn => ⟨white_ordered_sum D hLV, white_ordered_A D hLV hn, white_ordered_B D hLV hn,
      white_ordered_trace_A D htr, white_ordered_trace_B D htr⟩⟩

/-- **The maximally mixed process is purifiable** (non-vacuity): `I/(mn)` is a process, it lies in `O_{A≺B}` and in `O_{B≺A}` (as `I/(2mn)` in the proof
of Lemma 8.1), and it is purifiable (Proposition 9.2). Hence `¬ Purifiable` is not trivially true. -/
theorem white_process (D : Ports) :
    Valid D ((1 / ((D.m : ℂ) * D.n)) • (1 : PMat D)) ∧
      OrderedAB D ((1 / ((D.m : ℂ) * D.n)) • (1 : PMat D)) ∧
      OrderedBA D ((1 / ((D.m : ℂ) * D.n)) • (1 : PMat D)) ∧
      Purifiable D ((1 / ((D.m : ℂ) * D.n)) • (1 : PMat D)) := by
  have hq : (1 / ((D.m : ℂ) * D.n)) = ((1 / ((D.m : ℚ) * D.n) : ℚ) : ℂ) := by
    first | (push_cast; ring) | push_cast | norm_num
  have hq0 : (0 : ℚ) ≤ 1 / ((D.m : ℚ) * D.n) := by positivity
  have hLV : InLV D ((1 / ((D.m : ℂ) * D.n)) • (1 : PMat D)) := by
    rw [hq]
    exact genLV_smul (isSelfAdjoint_ratCast _) genLV_one
  have hpsd : ((1 / ((D.m : ℂ) * D.n)) • (1 : PMat D)).PosSemidef := by
    rw [hq]
    exact posSemidef_complex_smul Matrix.PosSemidef.one (ratCast_nonneg_complex hq0)
  have htr : ((1 / ((D.m : ℂ) * D.n)) • (1 : PMat D)).trace = ((D.d * D.e : ℕ) : ℂ) := by
    have hm : (D.m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr D.m_ne_zero
    have hn : (D.n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr D.n_ne_zero
    rw [Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
    simp only [Fintype.card_prod, Fintype.card_fin]
    push_cast
    field_simp
    try ring
  have hA : OrderedAB D ((1 / ((D.m : ℂ) * D.n)) • (1 : PMat D)) :=
    ⟨hLV, hpsd, by rw [map_smul, R_BO_one]⟩
  have hB : OrderedBA D ((1 / ((D.m : ℂ) * D.n)) • (1 : PMat D)) :=
    ⟨hLV, hpsd, by rw [map_smul, R_AO_one]⟩
  have hV : Valid D ((1 / ((D.m : ℂ) * D.n)) • (1 : PMat D)) := ⟨hLV, hpsd, htr⟩
  exact ⟨hV, hA, hB, ordered_purifiable (D := D) hV (Or.inl hA)⟩

/-- **`Causal` is not trivially true** (non-vacuity): the
two-way signalling table `p(a,b|x,y) = [a = y][b = x]` on bits is not causal. For each
component of a causal decomposition, the four entries with `a = y` and `b = x` add up to at
most `2`, because one party's marginal does not depend on the other party's setting; for the
table they add up to `4`. -/
theorem not_causal_swap :
    ¬ Causal (fun (x y a b : Fin 2) => if a = y ∧ b = x then (1 : ℝ) else 0) := by
  rintro ⟨lam, pAB, pBA, h0, h1, hA, hB, hnsA, hnsB, hdec⟩
  have w : ∀ x y : Fin 2, lam * pAB x y y x + (1 - lam) * pBA x y y x = 1 := by
    intro x y
    have h := hdec x y y x
    simp at h
    linarith
  have kA : ∀ x : Fin 2, pAB x 0 0 x + pAB x 1 1 x ≤ 1 := by
    intro x
    have s0 : pAB x 0 0 x ≤ ∑ b, pAB x 0 0 b :=
      Finset.single_le_sum (fun b _ => hA.1 x 0 0 b) (Finset.mem_univ x)
    have s1 : pAB x 1 1 x ≤ ∑ b, pAB x 1 1 b :=
      Finset.single_le_sum (fun b _ => hA.1 x 1 1 b) (Finset.mem_univ x)
    have e1 : ∑ b, pAB x 1 1 b = ∑ b, pAB x 0 1 b := hnsA x 1 0 1
    have e2 : ∑ a, ∑ b, pAB x 0 a b = 1 := hA.2 x 0
    rw [Fin.sum_univ_two] at e2
    linarith
  have kB : ∀ y : Fin 2, pBA 0 y y 0 + pBA 1 y y 1 ≤ 1 := by
    intro y
    have s0 : pBA 0 y y 0 ≤ ∑ a, pBA 0 y a 0 :=
      Finset.single_le_sum (fun a _ => hB.1 0 y a 0) (Finset.mem_univ y)
    have s1 : pBA 1 y y 1 ≤ ∑ a, pBA 1 y a 1 :=
      Finset.single_le_sum (fun a _ => hB.1 1 y a 1) (Finset.mem_univ y)
    have e1 : ∑ a, pBA 1 y a 1 = ∑ a, pBA 0 y a 1 := hnsB 1 0 y 1
    have e2 : ∑ a, ∑ b, pBA 0 y a b = 1 := hB.2 0 y
    rw [Finset.sum_comm, Fin.sum_univ_two] at e2
    linarith
  have m1 : 0 ≤ lam * (2 - (pAB 0 0 0 0 + pAB 0 1 1 0 + pAB 1 0 0 1 + pAB 1 1 1 1)) :=
    mul_nonneg h0 (by linarith [kA 0, kA 1])
  have m2 : 0 ≤ (1 - lam) * (2 - (pBA 0 0 0 0 + pBA 0 1 1 0 + pBA 1 0 0 1 + pBA 1 1 1 1)) :=
    mul_nonneg (by linarith) (by linarith [kB 0, kB 1])
  nlinarith [w 0 0, w 0 1, w 1 0, w 1 1, m1, m2]

/-- **Proposition 9.1** (`prop:onedim-order`): if `d = 1` or `n = 1`, every process belongs to
`O_{B≺A}`; if `e = 1` or `m = 1`, every process belongs to `O_{A≺B}`. -/
theorem proposition_9_1 (D : Ports) {W : PMat D} (hW : Valid D W) :
    ((D.d = 1 ∨ D.n = 1) → OrderedBA D W) ∧ ((D.e = 1 ∨ D.m = 1) → OrderedAB D W) :=
  ⟨fun h => h.elim (fun hd => orderedBA_of_d_eq_one hd hW)
      (fun hn => orderedBA_of_n_eq_one hn hW),
    fun h => h.elim (fun he => orderedAB_of_e_eq_one he hW)
      (fun hm => orderedAB_of_m_eq_one hm hW)⟩

/-- **The affine space of the ball**: for `m, d, n, e ≥ 2` the operators
`W_c + Δ` with `Δ ∈ L_V` and `Tr Δ = 0` form the affine space `{T ∈ L_V : Tr T = de}`, which
contains all processes. -/
theorem ball_affine (D : Ports) (hD : AllPortsGE2 D) (T : PMat D) :
    ((InLV D T ∧ T.trace = ((D.d * D.e : ℕ) : ℂ)) ↔
        ∃ Δ : PMat D, InLV D Δ ∧ Δ.trace = 0 ∧ T = WcC D + Δ) ∧
      (Valid D T → InLV D T ∧ T.trace = ((D.d * D.e : ℕ) : ℂ)) := by
  have hc := wc_valid D hD
  refine ⟨⟨fun h => ⟨T - WcC D, genLV_sub h.1 hc.1, ?_, by abel⟩, ?_⟩, fun hV => ⟨hV.1, hV.2.2⟩⟩
  · rw [Matrix.trace_sub, h.2, hc.2.2, sub_self]
  · rintro ⟨Δ, hΔ, htr, rfl⟩
    exact ⟨genLV_add hc.1 hΔ, by rw [Matrix.trace_add, hc.2.2, htr, add_zero]⟩

/-- **Processes near the maximally mixed process are causally separable** (from Lemma 8.1): if `W` is a process and `‖W - I/(mn)‖_∞ ≤ 1/(3mn)`, then `W` is causally
separable, in every local dimension. -/
theorem white_cs (D : Ports) {W : PMat D} (hW : Valid D W)
    (hnorm : opNorm (W - (1 / ((D.m : ℂ) * D.n)) • (1 : PMat D)) ≤ 1 / (3 * D.m * D.n)) :
    CausallySeparable D W := by
  have hI := (white_process D).1
  have hX : InLV D (W - (1 / ((D.m : ℂ) * D.n)) • (1 : PMat D)) := genLV_sub hW.1 hI.1
  have htr : (W - (1 / ((D.m : ℂ) * D.n)) • (1 : PMat D)).trace = 0 := by
    rw [Matrix.trace_sub, hW.2.2, hI.2.2, sub_self]
  obtain ⟨-, -, -, h⟩ := lemma_8_1 D hX htr
  obtain ⟨hsum, hA, hB, -, -⟩ := h hnorm
  refine ⟨hW, _, _, hA, hB, ?_⟩
  rw [← hsum]
  abel

/-- **`S_0` is a causal witness that detects `W_0`** (Section 7: "a Hermitian
operator `S` with `Tr(S T) ≥ 0` for all causally separable processes `T` is called a causal
witness"): `S_0` is Hermitian, `Tr(S_0 T) ≥ 0` for every causally separable process `T`
(Proposition 7.1(a)), and `Tr(S_0 W_0) = -1/5` (Proposition 7.1(b)). -/
theorem definition_witness (D : Ports) (hD : AllPortsGE2 D) :
    (toC (S0 D.m D.d D.n D.e)).IsHermitian ∧
      (∀ T : PMat D, CausallySeparable D T → 0 ≤ Matrix.trace (toC (S0 D.m D.d D.n D.e) * T)) ∧
      Matrix.trace (toC (S0 D.m D.d D.n D.e) * toC (W0 D.m D.d D.n D.e)) = -1 / 5 := by
  refine ⟨S0_isHermitian, ?_, ?_⟩
  · rintro T ⟨-, U, V, hU, hV, rfl⟩
    exact (proposition_7_1_a D hD).2.2 U V hU hV
  · rw [← Matrix.map_mul, trace_toC,
      witness_negative (m := D.m) (d := D.d) (n := D.n) (e := D.e) hD.1 hD.2.1 hD.2.2.1 hD.2.2.2]
    norm_num

end CausalNonpurifiability
