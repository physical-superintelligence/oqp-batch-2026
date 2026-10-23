module

public import CausalNonpurifiability.Definitions.InstrumentsCore
public import Mathlib
public import CausalNonpurifiability.Linear.Indices
public import CausalNonpurifiability.Linear.PartialTrace
public import CausalNonpurifiability.Linear.Replacement
public import CausalNonpurifiability.Definitions.Process
public import CausalNonpurifiability.Definitions.Causality
public import CausalNonpurifiability.Linear.Positive

@[expose] public section


/-!
# `CausalNonpurifiability.Definitions.Instruments`

Choi-coordinate instruments (`eq:choi`, `M = Jᵀ`), density operators, the ancilla-extended
process `extendInput D W σ` (with its entry formula), the extended Born rule
`bornExtended` (`eq:born`) with its reality and positivity lemmas, the normalization
theorem `valid_born_extended : Valid D W → Density σ → Conditional (bornExtended D W σ M N)`,
and the complete extensible-causality quantifier `ExtensiblyCausal`.

The normalization is a forward implication: writing the total instrument
elements as `(1/|O|) • 1 + Δ` with `Tr_O Δ = 0`, the pairing with a process satisfying
`eq:LV-a,b,c` (`GenLV`) reduces to the constant term `Tr W · Tr σ / (d e) = 1`; the three
cross terms vanish because replacement images pair to zero with output-traceless deviations.
This is proved once, generically (`GenLV.trace_mul_kronecker`), and applied to
`extended W σ`, which is in `L_V` by `GenLV.extended`.

Manuscript anchors: `eq:choi`, `eq:born`, `eq:LV`, `eq:valid`, §2.2 (extensible causality).
-/

set_option autoImplicit false

open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

namespace CausalNonpurifiability

/-! ### Instruments and states -/

section InstrumentLemmas

variable {I O X A : Type} [Fintype I] [Fintype O] [Fintype A] [DecidableEq I]

/-- Coarse-grainings `F = ∑_{a ∈ S} M_{a|x}` are positive. -/
theorem Instrument.sum_posSemidef (M : Instrument I O X A) (x : X) (S : Finset A) :
    (∑ a ∈ S, M.elem x a).PosSemidef :=
  Finset.sum_induction _ _ (fun _ _ h h' => h.add h') Matrix.PosSemidef.zero
    (fun a _ => M.positive x a)

/-- Output partial traces of coarse-grainings are effects: `E = Tr_O F` with
`0 ≤ E ≤ 1`, the complement being `Tr_O ∑_{a ∉ S} M_{a|x}` (before `eq:endpoints`: the `E_{a|x} = Tr_{A_O} M_{a|x}` are effects with `∑_a E_{a|x} = I`). -/
theorem Instrument.effect_ptraceOut [DecidableEq A] (M : Instrument I O X A) (x : X)
    (S : Finset A) : Effect (ptraceOut (∑ a ∈ S, M.elem x a)) := by
  refine ⟨ptraceOut_posSemidef (M.sum_posSemidef x S), ?_⟩
  have h : (1 : Op I) - ptraceOut (∑ a ∈ S, M.elem x a) = ptraceOut (∑ a ∈ Sᶜ, M.elem x a) := by
    rw [← M.normalized x, ← Finset.sum_add_sum_compl S, ptraceOut_add, add_sub_cancel_left]
  rw [h]
  exact ptraceOut_posSemidef (M.sum_posSemidef x Sᶜ)

end InstrumentLemmas

/-! ### Ancilla extension of the process -/

section Extended

variable {AI AO BI BO RA RB : Type}

/-- `extended W σ` is the regrouped Kronecker product `W ⊗ₖ σ` along `eqExt`. -/
theorem extended_reindex_eqExt (W : Op (LabIdx AI AO BI BO)) (σ : Op (RA × RB)) :
    extended W σ
      = Matrix.reindex (eqExt AI AO BI BO RA RB) (eqExt AI AO BI BO RA RB) (W ⊗ₖ σ) := by
  ext x y
  simp [Matrix.reindex_apply, extended_apply]

variable [Fintype AI] [Fintype AO] [Fintype BI] [Fintype BO] [Fintype RA] [Fintype RB]

/-- `W ≥ 0`, `σ ≥ 0` give `W ⊗ σ ≥ 0` on the enlarged inputs. -/
theorem posSemidef_extended {W : Op (LabIdx AI AO BI BO)} {σ : Op (RA × RB)}
    (hW : W.PosSemidef) (hσ : σ.PosSemidef) : (extended W σ).PosSemidef := by
  rw [extended_reindex_eqExt, Matrix.reindex_apply]
  exact (posSemidef_kronecker hW hσ).submatrix _

/-- Reindexing along an equivalence preserves the trace (no decidability assumptions). -/
theorem trace_submatrix_equiv_eq {ι κ : Type} [Fintype ι] [Fintype κ] (M : Op κ) (e : ι ≃ κ) :
    (M.submatrix e e).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp e (fun j => M j j)

/-- `Tr (W ⊗ σ) = Tr W · Tr σ`. -/
theorem trace_extended (W : Op (LabIdx AI AO BI BO)) (σ : Op (RA × RB)) :
    (extended W σ).trace = W.trace * σ.trace := by
  rw [extended_reindex_eqExt, Matrix.reindex_apply, trace_submatrix_equiv_eq,
    Matrix.trace_kronecker]

end Extended

section ExtendInput

variable (D : Ports) {RA RB : Type}

theorem extendInput_apply (W : PMat D) (σ : Op (RA × RB)) (ai ai' : Fin D.m) (ra ra' : RA)
    (ao ao' : Fin D.d) (bi bi' : Fin D.n) (rb rb' : RB) (bo bo' : Fin D.e) :
    extendInput D W σ (((ai, ra), ao), ((bi, rb), bo)) (((ai', ra'), ao'), ((bi', rb'), bo'))
      = W ((ai, ao), (bi, bo)) ((ai', ao'), (bi', bo')) * σ (ra, rb) (ra', rb') := rfl

theorem extendInput_eq_extended (W : PMat D) (σ : Op (RA × RB)) :
    extendInput D W σ = extended W σ := rfl

theorem extendInput_hermitian {W : PMat D} {σ : Op (RA × RB)} (hW : W.IsHermitian)
    (hσ : σ.IsHermitian) : (extendInput D W σ).IsHermitian :=
  extended_isHermitian hW hσ

variable [Fintype RA] [Fintype RB]

theorem extendInput_psd {W : PMat D} {σ : Op (RA × RB)} (hW : W.PosSemidef)
    (hσ : σ.PosSemidef) : (extendInput D W σ).PosSemidef :=
  posSemidef_extended hW hσ

theorem extendInput_trace (W : PMat D) (σ : Op (RA × RB)) :
    (extendInput D W σ).trace = W.trace * σ.trace :=
  trace_extended W σ

end ExtendInput

/-! ### The extended Born rule -/

section Born

variable (D : Ports) {RA RB X Y A B : Type} [Fintype RA] [DecidableEq RA] [Fintype RB]
  [DecidableEq RB] [Fintype A] [Fintype B]

/-- The Born trace is real for positive `W`, `σ` (PSD pairing). -/
theorem bornExtended_im_zero {W : PMat D} {σ : Op (RA × RB)} (hW : W.PosSemidef)
    (hσ : σ.PosSemidef) (M : Instrument (Fin D.m × RA) (Fin D.d) X A)
    (N : Instrument (Fin D.n × RB) (Fin D.e) Y B) (x : X) (y : Y) (a : A) (b : B) :
    ((extendInput D W σ * (M.elem x a ⊗ₖ N.elem y b)).trace).im = 0 :=
  trace_mul_im_zero (extendInput_psd D hW hσ) (posSemidef_kronecker (M.positive x a) (N.positive y b))

/-- Born probabilities are nonnegative for positive `W`, `σ`. -/
theorem bornExtended_nonneg {W : PMat D} {σ : Op (RA × RB)} (hW : W.PosSemidef)
    (hσ : σ.PosSemidef) (M : Instrument (Fin D.m × RA) (Fin D.d) X A)
    (N : Instrument (Fin D.n × RB) (Fin D.e) Y B) (x : X) (y : Y) (a : A) (b : B) :
    0 ≤ bornExtended D W σ M N x y a b :=
  trace_mul_re_nonneg (extendInput_psd D hW hσ)
    (posSemidef_kronecker (M.positive x a) (N.positive y b))

/-- Bilinearity of the Kronecker product over finite sums. -/
theorem sum_kronecker_sum_eq {ι κ I J : Type} [Fintype ι] [Fintype κ] (M : ι → Op I)
    (N : κ → Op J) : (∑ a, M a) ⊗ₖ (∑ b, N b) = ∑ a, ∑ b, M a ⊗ₖ N b := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp [Matrix.sum_apply, Finset.sum_mul_sum]

/-- Summing the Born rule over both outcomes pairs the process with the total instrument
elements `∑_a M_{a|x}`, `∑_b N_{b|y}`. -/
theorem bornExtended_sum (W : PMat D) (σ : Op (RA × RB))
    (M : Instrument (Fin D.m × RA) (Fin D.d) X A) (N : Instrument (Fin D.n × RB) (Fin D.e) Y B)
    (x : X) (y : Y) :
    ∑ a, ∑ b, bornExtended D W σ M N x y a b
      = ((extendInput D W σ * ((∑ a, M.elem x a) ⊗ₖ (∑ b, N.elem y b))).trace).re := by
  simp only [bornExtended]
  rw [sum_kronecker_sum_eq, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]

end Born

/-! ### Normalization from `eq:LV` (forward implication) -/

section Normalization

variable {A O B T : Type} [Fintype A] [DecidableEq A] [Fintype O] [DecidableEq O]
  [Fintype B] [DecidableEq B] [Fintype T] [DecidableEq T]

/-- `R_{A_O}` acts on the Alice factor of a Kronecker product: `R_{A_O}(M ⊗ N) = R(M) ⊗ N`. -/
theorem R_AO_kronecker (M : Op (A × O)) (N : Op (B × T)) :
    R_AO (M ⊗ₖ N) = replaceLast M ⊗ₖ N := by
  ext ⟨⟨a, o⟩, ⟨b, t⟩⟩ ⟨⟨a', o'⟩, ⟨b', t'⟩⟩
  simp only [R_AO_apply, Matrix.kroneckerMap_apply, replaceLast_apply, ptraceOut_apply]
  split_ifs
  · rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun z _ => by ring
  · simp

/-- `R_{B_O}` acts on the Bob factor of a Kronecker product: `R_{B_O}(M ⊗ N) = M ⊗ R(N)`. -/
theorem R_BO_kronecker (M : Op (A × O)) (N : Op (B × T)) :
    R_BO (M ⊗ₖ N) = M ⊗ₖ replaceLast N := by
  ext ⟨⟨a, o⟩, ⟨b, t⟩⟩ ⟨⟨a', o'⟩, ⟨b', t'⟩⟩
  simp only [R_BO_apply, Matrix.kroneckerMap_apply, replaceLast_apply, ptraceOut_apply]
  split_ifs
  · rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => by ring
  · simp

/-- `M ⊗ I_{B_I B_O}` is `R_{B_I B_O}`-invariant. -/
theorem R_BIBO_kronecker_one (M : Op (A × O)) :
    R_BIBO (M ⊗ₖ (1 : Op (B × T))) = M ⊗ₖ 1 := by
  ext ⟨⟨a, o⟩, ⟨b, t⟩⟩ ⟨⟨a', o'⟩, ⟨b', t'⟩⟩
  have : Nonempty (B × T) := ⟨(b, t)⟩
  simp only [R_BIBO_apply, Matrix.kroneckerMap_apply, Matrix.one_apply_eq, mul_one,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  split_ifs with h
  · rw [h, Matrix.one_apply_eq, mul_one, ← mul_assoc, invCard_mul_card, one_mul]
  · rw [Matrix.one_apply_ne h, mul_zero]

/-- `I_{A_I A_O} ⊗ N` is `R_{A_I A_O}`-invariant. -/
theorem R_AIAO_one_kronecker (N : Op (B × T)) :
    R_AIAO ((1 : Op (A × O)) ⊗ₖ N) = 1 ⊗ₖ N := by
  ext ⟨⟨a, o⟩, ⟨b, t⟩⟩ ⟨⟨a', o'⟩, ⟨b', t'⟩⟩
  have : Nonempty (A × O) := ⟨(a, o)⟩
  simp only [R_AIAO_apply, Matrix.kroneckerMap_apply, Matrix.one_apply_eq, one_mul,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  split_ifs with h
  · rw [h, Matrix.one_apply_eq, one_mul, ← mul_assoc, invCard_mul_card, one_mul]
  · rw [Matrix.one_apply_ne h, zero_mul]

/-- Output-traceless matrices are killed by the replacement. -/
theorem replaceLast_eq_zero_of_ptraceOut {I Y : Type} [Fintype I] [Fintype Y] [DecidableEq I]
    [DecidableEq Y] {N : Op (I × Y)} (h : ptraceOut N = 0) : replaceLast N = 0 := by
  rw [replaceLast, h, Matrix.zero_kronecker, smul_zero]

/-- The deviation `Δ = M − (1/|O|) • 1` of a normalized total element is output-traceless. -/
theorem ptraceOut_sub_invCard_smul_one {I Y : Type} [Fintype I] [Fintype Y] [DecidableEq I]
    [DecidableEq Y] [Nonempty Y] {M : Op (I × Y)} (hM : ptraceOut M = 1) :
    ptraceOut (M - invCard Y • (1 : Op (I × Y))) = 0 := by
  rw [ptraceOut_sub, ptraceOut_smul, ptraceOut_one, hM, smul_smul, invCard_mul_card, one_smul,
    sub_self]

/-- **Normalization of the pairing** (forward implication).  For `W ∈ L_V`
(`eq:LV-a,b,c`) and total instrument elements `Mt`, `Nt` with `Tr_{A_O} Mt = I`,
`Tr_{B_O} Nt = I`: `Tr[W (Mt ⊗ Nt)] = Tr W / (|A_O| |B_O|)`.  Proof: `Mt = (1/|A_O|) 1 + Δ_A`,
`Nt = (1/|B_O|) 1 + Δ_B` with output-traceless deviations; the `Δ_A ⊗ 1` term vanishes by
`eq:LV-a`, the `1 ⊗ Δ_B` term by `eq:LV-b`, the `Δ_A ⊗ Δ_B` term by `eq:LV-c`, each through
the self-adjointness of the replacements and `R(Δ) = 0`. -/
theorem GenLV.trace_mul_kronecker [Nonempty O] [Nonempty T]
    {W : Op (LabIdx A O B T)} (hW : GenLV W) {Mt : Op (A × O)} (hM : ptraceOut Mt = 1)
    {Nt : Op (B × T)} (hN : ptraceOut Nt = 1) :
    (W * (Mt ⊗ₖ Nt)).trace = invCard O * invCard T * W.trace := by
  obtain ⟨_, ha, hb, hc⟩ := hW
  obtain ⟨ΔA, hΔA⟩ : ∃ Δ : Op (A × O), Δ = Mt - invCard O • 1 := ⟨_, rfl⟩
  obtain ⟨ΔB, hΔB⟩ : ∃ Δ : Op (B × T), Δ = Nt - invCard T • 1 := ⟨_, rfl⟩
  have hA : ptraceOut ΔA = 0 := by rw [hΔA]; exact ptraceOut_sub_invCard_smul_one hM
  have hB : ptraceOut ΔB = 0 := by rw [hΔB]; exact ptraceOut_sub_invCard_smul_one hN
  have hMt : Mt = invCard O • (1 : Op (A × O)) + ΔA := by rw [hΔA]; abel
  have hNt : Nt = invCard T • (1 : Op (B × T)) + ΔB := by rw [hΔB]; abel
  -- replacement images pair to zero with output-traceless deviations
  have zA : ∀ (X : Op (LabIdx A O B T)) (N : Op (B × T)), (R_AO X * (ΔA ⊗ₖ N)).trace = 0 := by
    intro X N
    rw [R_AO_pairing, R_AO_kronecker, replaceLast_eq_zero_of_ptraceOut hA,
      Matrix.zero_kronecker, Matrix.mul_zero, Matrix.trace_zero]
  have zB : ∀ (X : Op (LabIdx A O B T)) (M : Op (A × O)), (R_BO X * (M ⊗ₖ ΔB)).trace = 0 := by
    intro X M
    rw [R_BO_pairing, R_BO_kronecker, replaceLast_eq_zero_of_ptraceOut hB,
      Matrix.kronecker_zero, Matrix.mul_zero, Matrix.trace_zero]
  -- the three cross terms
  have t2 : (W * ((1 : Op (A × O)) ⊗ₖ ΔB)).trace = 0 := by
    rw [← R_AIAO_one_kronecker ΔB, ← R_AIAO_pairing, sub_eq_zero.mp hb, zB]
  have t3 : (W * (ΔA ⊗ₖ (1 : Op (B × T)))).trace = 0 := by
    rw [← R_BIBO_kronecker_one ΔA, ← R_BIBO_pairing, sub_eq_zero.mp ha, zA]
  have hW3 : W = R_AO W + R_BO W - R_AO (R_BO W) := by
    rw [← sub_eq_zero, ← hc]
    abel
  have t4 : (W * (ΔA ⊗ₖ ΔB)).trace = 0 := by
    rw [hW3, sub_mul, add_mul, Matrix.trace_sub, Matrix.trace_add, zA, zB, zA, add_zero,
      sub_zero]
  -- expand and collect
  have expand : Mt ⊗ₖ Nt
      = (invCard T * invCard O) • (1 : Op (LabIdx A O B T))
        + invCard O • ((1 : Op (A × O)) ⊗ₖ ΔB) + invCard T • (ΔA ⊗ₖ (1 : Op (B × T)))
        + ΔA ⊗ₖ ΔB := by
    rw [hMt, hNt]
    simp only [Matrix.add_kronecker, Matrix.kronecker_add, Matrix.smul_kronecker,
      Matrix.kronecker_smul, Matrix.one_kronecker_one, smul_add, smul_smul]
    abel
  rw [expand]
  simp only [mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul,
    Matrix.mul_one, t2, t3, t4, mul_zero, add_zero]
  ring

end Normalization

/-! ### Valid processes give conditional distributions -/

section ValidBorn

variable (D : Ports) {RA RB X Y A B : Type} [Fintype RA] [DecidableEq RA] [Fintype RB]
  [DecidableEq RB] [Fintype A] [Fintype B]

/-- `(1/d)(1/e)(d e) = 1` for the port dimensions. -/
theorem invCard_fin_mul_card_mul : invCard (Fin D.d) * invCard (Fin D.e) * ((D.d * D.e : ℕ) : ℂ) = 1 := by
  have hd : (D.d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr D.d_ne_zero
  have he : (D.e : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr D.e_ne_zero
  rw [invCard, invCard, Fintype.card_fin, Fintype.card_fin, Nat.cast_mul]
  calc ((D.d : ℂ))⁻¹ * ((D.e : ℂ))⁻¹ * ((D.d : ℂ) * (D.e : ℂ))
      = ((D.d : ℂ))⁻¹ * (D.d : ℂ) * (((D.e : ℂ))⁻¹ * (D.e : ℂ)) := by ring
    _ = 1 := by rw [inv_mul_cancel₀ hd, inv_mul_cancel₀ he, one_mul]

/-- **Valid processes yield conditional distributions** (`eq:valid` ⇒ normalized Born rule for
every shared state and every pair of instruments): nonnegativity from positivity, and
`∑_{a,b} p(a,b|x,y) = Tr[(W ⊗ σ)(Mtot ⊗ Ntot)] = Tr W · Tr σ /(d e) = 1` by
`GenLV.trace_mul_kronecker` applied to `extended W σ ∈ L_V` (`GenLV.extended`). -/
theorem valid_born_extended {W : PMat D} {σ : Op (RA × RB)} (hW : Valid D W) (hσ : Density σ)
    (M : Instrument (Fin D.m × RA) (Fin D.d) X A) (N : Instrument (Fin D.n × RB) (Fin D.e) Y B) :
    Conditional (bornExtended D W σ M N) := by
  refine ⟨fun x y a b => bornExtended_nonneg D hW.2.1 hσ.1 M N x y a b, fun x y => ?_⟩
  rw [bornExtended_sum]
  have hLV : GenLV (extendInput D W σ) := GenLV.extended hW.1 hσ.1.1
  rw [GenLV.trace_mul_kronecker hLV (M.normalized x) (N.normalized y), extendInput_trace,
    hW.2.2, hσ.2, mul_one, invCard_fin_mul_card_mul, Complex.one_re]

end ValidBorn

/-! ### Extensible causality -/

end CausalNonpurifiability
