module

public import CausalNonpurifiability.Definitions.SharedInputMarginalsCore
public import Mathlib
public import CausalNonpurifiability.Linear.Indices
public import CausalNonpurifiability.Linear.PartialTrace
public import CausalNonpurifiability.Linear.Replacement
public import CausalNonpurifiability.Linear.Positive
public import CausalNonpurifiability.Definitions.Process
public import CausalNonpurifiability.Definitions.Instruments
public import CausalNonpurifiability.EC.SOS
public import CausalNonpurifiability.EC.Compression
public import CausalNonpurifiability.Certificates.Qubit

@[expose] public section


/-!
# `CausalNonpurifiability.EC.Rectangles`

Endpoint arrays `r_A, r_B` (`eq:endpoints`), the ordered pairings `p_U, p_V` and the ordered
first-party marginals `a_U, b_V` (§5.3), the ordered-event bounds `p_U(F,G) ≤ a_U(F)` and
`p_V(F,G) ≤ b_V(G)`, the signed input pairing `D_C(E,H)` (`eq:DC`), the exact slack identity
`eq:rectangle-slack`, and every rectangle inequality `eq:rectangle`.

## Design (abstract layer)

Everything is stated for an arbitrary port configuration `D`, arbitrary finite ancillas
`R_A, R_B`, an arbitrary shared state `σ`, arbitrary extended instruments (finite settings and
outcomes), and **abstract** process data: `W = U + V + 2 Q_C` (`eq:signed-decomposition`),
`χ_A = ω_A(U) + Tr_{B_I} C`, `χ_B = ω_B(V) + Tr_{A_I} C` (`eq:reference-states`),
`U ∈ O_{A≺B}`, `V ∈ O_{B≺A}` (`eq:UV`), and `C = diagonal (cDC i₀ i₁ j₀ j₁)` (`eq:C`).
The final section instantiates these hypotheses for the signed four-vertex process
`W₀ = toC (W0 m d n e)` (`eq:centers`) in every port dimension `≥ 2`, from the bridges
(`signed_decomposition_toC`, `u_orderedAB`, `v_orderedBA`, `toC_omegaAq/Bq`,
`reference_state_A/B`) and `toC_Qembed_eq_QC`, `toC_C_eq_diagonal_cDC`, and exports
`rectangles_W0` / `rectangles_qubits` in exactly the `hrect` shape consumed by
`ec_of_rectangles` (`EC/Bridge`).

Conventions: Choi coordinates `M = Jᵀ` (`eq:choi`); the Born pairing is
`re Tr[(W ⊗ σ)(F ⊗ G)]` on `extendInput` (`eq:born`); reduced ancilla states are
`σ^{R_A} = Tr_{R_B} σ = ptraceOut σ` and `σ^{R_B} = Tr_{R_A} σ = ptraceFst σ`; the joint input
space `A_I B_I R_A R_B` is party-grouped as `(A_I × B_I) × (R_A × R_B)` (`sideA`/`sideB`/`regroup`,
`EC/Compression`).

Manuscript anchors: `eq:endpoints`, `eq:DC`, `eq:rectangle-slack`, `eq:rectangle`,
`eq:ordered-marginal`, `eq:signed-decomposition`, `eq:reference-states`.

Upstream lemmas consumed exactly once each: `ordered_completed_pairing` /
`ordered_completed_pairing_B` (`Definitions/Process`) for the two completed-channel
equalities, and `qc_pairing_extendInput`, `cA_pairing`, `cB_pairing` (`EC/Compression`) for the three pairing steps of the slack identity.
-/

set_option autoImplicit false

open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

namespace CausalNonpurifiability

noncomputable section

/-! ### Coarse-grained instrument elements -/

section Coarse

variable {I O X A : Type} [Fintype I] [Fintype O] [Fintype A] [DecidableEq I]

/-- Coarse-grained instrument element `F = ∑_{a ∈ S} M_{a|x}` (§5.3). -/
def coarse (M : Instrument I O X A) (x : X) (S : Finset A) : Op (I × O) :=
  ∑ a ∈ S, M.elem x a

theorem coarse_posSemidef (M : Instrument I O X A) (x : X) (S : Finset A) :
    (coarse M x S).PosSemidef :=
  M.sum_posSemidef x S

/-- Coarse-grained effect `E = Tr_O F` (§5.3, `E_{a|x} = Tr_{A_O} M_{a|x}`). -/
def coarseEffect (M : Instrument I O X A) (x : X) (S : Finset A) : Op I :=
  ptraceOut (coarse M x S)

/-- `E = Tr_O F` is an effect, the complement being the coarse-graining over the omitted
outcomes. -/
theorem coarseEffect_effect [DecidableEq A] (M : Instrument I O X A) (x : X) (S : Finset A) :
    Effect (coarseEffect M x S) :=
  M.effect_ptraceOut x S

theorem coarseEffect_posSemidef (M : Instrument I O X A) (x : X) (S : Finset A) :
    (coarseEffect M x S).PosSemidef :=
  ptraceOut_posSemidef (coarse_posSemidef M x S)

/-- The coarse-graining over all outcomes is the total instrument element. -/
theorem coarse_univ (M : Instrument I O X A) (x : X) :
    coarse M x Finset.univ = ∑ a, M.elem x a :=
  rfl

/-- `Tr_O ∑_a M_{a|x} = I` (§2.1 normalization). -/
theorem ptraceOut_coarse_univ (M : Instrument I O X A) (x : X) :
    ptraceOut (coarse M x Finset.univ) = 1 :=
  M.normalized x

/-- Completing a coarse-graining to the full channel adds the omitted outcomes. -/
theorem coarse_univ_eq_add_compl [DecidableEq A] (M : Instrument I O X A) (x : X)
    (S : Finset A) : coarse M x Finset.univ = coarse M x S + coarse M x Sᶜ :=
  (Finset.sum_add_sum_compl S (M.elem x)).symm

end Coarse

section PtraceSum

variable {I O ι : Type} [Fintype O]

/-- `Tr_O` of a finite sum. -/
theorem ptraceOut_finset_sum (s : Finset ι) (f : ι → Op (I × O)) :
    ptraceOut (∑ i ∈ s, f i) = ∑ i ∈ s, ptraceOut (f i) :=
  map_sum ptraceOutₗ f s

end PtraceSum

/-! ### Reduced ancilla states -/

section Reduced

variable {RA RB : Type} [Fintype RA] [Fintype RB]

theorem sigmaA_posSemidef {σ : Op (RA × RB)} (hσ : σ.PosSemidef) : (sigmaA σ).PosSemidef :=
  ptraceOut_posSemidef hσ

theorem sigmaB_posSemidef {σ : Op (RA × RB)} (hσ : σ.PosSemidef) : (sigmaB σ).PosSemidef := by
  unfold sigmaB ptraceFst
  rw [Matrix.reindex_apply]
  exact ptraceOut_posSemidef (hσ.submatrix _)

theorem trace_sigmaA (σ : Op (RA × RB)) : (sigmaA σ).trace = σ.trace :=
  trace_ptraceOut σ

theorem trace_sigmaB (σ : Op (RA × RB)) : (sigmaB σ).trace = σ.trace := by
  simp only [sigmaB, Matrix.trace, Matrix.diag_apply, ptraceFst_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]

end Reduced

/-! ### Endpoint arrays (`eq:endpoints`) -/

section EndpointsA

variable (D : Ports) {RA RB X A : Type} [Fintype RA] [Fintype RB] [DecidableEq RA] [Fintype A]

/-- Alice's endpoint array `r_A(a|x) = Tr[(χ_A ⊗ σ^{R_A}) E_{a|x}]` (`eq:endpoints`) for a
reference state `χ_A` on `A_I` (`eq:reference-states`: `χ_A = ω_A(U) + C_A = θ_m/2`). It depends
only on Alice's setting and outcome. -/
def rA (σ : Op (RA × RB)) (chiA : Op (Fin D.m)) (M : Instrument (Fin D.m × RA) (Fin D.d) X A)
    (x : X) (a : A) : ℝ :=
  (((chiA ⊗ₖ sigmaA σ) * ptraceOut (M.elem x a)).trace).re

theorem rA_nonneg {σ : Op (RA × RB)} (hσ : σ.PosSemidef) {chiA : Op (Fin D.m)}
    (hχ : chiA.PosSemidef) (M : Instrument (Fin D.m × RA) (Fin D.d) X A) (x : X) (a : A) :
    0 ≤ rA D σ chiA M x a :=
  trace_mul_re_nonneg (posSemidef_kronecker hχ (sigmaA_posSemidef hσ))
    (ptraceOut_posSemidef (M.positive x a))

/-- `r_A(S|x) = Tr[(χ_A ⊗ σ^{R_A}) E]` with `E = Tr_{A_O} F` the coarse-grained effect
("`r_A(S|x)` denotes a sum", §5.3). -/
theorem sum_rA_finset (σ : Op (RA × RB)) (chiA : Op (Fin D.m))
    (M : Instrument (Fin D.m × RA) (Fin D.d) X A) (x : X) (S : Finset A) :
    ∑ a ∈ S, rA D σ chiA M x a
      = (((chiA ⊗ₖ sigmaA σ) * ptraceOut (coarse M x S)).trace).re := by
  unfold rA coarse
  rw [ptraceOut_finset_sum, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]

/-- Total mass of Alice's endpoint array: `∑_a r_A(a|x) = Tr χ_A · Tr σ` (`eq:endpoints`,
using `Tr_{A_O} ∑_a M_{a|x} = I`). -/
theorem sum_rA (σ : Op (RA × RB)) (chiA : Op (Fin D.m))
    (M : Instrument (Fin D.m × RA) (Fin D.d) X A) (x : X) :
    ∑ a, rA D σ chiA M x a = (chiA.trace * σ.trace).re := by
  rw [sum_rA_finset, ptraceOut_coarse_univ, Matrix.mul_one, Matrix.trace_kronecker, trace_sigmaA]

/-- `∑_a r_A(a|x) = 1/2` for a density `σ` and a reference state of trace `1/2`
(`eq:endpoints`: "total masses `1/2, 1/2`"). -/
theorem sum_rA_half {σ : Op (RA × RB)} (hσ : σ.trace = 1) {chiA : Op (Fin D.m)}
    (hχ : chiA.trace = ((1 / 2 : ℝ) : ℂ)) (M : Instrument (Fin D.m × RA) (Fin D.d) X A)
    (x : X) : ∑ a, rA D σ chiA M x a = 1 / 2 := by
  rw [sum_rA, hσ, hχ, mul_one, Complex.ofReal_re]

end EndpointsA

section EndpointsB

variable (D : Ports) {RA RB Y B : Type} [Fintype RA] [Fintype RB] [DecidableEq RB] [Fintype B]

/-- Bob's endpoint array `r_B(b|y) = Tr[(χ_B ⊗ σ^{R_B}) H_{b|y}]` (`eq:endpoints`). -/
def rB (σ : Op (RA × RB)) (chiB : Op (Fin D.n)) (N : Instrument (Fin D.n × RB) (Fin D.e) Y B)
    (y : Y) (b : B) : ℝ :=
  (((chiB ⊗ₖ sigmaB σ) * ptraceOut (N.elem y b)).trace).re

theorem rB_nonneg {σ : Op (RA × RB)} (hσ : σ.PosSemidef) {chiB : Op (Fin D.n)}
    (hχ : chiB.PosSemidef) (N : Instrument (Fin D.n × RB) (Fin D.e) Y B) (y : Y) (b : B) :
    0 ≤ rB D σ chiB N y b :=
  trace_mul_re_nonneg (posSemidef_kronecker hχ (sigmaB_posSemidef hσ))
    (ptraceOut_posSemidef (N.positive y b))

theorem sum_rB_finset (σ : Op (RA × RB)) (chiB : Op (Fin D.n))
    (N : Instrument (Fin D.n × RB) (Fin D.e) Y B) (y : Y) (T : Finset B) :
    ∑ b ∈ T, rB D σ chiB N y b
      = (((chiB ⊗ₖ sigmaB σ) * ptraceOut (coarse N y T)).trace).re := by
  unfold rB coarse
  rw [ptraceOut_finset_sum, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]

theorem sum_rB (σ : Op (RA × RB)) (chiB : Op (Fin D.n))
    (N : Instrument (Fin D.n × RB) (Fin D.e) Y B) (y : Y) :
    ∑ b, rB D σ chiB N y b = (chiB.trace * σ.trace).re := by
  rw [sum_rB_finset, ptraceOut_coarse_univ, Matrix.mul_one, Matrix.trace_kronecker, trace_sigmaB]

theorem sum_rB_half {σ : Op (RA × RB)} (hσ : σ.trace = 1) {chiB : Op (Fin D.n)}
    (hχ : chiB.trace = ((1 / 2 : ℝ) : ℂ)) (N : Instrument (Fin D.n × RB) (Fin D.e) Y B)
    (y : Y) : ∑ b, rB D σ chiB N y b = 1 / 2 := by
  rw [sum_rB, hσ, hχ, mul_one, Complex.ofReal_re]

end EndpointsB

/-! ### Ordered pairings and ordered first-party marginals (§5.3) -/

section Pairings

variable (D : Ports) {RA RB : Type} [Fintype RA] [Fintype RB]

/-- The pairing `p_T(F,G) = Tr[(T ⊗ σ)(F ⊗ G)]` of a process `T` with local operators `F`, `G`
on the ancilla-extended laboratories (§5.3, `p_U`, `p_V`; for `T = W` and instrument elements
this is the Born rule `eq:born`). -/
def pT (T : PMat D) (σ : Op (RA × RB)) (F : Op ((Fin D.m × RA) × Fin D.d))
    (G : Op ((Fin D.n × RB) × Fin D.e)) : ℝ :=
  ((extendInput D T σ * (F ⊗ₖ G)).trace).re

/-- Alice's ordered first-party marginal `a_U(F) = Tr[(ω_A(U) ⊗ σ^{R_A}) E]`, `E = Tr_{A_O} F`
(§5.3, `eq:ordered-marginal`). -/
def aU (U : PMat D) (σ : Op (RA × RB)) (F : Op ((Fin D.m × RA) × Fin D.d)) : ℝ :=
  (((omegaA D U ⊗ₖ sigmaA σ) * ptraceOut F).trace).re

/-- Bob's ordered first-party marginal `b_V(G) = Tr[(ω_B(V) ⊗ σ^{R_B}) H]`, `H = Tr_{B_O} G`
(§5.3). -/
def bV (V : PMat D) (σ : Op (RA × RB)) (G : Op ((Fin D.n × RB) × Fin D.e)) : ℝ :=
  (((omegaB D V ⊗ₖ sigmaB σ) * ptraceOut G).trace).re

/-- Bilinearity of the Kronecker product over finite sums. -/
theorem kronecker_finset_sum_sum {ι κ I J : Type} (s : Finset ι) (t : Finset κ) (M : ι → Op I)
    (N : κ → Op J) : (∑ i ∈ s, M i) ⊗ₖ (∑ j ∈ t, N j) = ∑ i ∈ s, ∑ j ∈ t, M i ⊗ₖ N j := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp [Matrix.sum_apply, Finset.sum_mul_sum]

theorem pT_add_right (T : PMat D) (σ : Op (RA × RB)) (F : Op ((Fin D.m × RA) × Fin D.d))
    (G₁ G₂ : Op ((Fin D.n × RB) × Fin D.e)) :
    pT D T σ F (G₁ + G₂) = pT D T σ F G₁ + pT D T σ F G₂ := by
  simp only [pT, Matrix.kronecker_add, Matrix.mul_add, Matrix.trace_add, Complex.add_re]

theorem pT_add_left (T : PMat D) (σ : Op (RA × RB)) (F₁ F₂ : Op ((Fin D.m × RA) × Fin D.d))
    (G : Op ((Fin D.n × RB) × Fin D.e)) :
    pT D T σ (F₁ + F₂) G = pT D T σ F₁ G + pT D T σ F₂ G := by
  simp only [pT, Matrix.add_kronecker, Matrix.mul_add, Matrix.trace_add, Complex.add_re]

omit [Fintype RA] [Fintype RB] in
/-- Linearity of the ancilla extension in the process (`extendInput D W σ = extended W σ`). -/
theorem extendInput_add' (T₁ T₂ : PMat D) (σ : Op (RA × RB)) :
    extendInput D (T₁ + T₂) σ = extendInput D T₁ σ + extendInput D T₂ σ :=
  extended_add T₁ σ T₂

omit [Fintype RA] [Fintype RB] in
theorem extendInput_smul' (c : ℂ) (T : PMat D) (σ : Op (RA × RB)) :
    extendInput D (c • T) σ = c • extendInput D T σ := by
  ext x y
  simp only [extendInput_eq_extended, extended_apply, Matrix.smul_apply, smul_eq_mul, mul_assoc]

theorem pT_add_process (T₁ T₂ : PMat D) (σ : Op (RA × RB)) (F : Op ((Fin D.m × RA) × Fin D.d))
    (G : Op ((Fin D.n × RB) × Fin D.e)) :
    pT D (T₁ + T₂) σ F G = pT D T₁ σ F G + pT D T₂ σ F G := by
  simp only [pT, extendInput_add', Matrix.add_mul, Matrix.trace_add, Complex.add_re]

theorem pT_two_smul (T : PMat D) (σ : Op (RA × RB)) (F : Op ((Fin D.m × RA) × Fin D.d))
    (G : Op ((Fin D.n × RB) × Fin D.e)) :
    pT D ((2 : ℂ) • T) σ F G = 2 * pT D T σ F G := by
  unfold pT
  rw [extendInput_smul', Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  simp [Complex.mul_re]

/-! #### Completed-channel equalities (`ordered_completed_pairing`, `Definitions/Process`) -/

/-- Completed-channel equality for `U ∈ O_{A≺B}`: for Bob's total element `Tr_{B_O} N = I`,
`Tr[(U ⊗ σ)(F ⊗ N)] = Tr[(ω_A(U) ⊗ σ^{R_A}) Tr_{A_O} F]` ("the equality for the completed
channel follows directly from `eq:ordered-marginal` and `Tr_{B_O} ∑_b N_{b|y} = I`", §5.3). -/
theorem completed_pairing_A [DecidableEq RA] [DecidableEq RB] {U : PMat D} (hU : OrderedAB D U) (σ : Op (RA × RB))
    (F : Op ((Fin D.m × RA) × Fin D.d)) {Ntot : Op ((Fin D.n × RB) × Fin D.e)}
    (hN : ptraceOut Ntot = 1) :
    (extendInput D U σ * (F ⊗ₖ Ntot)).trace = ((omegaA D U ⊗ₖ sigmaA σ) * ptraceOut F).trace :=
  ordered_completed_pairing D hU σ F Ntot hN

/-- Completed-channel equality for `V ∈ O_{B≺A}` (symmetric, with `σ^{R_B} = Tr_{R_A} σ`). -/
theorem completed_pairing_B [DecidableEq RA] [DecidableEq RB] {V : PMat D} (hV : OrderedBA D V) (σ : Op (RA × RB))
    (G : Op ((Fin D.n × RB) × Fin D.e)) {Mtot : Op ((Fin D.m × RA) × Fin D.d)}
    (hM : ptraceOut Mtot = 1) :
    (extendInput D V σ * (Mtot ⊗ₖ G)).trace = ((omegaB D V ⊗ₖ sigmaB σ) * ptraceOut G).trace :=
  ordered_completed_pairing_B D hV σ Mtot G hM

variable [DecidableEq RA] [DecidableEq RB] {X Y A B : Type} [Fintype A] [Fintype B]

theorem bornExtended_eq_pT (W : PMat D) (σ : Op (RA × RB))
    (M : Instrument (Fin D.m × RA) (Fin D.d) X A) (N : Instrument (Fin D.n × RB) (Fin D.e) Y B)
    (x : X) (y : Y) (a : A) (b : B) :
    bornExtended D W σ M N x y a b = pT D W σ (M.elem x a) (N.elem y b) :=
  rfl

/-- `p(S,T|x,y) = ∑_{a∈S} ∑_{b∈T} p(a,b|x,y) = p_W(F,G)` for the coarse-grainings
`F = ∑_{a∈S} M_{a|x}`, `G = ∑_{b∈T} N_{b|y}` (§5.3). -/
theorem pT_coarse (W : PMat D) (σ : Op (RA × RB)) (M : Instrument (Fin D.m × RA) (Fin D.d) X A)
    (N : Instrument (Fin D.n × RB) (Fin D.e) Y B) (x : X) (y : Y) (S : Finset A) (T : Finset B) :
    ∑ a ∈ S, ∑ b ∈ T, bornExtended D W σ M N x y a b
      = pT D W σ (coarse M x S) (coarse N y T) := by
  simp only [bornExtended_eq_pT, pT, coarse]
  rw [kronecker_finset_sum_sum, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]

/-- PSD pairing: `p_T(F,G) ≥ 0` for positive `T, σ, F, G`. -/
theorem pT_nonneg {T : PMat D} (hT : T.PosSemidef) {σ : Op (RA × RB)} (hσ : σ.PosSemidef)
    {F : Op ((Fin D.m × RA) × Fin D.d)} (hF : F.PosSemidef)
    {G : Op ((Fin D.n × RB) × Fin D.e)} (hG : G.PosSemidef) : 0 ≤ pT D T σ F G :=
  trace_mul_re_nonneg (extendInput_psd D hT hσ) (posSemidef_kronecker hF hG)

/-! #### Ordered-event bounds -/

/-- **Ordered-event bound, Alice first**: for `U ∈ O_{A≺B}`, a density `σ`, a positive local
operator `F` and any coarse-graining `G = ∑_{b∈T} N_{b|y}`, `p_U(F,G) ≤ a_U(F)` (§5.3).
Proof: complete `G` to Bob's full channel, where equality holds (`completed_pairing_A`); the
omitted outcomes contribute `p_U(F, ∑_{b∉T} N_{b|y}) ≥ 0` by PSD pairing. -/
theorem ordered_event_bound_A [DecidableEq B] {U : PMat D} (hU : OrderedAB D U)
    {σ : Op (RA × RB)} (hσ : Density σ) {F : Op ((Fin D.m × RA) × Fin D.d)} (hF : F.PosSemidef)
    (N : Instrument (Fin D.n × RB) (Fin D.e) Y B) (y : Y) (T : Finset B) :
    pT D U σ F (coarse N y T) ≤ aU D U σ F := by
  have h1 : pT D U σ F (coarse N y Finset.univ) = aU D U σ F := by
    unfold pT aU
    rw [completed_pairing_A D hU σ F (ptraceOut_coarse_univ N y)]
  have h2 : pT D U σ F (coarse N y Finset.univ)
      = pT D U σ F (coarse N y T) + pT D U σ F (coarse N y Tᶜ) := by
    rw [coarse_univ_eq_add_compl N y T, pT_add_right]
  have h3 : 0 ≤ pT D U σ F (coarse N y Tᶜ) :=
    pT_nonneg D hU.2.1 hσ.1 hF (coarse_posSemidef N y Tᶜ)
  linarith

/-- **Ordered-event bound, Bob first**: for `V ∈ O_{B≺A}`, `p_V(F,G) ≤ b_V(G)` for every
coarse-graining `F = ∑_{a∈S} M_{a|x}` and positive `G` (§5.3). -/
theorem ordered_event_bound_B [DecidableEq A] {V : PMat D} (hV : OrderedBA D V)
    {σ : Op (RA × RB)} (hσ : Density σ) {G : Op ((Fin D.n × RB) × Fin D.e)} (hG : G.PosSemidef)
    (M : Instrument (Fin D.m × RA) (Fin D.d) X A) (x : X) (S : Finset A) :
    pT D V σ (coarse M x S) G ≤ bV D V σ G := by
  have h1 : pT D V σ (coarse M x Finset.univ) G = bV D V σ G := by
    unfold pT bV
    rw [completed_pairing_B D hV σ G (ptraceOut_coarse_univ M x)]
  have h2 : pT D V σ (coarse M x Finset.univ) G
      = pT D V σ (coarse M x S) G + pT D V σ (coarse M x Sᶜ) G := by
    rw [coarse_univ_eq_add_compl M x S, pT_add_left]
  have h3 : 0 ≤ pT D V σ (coarse M x Sᶜ) G :=
    pT_nonneg D hV.2.1 hσ.1 (coarse_posSemidef M x Sᶜ) hG
  linarith

end Pairings

/-! ### The signed input pairing `D_C(E,H)` (`eq:DC`) -/

section SignedPairing

variable (D : Ports) {RA RB : Type} [Fintype RA] [Fintype RB] [DecidableEq RA] [DecidableEq RB]

/-- `D_C(E,H) = Tr[(C ⊗ σ)(E' + H' − 2E'H')]` (`eq:DC`) on the party-grouped joint input space
`(A_I × B_I) × (R_A × R_B)`, with `E' = E ⊗ 1_{B_I R_B}`, `H' = 1_{A_I R_A} ⊗ H` (`sideA`,
`sideB`); identity factors are explicit, nothing is dephased. -/
def DC (Cm : Op (Fin D.m × Fin D.n)) (σ : Op (RA × RB)) (E : Op (Fin D.m × RA))
    (H : Op (Fin D.n × RB)) : ℝ :=
  (((Cm ⊗ₖ σ) * (sideA (J := Fin D.n) (RB := RB) E + sideB (I := Fin D.m) (RA := RA) H
      - 2 * sideA (J := Fin D.n) (RB := RB) E * sideB (I := Fin D.m) (RA := RA) H)).trace).re

/-- Expansion of `D_C(E,H)` into its three pairings. -/
theorem DC_eq (Cm : Op (Fin D.m × Fin D.n)) (σ : Op (RA × RB)) (E : Op (Fin D.m × RA))
    (H : Op (Fin D.n × RB)) :
    DC D Cm σ E H
      = (((Cm ⊗ₖ σ) * sideA (J := Fin D.n) (RB := RB) E).trace).re
        + (((Cm ⊗ₖ σ) * sideB (I := Fin D.m) (RA := RA) H).trace).re
        - 2 * (((Cm ⊗ₖ σ) * (sideA (J := Fin D.n) (RB := RB) E
            * sideB (I := Fin D.m) (RA := RA) H)).trace).re := by
  unfold DC
  rw [two_mul, add_mul, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_add, Matrix.trace_sub,
    Matrix.trace_add, Matrix.trace_add, Complex.sub_re, Complex.add_re, Complex.add_re]
  ring

/-- **`eq:DC` positivity** for the manuscript's diagonal `C = diagonal (cDC i₀ i₁ j₀ j₁)`
(`eq:C`), a PSD `σ` and effects `E`, `H`: `D_C(E,H) ≥ 0` (`dc_re_nonneg_abstract`,
via `eq:operator-SOS`). -/
theorem DC_nonneg {Cm : Op (Fin D.m × Fin D.n)} {i0 i1 : Fin D.m} {j0 j1 : Fin D.n}
    (hC : Cm = Matrix.diagonal (cDC i0 i1 j0 j1)) {σ : Op (RA × RB)} (hσ : σ.PosSemidef)
    {E : Op (Fin D.m × RA)} (hE : Effect E) {H : Op (Fin D.n × RB)} (hH : Effect H) :
    0 ≤ DC D Cm σ E H := by
  unfold DC
  rw [hC]
  exact (Complex.nonneg_iff.mp (dc_nonneg_abstract hσ hE hH i0 i1 j0 j1)).1

/-- Positive real scaling of the signed coefficient matrix scales `D_C` (`eq:DC` is linear in `C`). -/
theorem DC_real_smul (c : ℝ) (Cm : Op (Fin D.m × Fin D.n)) (σ : Op (RA × RB)) (E : Op (Fin D.m × RA))
    (H : Op (Fin D.n × RB)) : DC D ((c : ℂ) • Cm) σ E H = c * DC D Cm σ E H := by
  unfold DC
  rw [Matrix.smul_kronecker, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

theorem DC_rat_smul (q : ℚ) (Cm : Op (Fin D.m × Fin D.n)) (σ : Op (RA × RB)) (E : Op (Fin D.m × RA))
    (H : Op (Fin D.n × RB)) : DC D ((q : ℂ) • Cm) σ E H = (q : ℝ) * DC D Cm σ E H := by
  rw [← Complex.ofReal_ratCast, DC_real_smul]

/-! #### Pairing steps from `EC/Compression` -/

/-- `p_{Q_C}(F,G) = Tr[(C ⊗ σ)(E' H')]` with `E = Tr_{A_O} F`, `H = Tr_{B_O} G`: `Q_C` carries
the identity on the outputs, so the output indices of `F`, `G` are traced (`eq:QC`). -/
theorem qc_pairing_step (Cm : Op (Fin D.m × Fin D.n)) (σ : Op (RA × RB))
    (F : Op ((Fin D.m × RA) × Fin D.d)) (G : Op ((Fin D.n × RB) × Fin D.e)) :
    (extendInput D (QC D Cm) σ * (F ⊗ₖ G)).trace
      = ((Cm ⊗ₖ σ) * (sideA (J := Fin D.n) (RB := RB) (ptraceOut F)
          * sideB (I := Fin D.m) (RA := RA) (ptraceOut G))).trace :=
  qc_pairing_extendInput D Cm σ F G

omit [DecidableEq RA] in
/-- `Tr[(C_A ⊗ σ^{R_A}) E] = Tr[(C ⊗ σ) E']` with `C_A = Tr_{B_I} C` (`eq:reference-states`). -/
theorem cA_pairing_step (Cm : Op (Fin D.m × Fin D.n)) (σ : Op (RA × RB)) (E : Op (Fin D.m × RA)) :
    ((ptraceOut Cm ⊗ₖ sigmaA σ) * E).trace
      = ((Cm ⊗ₖ σ) * sideA (J := Fin D.n) (RB := RB) E).trace :=
  cA_pairing Cm σ E

omit [DecidableEq RB] in
/-- `Tr[(C_B ⊗ σ^{R_B}) H] = Tr[(C ⊗ σ) H']` with `C_B = Tr_{A_I} C` (`eq:reference-states`). -/
theorem cB_pairing_step (Cm : Op (Fin D.m × Fin D.n)) (σ : Op (RA × RB)) (H : Op (Fin D.n × RB)) :
    ((ptraceFst Cm ⊗ₖ sigmaB σ) * H).trace
      = ((Cm ⊗ₖ σ) * sideB (I := Fin D.m) (RA := RA) H).trace :=
  cB_pairing Cm σ H

end SignedPairing

/-! ### The exact slack identity and every rectangle (`eq:rectangle-slack`, `eq:rectangle`) -/

section Rectangles

variable (D : Ports) {RA RB X Y A B : Type} [Fintype RA] [Fintype RB] [DecidableEq RA]
  [DecidableEq RB] [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

omit [DecidableEq A] [DecidableEq B] in
/-- **Exact slack identity** (`eq:rectangle-slack`): for `W = U + V + 2 Q_C`
(`eq:signed-decomposition`) and reference states `χ_A = ω_A(U) + Tr_{B_I} C`,
`χ_B = ω_B(V) + Tr_{A_I} C` (`eq:reference-states`), with `F = ∑_{a∈S} M_{a|x}`,
`G = ∑_{b∈T} N_{b|y}`, `E = Tr_{A_O} F`, `H = Tr_{B_O} G`:
`r_A(S|x) + r_B(T|y) − p(S,T|x,y) = [a_U(F) − p_U(F,G)] + [b_V(G) − p_V(F,G)] + D_C(E,H)`.
No positivity is used; this is bilinearity of the trace plus the three pairing identities. -/
theorem rectangle_slack {W U V : PMat D} {Cm : Op (Fin D.m × Fin D.n)}
    (hW : W = U + V + (2 : ℂ) • QC D Cm) {chiA : Op (Fin D.m)}
    (hχA : chiA = omegaA D U + ptraceOut Cm) {chiB : Op (Fin D.n)}
    (hχB : chiB = omegaB D V + ptraceFst Cm) (σ : Op (RA × RB))
    (M : Instrument (Fin D.m × RA) (Fin D.d) X A) (N : Instrument (Fin D.n × RB) (Fin D.e) Y B)
    (x : X) (y : Y) (S : Finset A) (T : Finset B) :
    ∑ a ∈ S, rA D σ chiA M x a + ∑ b ∈ T, rB D σ chiB N y b
        - ∑ a ∈ S, ∑ b ∈ T, bornExtended D W σ M N x y a b
      = (aU D U σ (coarse M x S) - pT D U σ (coarse M x S) (coarse N y T))
        + (bV D V σ (coarse N y T) - pT D V σ (coarse M x S) (coarse N y T))
        + DC D Cm σ (coarseEffect M x S) (coarseEffect N y T) := by
  unfold coarseEffect
  have hrA : ∑ a ∈ S, rA D σ chiA M x a
      = aU D U σ (coarse M x S)
        + (((Cm ⊗ₖ σ) * sideA (J := Fin D.n) (RB := RB) (ptraceOut (coarse M x S))).trace).re := by
    rw [sum_rA_finset, hχA, Matrix.add_kronecker, Matrix.add_mul, Matrix.trace_add,
      Complex.add_re, cA_pairing_step]
    rfl
  have hrB : ∑ b ∈ T, rB D σ chiB N y b
      = bV D V σ (coarse N y T)
        + (((Cm ⊗ₖ σ) * sideB (I := Fin D.m) (RA := RA) (ptraceOut (coarse N y T))).trace).re := by
    rw [sum_rB_finset, hχB, Matrix.add_kronecker, Matrix.add_mul, Matrix.trace_add,
      Complex.add_re, cB_pairing_step]
    rfl
  have hp : ∑ a ∈ S, ∑ b ∈ T, bornExtended D W σ M N x y a b
      = pT D U σ (coarse M x S) (coarse N y T) + pT D V σ (coarse M x S) (coarse N y T)
        + 2 * (((Cm ⊗ₖ σ) * (sideA (J := Fin D.n) (RB := RB) (ptraceOut (coarse M x S))
            * sideB (I := Fin D.m) (RA := RA) (ptraceOut (coarse N y T)))).trace).re := by
    rw [pT_coarse, hW, pT_add_process, pT_add_process, pT_two_smul]
    unfold pT
    rw [qc_pairing_step]
  rw [hrA, hrB, hp, DC_eq]
  ring

/-- **Every rectangle** (`eq:rectangle`), positivity of the signed pairing as a hypothesis:
`p(S,T|x,y) ≤ r_A(S|x) + r_B(T|y)` for all outcome subsets `S`, `T`, from the slack identity, the
two ordered-event bounds and `D_C(E,H) ≥ 0` for all effects `E`, `H`. -/
theorem rectangle_bound_of_dc {W U V : PMat D} {Cm : Op (Fin D.m × Fin D.n)}
    (hW : W = U + V + (2 : ℂ) • QC D Cm) (hU : OrderedAB D U) (hV : OrderedBA D V)
    {σ : Op (RA × RB)} (hσ : Density σ)
    (hDC : ∀ (E : Op (Fin D.m × RA)) (H : Op (Fin D.n × RB)), Effect E → Effect H →
      0 ≤ DC D Cm σ E H)
    {chiA : Op (Fin D.m)} (hχA : chiA = omegaA D U + ptraceOut Cm) {chiB : Op (Fin D.n)}
    (hχB : chiB = omegaB D V + ptraceFst Cm)
    (M : Instrument (Fin D.m × RA) (Fin D.d) X A) (N : Instrument (Fin D.n × RB) (Fin D.e) Y B)
    (x : X) (y : Y) (S : Finset A) (T : Finset B) :
    ∑ a ∈ S, ∑ b ∈ T, bornExtended D W σ M N x y a b
      ≤ ∑ a ∈ S, rA D σ chiA M x a + ∑ b ∈ T, rB D σ chiB N y b := by
  have hs := rectangle_slack D hW hχA hχB σ M N x y S T
  have h1 := ordered_event_bound_A D hU hσ (coarse_posSemidef M x S) N y T
  have h2 := ordered_event_bound_B D hV hσ (coarse_posSemidef N y T) M x S
  have h3 := hDC _ _ (coarseEffect_effect M x S) (coarseEffect_effect N y T)
  linarith

/-- **Every rectangle** (`eq:rectangle`) for the manuscript's diagonal `C = diagonal (cDC …)`
(`eq:C`): `D_C ≥ 0` by `DC_nonneg`. -/
theorem rectangle_bound {W U V : PMat D} {Cm : Op (Fin D.m × Fin D.n)}
    (hW : W = U + V + (2 : ℂ) • QC D Cm) (hU : OrderedAB D U) (hV : OrderedBA D V)
    {i0 i1 : Fin D.m} {j0 j1 : Fin D.n} (hC : Cm = Matrix.diagonal (cDC i0 i1 j0 j1))
    {chiA : Op (Fin D.m)} (hχA : chiA = omegaA D U + ptraceOut Cm) {chiB : Op (Fin D.n)}
    (hχB : chiB = omegaB D V + ptraceFst Cm) {σ : Op (RA × RB)} (hσ : Density σ)
    (M : Instrument (Fin D.m × RA) (Fin D.d) X A) (N : Instrument (Fin D.n × RB) (Fin D.e) Y B)
    (x : X) (y : Y) (S : Finset A) (T : Finset B) :
    ∑ a ∈ S, ∑ b ∈ T, bornExtended D W σ M N x y a b
      ≤ ∑ a ∈ S, rA D σ chiA M x a + ∑ b ∈ T, rB D σ chiB N y b :=
  rectangle_bound_of_dc D hW hU hV hσ (fun _ _ hE hH => DC_nonneg D hC hσ.1 hE hH) hχA hχB
    M N x y S T

/-- **Public interface for `EC/Bridge`**, positivity of the signed pairing as a hypothesis:
nonnegative setting-local endpoint arrays of mass `1/2` bounding every rectangle. -/
theorem rectangle_interface_of_dc {W U V : PMat D} {Cm : Op (Fin D.m × Fin D.n)}
    (hW : W = U + V + (2 : ℂ) • QC D Cm) (hU : OrderedAB D U) (hV : OrderedBA D V)
    {σ : Op (RA × RB)} (hσ : Density σ)
    (hDC : ∀ (E : Op (Fin D.m × RA)) (H : Op (Fin D.n × RB)), Effect E → Effect H →
      0 ≤ DC D Cm σ E H)
    {chiA : Op (Fin D.m)} (hχA : chiA = omegaA D U + ptraceOut Cm) (hχA_psd : chiA.PosSemidef)
    (hχA_tr : chiA.trace = ((1 / 2 : ℝ) : ℂ)) {chiB : Op (Fin D.n)}
    (hχB : chiB = omegaB D V + ptraceFst Cm) (hχB_psd : chiB.PosSemidef)
    (hχB_tr : chiB.trace = ((1 / 2 : ℝ) : ℂ))
    (M : Instrument (Fin D.m × RA) (Fin D.d) X A) (N : Instrument (Fin D.n × RB) (Fin D.e) Y B) :
    (∀ x a, 0 ≤ rA D σ chiA M x a) ∧ (∀ y b, 0 ≤ rB D σ chiB N y b) ∧
    (∀ x, ∑ a, rA D σ chiA M x a = 1 / 2) ∧ (∀ y, ∑ b, rB D σ chiB N y b = 1 / 2) ∧
    (∀ x y (S : Finset A) (T : Finset B),
      ∑ a ∈ S, ∑ b ∈ T, bornExtended D W σ M N x y a b
        ≤ ∑ a ∈ S, rA D σ chiA M x a + ∑ b ∈ T, rB D σ chiB N y b) :=
  ⟨fun x a => rA_nonneg D hσ.1 hχA_psd M x a, fun y b => rB_nonneg D hσ.1 hχB_psd N y b,
    fun x => sum_rA_half D hσ.2 hχA_tr M x, fun y => sum_rB_half D hσ.2 hχB_tr N y,
    fun x y S T => rectangle_bound_of_dc D hW hU hV hσ hDC hχA hχB M N x y S T⟩

/-- **Public interface for `EC/Bridge`**: for the abstract signed
four-vertex data with the manuscript's diagonal `C`, the endpoint arrays are nonnegative, depend
only on their local setting (by definition), have total masses `1/2`, and bound every rectangle. -/
theorem rectangle_interface {W U V : PMat D} {Cm : Op (Fin D.m × Fin D.n)}
    (hW : W = U + V + (2 : ℂ) • QC D Cm) (hU : OrderedAB D U) (hV : OrderedBA D V)
    {i0 i1 : Fin D.m} {j0 j1 : Fin D.n} (hC : Cm = Matrix.diagonal (cDC i0 i1 j0 j1))
    {chiA : Op (Fin D.m)} (hχA : chiA = omegaA D U + ptraceOut Cm) (hχA_psd : chiA.PosSemidef)
    (hχA_tr : chiA.trace = ((1 / 2 : ℝ) : ℂ)) {chiB : Op (Fin D.n)}
    (hχB : chiB = omegaB D V + ptraceFst Cm) (hχB_psd : chiB.PosSemidef)
    (hχB_tr : chiB.trace = ((1 / 2 : ℝ) : ℂ)) {σ : Op (RA × RB)} (hσ : Density σ)
    (M : Instrument (Fin D.m × RA) (Fin D.d) X A) (N : Instrument (Fin D.n × RB) (Fin D.e) Y B) :
    (∀ x a, 0 ≤ rA D σ chiA M x a) ∧ (∀ y b, 0 ≤ rB D σ chiB N y b) ∧
    (∀ x, ∑ a, rA D σ chiA M x a = 1 / 2) ∧ (∀ y, ∑ b, rB D σ chiB N y b = 1 / 2) ∧
    (∀ x y (S : Finset A) (T : Finset B),
      ∑ a ∈ S, ∑ b ∈ T, bornExtended D W σ M N x y a b
        ≤ ∑ a ∈ S, rA D σ chiA M x a + ∑ b ∈ T, rB D σ chiB N y b) :=
  rectangle_interface_of_dc D hW hU hV hσ (fun _ _ hE hH => DC_nonneg D hC hσ.1 hE hH) hχA hχA_psd
    hχA_tr hχB hχB_psd hχB_tr M N

end Rectangles

/-! ### Concrete instantiation: the signed four-vertex process `W₀` (`eq:centers`) -/

section Concrete

variable (D : Ports)

/-- Alice's reference state `χ_A = θ_m/2` (`eq:reference-states`), complex coordinates. -/
def chiA : Op (Fin D.m) := toC ((1 / 2 : ℚ) • theta D.m)

/-- Bob's reference state `χ_B = θ_n/2` (`eq:reference-states`), complex coordinates. -/
def chiB : Op (Fin D.n) := toC ((1 / 2 : ℚ) • theta D.n)

/-- `Tr_{B_I}` commutes with the rational-to-complex map: `toC (C_A) = Tr_{B_I} (toC C)`. -/
theorem toC_ptrB (Cq : Matrix (Fin D.m × Fin D.n) (Fin D.m × Fin D.n) ℚ) :
    toC (ptrB Cq) = ptraceOut (toC Cq) := by
  ext a a'
  simp [ptrB, ptraceOut_apply]

/-- `Tr_{A_I}` commutes with the rational-to-complex map: `toC (C_B) = Tr_{A_I} (toC C)`. -/
theorem toC_ptrA (Cq : Matrix (Fin D.m × Fin D.n) (Fin D.m × Fin D.n) ℚ) :
    toC (ptrA Cq) = ptraceFst (toC Cq) := by
  ext b b'
  simp [ptrA, ptraceFst_apply]

/-- `χ_A = ω_A(U) + C_A` in complex coordinates (`eq:reference-states`). -/
theorem chiA_eq (h : AllPortsGE2 D) :
    chiA D = omegaA D (toC (U D.m D.d D.n D.e)) + ptraceOut (toC (C D.m D.n)) := by
  rw [chiA, ← reference_state_A h.2.2.1 D.d_pos D.e_pos, toC_add, toC_omegaAq, toC_ptrB]

/-- `χ_B = ω_B(V) + C_B` in complex coordinates (`eq:reference-states`). -/
theorem chiB_eq (h : AllPortsGE2 D) :
    chiB D = omegaB D (toC (V D.m D.d D.n D.e)) + ptraceFst (toC (C D.m D.n)) := by
  rw [chiB, ← reference_state_B h.1 D.d_pos D.e_pos, toC_add, toC_omegaBq, toC_ptrA]

/-- `θ_r/2 = (3/8)|0⟩⟨0| + (1/8)|1⟩⟨1|` (`eq:local-data`). -/
theorem half_theta_eq (r : ℕ) :
    (1 / 2 : ℚ) • theta r = (3 / 8 : ℚ) • proj r 0 + (1 / 8 : ℚ) • proj r 1 := by
  rw [theta]
  module

theorem chiA_posSemidef : (chiA D).PosSemidef := by
  rw [chiA, half_theta_eq, toC_add]
  exact (psd_toC_smul_proj D.m 0 (by norm_num)).add (psd_toC_smul_proj D.m 1 (by norm_num))

theorem chiB_posSemidef : (chiB D).PosSemidef := by
  rw [chiB, half_theta_eq, toC_add]
  exact (psd_toC_smul_proj D.n 0 (by norm_num)).add (psd_toC_smul_proj D.n 1 (by norm_num))

/-- `Tr χ_A = 1/2` (`eq:reference-states`). -/
theorem chiA_trace (hm : 2 ≤ D.m) : (chiA D).trace = ((1 / 2 : ℝ) : ℂ) := by
  rw [chiA, trace_toC, Matrix.trace_smul, trace_theta hm, smul_eq_mul, mul_one]
  norm_num

/-- `Tr χ_B = 1/2` (`eq:reference-states`). -/
theorem chiB_trace (hn : 2 ≤ D.n) : (chiB D).trace = ((1 / 2 : ℝ) : ℂ) := by
  rw [chiB, trace_toC, Matrix.trace_smul, trace_theta hn, smul_eq_mul, mul_one]
  norm_num

/-- `W₀ = U + V + 2 Q_C` in the complex process space with `QC`
(`eq:signed-decomposition`). -/
theorem W0_signed :
    toC (W0 D.m D.d D.n D.e)
      = toC (U D.m D.d D.n D.e) + toC (V D.m D.d D.n D.e) + (2 : ℂ) • QC D (toC (C D.m D.n)) := by
  rw [signed_decomposition_toC D, toC_Qembed_eq_QC]
  norm_num

variable {RA RB X Y A B : Type} [Fintype RA] [Fintype RB] [DecidableEq RA] [DecidableEq RB]
  [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- **Rectangle interface for `W₀`** (all ports `≥ 2`): with `χ_A = θ_m/2`, `χ_B = θ_n/2`, the
endpoint arrays are nonnegative, of mass `1/2`, and bound every rectangle of the extended Born
distribution of `W₀` (`eq:endpoints`, `eq:rectangle`). -/
theorem rectangle_interface_W0 (h : AllPortsGE2 D) {σ : Op (RA × RB)} (hσ : Density σ)
    (M : Instrument (Fin D.m × RA) (Fin D.d) X A) (N : Instrument (Fin D.n × RB) (Fin D.e) Y B) :
    (∀ x a, 0 ≤ rA D σ (chiA D) M x a) ∧ (∀ y b, 0 ≤ rB D σ (chiB D) N y b) ∧
    (∀ x, ∑ a, rA D σ (chiA D) M x a = 1 / 2) ∧ (∀ y, ∑ b, rB D σ (chiB D) N y b = 1 / 2) ∧
    (∀ x y (S : Finset A) (T : Finset B),
      ∑ a ∈ S, ∑ b ∈ T, bornExtended D (toC (W0 D.m D.d D.n D.e)) σ M N x y a b
        ≤ ∑ a ∈ S, rA D σ (chiA D) M x a + ∑ b ∈ T, rB D σ (chiB D) N y b) :=
  rectangle_interface D (W0_signed D) (u_orderedAB D h) (v_orderedBA D h)
    (toC_C_eq_diagonal_cDC h.1 h.2.2.1) (chiA_eq D h) (chiA_posSemidef D) (chiA_trace D h.1)
    (chiB_eq D h) (chiB_posSemidef D) (chiB_trace D h.2.2.1) hσ M N

/-- **Rectangle data for `W₀`** in exactly the `hrect` shape of `ec_of_rectangles` (`EC/Bridge`): for every finite shared ancilla, density `σ`, and extended instruments with finite
alphabets, the endpoint arrays `r_A(·|x) = rA D σ χ_A M x`, `r_B(·|y) = rB D σ χ_B N y`
(`eq:endpoints`) are nonnegative, of mass `1/2`, and dominate every outcome rectangle
(`eq:rectangle`) of the extended Born distribution of `W₀`, in every port dimension `≥ 2`. -/
theorem rectangles_W0 (h : AllPortsGE2 D) :
    ∀ (r s nx ny na nb : ℕ) (σ : Op (Fin (r + 1) × Fin (s + 1))), Density σ →
      ∀ (M : Instrument (Fin D.m × Fin (r + 1)) (Fin D.d) (Fin (nx + 1)) (Fin (na + 1)))
        (N : Instrument (Fin D.n × Fin (s + 1)) (Fin D.e) (Fin (ny + 1)) (Fin (nb + 1))),
        ∃ (eA : Fin (nx + 1) → Fin (na + 1) → ℝ) (eB : Fin (ny + 1) → Fin (nb + 1) → ℝ),
          (∀ x a, 0 ≤ eA x a) ∧ (∀ y b, 0 ≤ eB y b) ∧
          (∀ x, ∑ a, eA x a = 1 / 2) ∧ (∀ y, ∑ b, eB y b = 1 / 2) ∧
          ∀ x y (S : Finset (Fin (na + 1))) (T : Finset (Fin (nb + 1))),
            (∑ a ∈ S, ∑ b ∈ T, bornExtended D (toC (W0 D.m D.d D.n D.e)) σ M N x y a b) ≤
              (∑ a ∈ S, eA x a) + ∑ b ∈ T, eB y b := by
  intro r s nx ny na nb σ hσ M N
  obtain ⟨h1, h2, h3, h4, h5⟩ := rectangle_interface_W0 D h hσ M N
  exact ⟨rA D σ (chiA D) M, rB D σ (chiB D) N, h1, h2, h3, h4, h5⟩

/-- The four-qubit instance (`eq:qubit`): `rectangles_W0` for `W_q = toC (W0 2 2 2 2)`, in the
shape consumed by `ec_of_rectangles wq_valid`. -/
theorem rectangles_qubits :
    ∀ (r s nx ny na nb : ℕ) (σ : Op (Fin (r + 1) × Fin (s + 1))), Density σ →
      ∀ (M : Instrument (Fin 2 × Fin (r + 1)) (Fin 2) (Fin (nx + 1)) (Fin (na + 1)))
        (N : Instrument (Fin 2 × Fin (s + 1)) (Fin 2) (Fin (ny + 1)) (Fin (nb + 1))),
        ∃ (eA : Fin (nx + 1) → Fin (na + 1) → ℝ) (eB : Fin (ny + 1) → Fin (nb + 1) → ℝ),
          (∀ x a, 0 ≤ eA x a) ∧ (∀ y b, 0 ≤ eB y b) ∧
          (∀ x, ∑ a, eA x a = 1 / 2) ∧ (∀ y, ∑ b, eB y b = 1 / 2) ∧
          ∀ x y (S : Finset (Fin (na + 1))) (T : Finset (Fin (nb + 1))),
            (∑ a ∈ S, ∑ b ∈ T, bornExtended qubits (toC (W0 2 2 2 2)) σ M N x y a b) ≤
              (∑ a ∈ S, eA x a) + ∑ b ∈ T, eB y b :=
  rectangles_W0 qubits ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩

end Concrete

end

end CausalNonpurifiability
