module

public import Mathlib

@[expose] public section


/-!
# `CausalNonpurifiability.Definitions.Causality`

Conditional distributions, no-signalling predicates, `Causal` (setting-independent
weight, real components, `eq:causal-definition`), `HalfCausal` (weight fixed at `1/2`,
the shape produced by `eq:causal-components`), and `HalfCausal → Causal`.

Everything here is distribution-level: `Prob X Y A B` is an arbitrary real table
indexed by settings `x : X`, `y : Y` and outcomes `a : A`, `b : B`.  The quantum
side (`ExtensiblyCausal`, which needs `bornExtended` from
`CausalNonpurifiability.Definitions.Instruments`) is declared in that module.

Manuscript anchors: `eq:causal-definition`, Oreshkov–Giarmatzi Def. 3.2 (§2.2).

Conventions: outcome labels are kept even when their probability vanishes; the
components of a causal decomposition are ordinary real distributions, not required
to be quantum-realizable; the weight is quantified *outside* the setting
quantifiers.
-/

set_option autoImplicit false

open Finset

namespace CausalNonpurifiability

/-- A real table `p x y a b` = "probability of outcomes `(a,b)` given settings `(x,y)`"
(`eq:causal-definition`: `p(a,b|x,y)`). No normalization is built in. -/
abbrev Prob (X Y A B : Type) := X → Y → A → B → ℝ

section Definitions

variable {X Y A B : Type}

/-- `Conditional p`: every entry is nonnegative and, for every setting pair, the
outcome table is normalized (`∑ a, ∑ b, p x y a b = 1`).  This is the
"normalized nonnegative distribution" requirement on both components in
`eq:causal-definition`. -/
def Conditional [Fintype A] [Fintype B] (p : Prob X Y A B) : Prop :=
  (∀ x y a b, 0 ≤ p x y a b) ∧ ∀ x y, ∑ a, ∑ b, p x y a b = 1

/-- `NS_AB p`: Alice's marginal `∑ b, p x y a b` does not depend on Bob's setting `y`
(no signalling from Bob to Alice; the constraint on `p^{A≺B}` in
`eq:causal-definition`). -/
def NS_AB [Fintype B] (p : Prob X Y A B) : Prop :=
  ∀ x y y' a, ∑ b, p x y a b = ∑ b, p x y' a b

/-- `NS_BA p`: Bob's marginal `∑ a, p x y a b` does not depend on Alice's setting `x`
(no signalling from Alice to Bob; the constraint on `p^{B≺A}` in
`eq:causal-definition`). -/
def NS_BA [Fintype A] (p : Prob X Y A B) : Prop :=
  ∀ x x' y b, ∑ a, p x y a b = ∑ a, p x' y a b

/-- `Causal p` (`eq:causal-definition`): `p = λ p^{A≺B} + (1-λ) p^{B≺A}` with
`0 ≤ λ ≤ 1`, both components normalized nonnegative distributions,
`p^{A≺B}` non-signalling from Bob to Alice and `p^{B≺A}` non-signalling from
Alice to Bob.  The weight `lam` is chosen *before* the settings and outcomes are
quantified ("The weight λ is the same for all settings"). -/
def Causal [Fintype A] [Fintype B] (p : Prob X Y A B) : Prop :=
  ∃ (lam : ℝ) (pAB pBA : Prob X Y A B),
    0 ≤ lam ∧ lam ≤ 1 ∧
    Conditional pAB ∧ Conditional pBA ∧
    NS_AB pAB ∧ NS_BA pBA ∧
    ∀ x y a b, p x y a b = lam * pAB x y a b + (1 - lam) * pBA x y a b

/-- `HalfCausal p`: the special case `λ = 1/2` of `eq:causal-definition`, which is
the shape delivered by the transport construction (`eq:causal-components`:
`p = ½ p^{A≺B} + ½ p^{B≺A}`). -/
def HalfCausal [Fintype A] [Fintype B] (p : Prob X Y A B) : Prop :=
  ∃ (pAB pBA : Prob X Y A B),
    Conditional pAB ∧ Conditional pBA ∧
    NS_AB pAB ∧ NS_BA pBA ∧
    ∀ x y a b, p x y a b = (1 / 2) * pAB x y a b + (1 / 2) * pBA x y a b

/-- A half-causal distribution is causal (take `λ = 1/2` in `eq:causal-definition`). -/
theorem halfCausal_causal [Fintype A] [Fintype B] {p : Prob X Y A B}
    (h : HalfCausal p) : Causal p := by
  obtain ⟨pAB, pBA, hAB, hBA, hnsAB, hnsBA, hdec⟩ := h
  refine ⟨1 / 2, pAB, pBA, by norm_num, by norm_num, hAB, hBA, hnsAB, hnsBA, ?_⟩
  intro x y a b
  rw [hdec x y a b]
  norm_num

/-- The marginal of a `Conditional` table over Bob's outcomes is nonnegative. -/
theorem Conditional.margA_nonneg [Fintype A] [Fintype B] {p : Prob X Y A B}
    (h : Conditional p) (x : X) (y : Y) (a : A) : 0 ≤ ∑ b, p x y a b :=
  Finset.sum_nonneg fun b _ => h.1 x y a b

/-- The marginal of a `Conditional` table over Alice's outcomes is nonnegative. -/
theorem Conditional.margB_nonneg [Fintype A] [Fintype B] {p : Prob X Y A B}
    (h : Conditional p) (x : X) (y : Y) (b : B) : 0 ≤ ∑ a, p x y a b :=
  Finset.sum_nonneg fun a _ => h.1 x y a b

/-- A causal decomposition of a table is itself a normalized nonnegative table. -/
theorem Causal.conditional [Fintype A] [Fintype B] {p : Prob X Y A B}
    (h : Causal p) : Conditional p := by
  obtain ⟨lam, pAB, pBA, h0, h1, hAB, hBA, -, -, hdec⟩ := h
  refine ⟨fun x y a b => ?_, fun x y => ?_⟩
  · rw [hdec x y a b]
    have := hAB.1 x y a b
    have := hBA.1 x y a b
    have : 0 ≤ 1 - lam := by linarith
    positivity
  · simp only [hdec, Finset.sum_add_distrib, ← Finset.mul_sum, hAB.2 x y, hBA.2 x y]
    ring

end Definitions

end CausalNonpurifiability
