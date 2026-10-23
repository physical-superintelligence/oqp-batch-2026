module

public import Mathlib

/-!
# Open Quantum Problem 43: statement of record

IQOQI Vienna Open Quantum Problem 43 asks: "The question is whether or not any extensibly causal
process is purifiable." This file states the answer, **no**, and the facts that support it, using
only Mathlib. Every theorem below has the placeholder proof `sorry`; `Solution.lean` proves the
same statements from the library `CausalNonpurifiability`, and Comparator checks that the two
files state exactly the same theorems and that the proofs use only the axioms `propext`,
`Quot.sound` and `Classical.choice`.

The definitions are copied verbatim (same names, same bodies, same section variables) from the
library modules named in each section heading, so that the statements below mean exactly what the
library proves. Only the documentation comments are new.

Setting: processes `W` on `A_I ⊗ A_O ⊗ B_I ⊗ B_O` for two parties, Alice (`A`) and Bob (`B`),
whose input and output spaces have finite dimensions `m, d, n, e`; the purifying systems `P'` and
`F'` of the problem are the past and future of the pure process `S` in `Purifiable`.
`docs/FIDELITY.md` maps the problem's wording to these definitions.

Tensor order and conventions: operators on `A_I ⊗ A_O ⊗ B_I ⊗ B_O` are complex matrices indexed by
`((a_I, a_O), (b_I, b_O))`. For a completely positive map `𝒜` with Choi matrix
`J(𝒜) = ∑_{i,j} |i⟩⟨j| ⊗ 𝒜(|i⟩⟨j|)`, the elements of instruments are the transposes
`M = J(𝒜)ᵀ` (the problem's "CJ representations"), so the Born rule is `Tr[W (M ⊗ N)]`; the
definition of purity uses the untransposed Choi matrices `J` of the local channels.
-/

@[expose] public section

set_option autoImplicit false

namespace CausalNonpurifiability

/-! ## Ports and index types (from `CausalNonpurifiability/Linear/Indices.lean`) -/

/-- Port dimensions `(m, d, n, e) = (dim A_I, dim A_O, dim B_I, dim B_O)`, all positive. -/
structure Ports where
  m : ℕ
  d : ℕ
  n : ℕ
  e : ℕ
  positive : 0 < m ∧ 0 < d ∧ 0 < n ∧ 0 < e

/-- Operators on a finite-dimensional space with a fixed basis indexed by `ι`. -/
abbrev Op (ι : Type) := Matrix ι ι ℂ

/-- Generic laboratory index in the order `A_I, A_O, B_I, B_O`, grouped by party:
`((a, o), (b, t))`. -/
abbrev LabIdx (AI AO BI BO : Type) := (AI × AO) × (BI × BO)

/-- Laboratory index of the port dimensions `D`. -/
abbrev LabIndex (D : Ports) := (Fin D.m × Fin D.d) × (Fin D.n × Fin D.e)

/-- Operators on `A_I ⊗ A_O ⊗ B_I ⊗ B_O`: the carrier of process matrices `W`. -/
abbrev PMat (D : Ports) := Op (LabIndex D)

/-- Four qubit ports: `m = d = n = e = 2`. -/
def qubits : Ports := ⟨2, 2, 2, 2, by decide⟩

section Coordinates

variable (AI AO BI BO : Type)

/-- Regrouping that moves `A_O` to the last position: `((a,o),(b,t)) ↦ ((a,(b,t)), o)`. -/
def eqAO : LabIdx AI AO BI BO ≃ (AI × (BI × BO)) × AO where
  toFun x := ((x.1.1, x.2), x.1.2)
  invFun y := ((y.1.1, y.2), y.1.2)
  left_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl
  right_inv := fun ⟨⟨_, ⟨_, _⟩⟩, _⟩ => rfl

/-- Regrouping that moves `B_O` to the last position: `((a,o),(b,t)) ↦ (((a,o),b), t)`. -/
def eqBO : LabIdx AI AO BI BO ≃ ((AI × AO) × BI) × BO where
  toFun x := ((x.1, x.2.1), x.2.2)
  invFun y := (y.1.1, (y.1.2, y.2))
  left_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl
  right_inv := fun ⟨⟨⟨_, _⟩, _⟩, _⟩ => rfl

/-- `B_I B_O` is already last: the identity regrouping. -/
def eqBIBO : LabIdx AI AO BI BO ≃ (AI × AO) × (BI × BO) where
  toFun x := x
  invFun y := y
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- Regrouping that moves `A_I A_O` to the last position: `((a,o),(b,t)) ↦ ((b,t),(a,o))`. -/
def eqAIAO : LabIdx AI AO BI BO ≃ (BI × BO) × (AI × AO) where
  toFun x := (x.2, x.1)
  invFun y := (y.2, y.1)
  left_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl
  right_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl

end Coordinates

/-! ## Partial trace (from `CausalNonpurifiability/Linear/PartialTrace.lean`) -/

section PartialTrace

open scoped Kronecker Matrix ComplexOrder

variable {I O : Type} [Fintype O]

/-- Partial trace over the second factor: `(Tr_O T)_{i,j} = ∑_o T_{(i,o),(j,o)}`. -/
def ptraceOut (T : Op (I × O)) : Op I := fun i j => ∑ o, T (i, o) (j, o)

theorem ptraceOut_apply (T : Op (I × O)) (i j : I) :
    ptraceOut T i j = ∑ o, T (i, o) (j, o) := rfl

theorem ptraceOut_add (S T : Op (I × O)) : ptraceOut (S + T) = ptraceOut S + ptraceOut T := by
  ext i j
  simp only [ptraceOut_apply, Matrix.add_apply, Finset.sum_add_distrib]

theorem ptraceOut_smul (c : ℂ) (T : Op (I × O)) : ptraceOut (c • T) = c • ptraceOut T := by
  ext i j
  simp only [ptraceOut_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]

end PartialTrace

/-! ## Replacement maps and the ancilla extension
(from `CausalNonpurifiability/Linear/Replacement.lean`) -/

section Replacement

set_option linter.unusedSectionVars false

open scoped Kronecker ComplexOrder

noncomputable section

/-- `1/|Y|` as a complex number. -/
def invCard (Y : Type) [Fintype Y] : ℂ := ((Fintype.card Y : ℂ))⁻¹

section Generic

variable {I Y : Type} [Fintype I] [Fintype Y] [DecidableEq I] [DecidableEq Y]

/-- Replacement of the last factor: `R_Y T = (Tr_Y T) ⊗ I_Y / |Y|` on `Op (I × Y)`. -/
def replaceLast (T : Op (I × Y)) : Op (I × Y) := invCard Y • (ptraceOut T ⊗ₖ (1 : Op Y))

omit [Fintype I] [DecidableEq I] in
theorem replaceLast_add (S T : Op (I × Y)) :
    replaceLast (S + T) = replaceLast S + replaceLast T := by
  unfold replaceLast
  rw [ptraceOut_add, Matrix.add_kronecker, smul_add]

omit [Fintype I] [DecidableEq I] in
theorem replaceLast_smul (c : ℂ) (T : Op (I × Y)) : replaceLast (c • T) = c • replaceLast T := by
  unfold replaceLast
  rw [ptraceOut_smul, Matrix.smul_kronecker, smul_comm]

/-- `replaceLast` as a `ℂ`-linear map. -/
def replaceLastₗ : Op (I × Y) →ₗ[ℂ] Op (I × Y) where
  toFun := replaceLast
  map_add' := replaceLast_add
  map_smul' := replaceLast_smul

end Generic

section Via

variable {ι I Y : Type} [Fintype ι] [DecidableEq ι] [Fintype I] [Fintype Y] [DecidableEq I]
  [DecidableEq Y]

/-- Replacement of the factor `Y` singled out by a regrouping `e : ι ≃ I × Y`. -/
def replaceVia (e : ι ≃ I × Y) : Op ι →ₗ[ℂ] Op ι :=
  (Matrix.reindexLinearEquiv ℂ ℂ e.symm e.symm).toLinearMap ∘ₗ replaceLastₗ ∘ₗ
    (Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap

end Via

section Named

variable {AI AO BI BO : Type} [Fintype AI] [Fintype AO] [Fintype BI] [Fintype BO]
  [DecidableEq AI] [DecidableEq AO] [DecidableEq BI] [DecidableEq BO]

/-- `R_{A_O} W = Tr_{A_O} W ⊗ I_{A_O} / d`, factors kept in their order. -/
def R_AO : Op (LabIdx AI AO BI BO) →ₗ[ℂ] Op (LabIdx AI AO BI BO) := replaceVia (eqAO AI AO BI BO)

/-- `R_{B_O} W = Tr_{B_O} W ⊗ I_{B_O} / e`. -/
def R_BO : Op (LabIdx AI AO BI BO) →ₗ[ℂ] Op (LabIdx AI AO BI BO) := replaceVia (eqBO AI AO BI BO)

/-- `R_{B_I B_O} W = Tr_{B_I B_O} W ⊗ I_{B_I B_O} / (n e)`. -/
def R_BIBO : Op (LabIdx AI AO BI BO) →ₗ[ℂ] Op (LabIdx AI AO BI BO) :=
  replaceVia (eqBIBO AI AO BI BO)

/-- `R_{A_I A_O} W = Tr_{A_I A_O} W ⊗ I_{A_I A_O} / (m d)`. -/
def R_AIAO : Op (LabIdx AI AO BI BO) →ₗ[ℂ] Op (LabIdx AI AO BI BO) :=
  replaceVia (eqAIAO AI AO BI BO)

end Named

section Extended

variable {AI AO BI BO RA RB : Type}

/-- `W ⊗ σ` with the ancilla factors `R_A`, `R_B` attached to the inputs, in the order
`((A_I × R_A) × A_O) × ((B_I × R_B) × B_O)`. -/
def extended (W : Op (LabIdx AI AO BI BO)) (σ : Op (RA × RB)) :
    Op (LabIdx (AI × RA) AO (BI × RB) BO) :=
  fun x y =>
    W ((x.1.1.1, x.1.2), (x.2.1.1, x.2.2)) ((y.1.1.1, y.1.2), (y.2.1.1, y.2.2)) *
      σ (x.1.1.2, x.2.1.2) (y.1.1.2, y.2.1.2)

end Extended

end

end Replacement

/-! ## Process matrices (from `CausalNonpurifiability/Definitions/ProcessCore.lean`)

OQP 43: "`W ∈ A^1_I ⊗ A^1_O ⊗ ... ⊗ A^N_I ⊗ A^N_O` is a process matrix with `A^i_I` and `A^i_O`
being the input and the output Hilbert spaces of party `i`. The set of process matrices is
defined by requiring that probabilities are well-defined [1,2]." -/

section Process

open scoped Kronecker ComplexOrder

noncomputable section

section GenLV

variable {AI AO BI BO : Type} [Fintype AI] [Fintype AO] [Fintype BI] [Fintype BO]
  [DecidableEq AI] [DecidableEq AO] [DecidableEq BI] [DecidableEq BO]

/-- The linear conditions of a bipartite process matrix: `W` is Hermitian,
`(1 - R_{A_O}) R_{B_I B_O} W = 0`, `(1 - R_{B_O}) R_{A_I A_O} W = 0` and
`(1 - R_{A_O})(1 - R_{B_O}) W = 0`. -/
def GenLV (W : Op (LabIdx AI AO BI BO)) : Prop :=
  W.IsHermitian ∧
  R_BIBO W - R_AO (R_BIBO W) = 0 ∧
  R_AIAO W - R_BO (R_AIAO W) = 0 ∧
  W - R_AO W - R_BO W + R_AO (R_BO W) = 0

end GenLV

variable (D : Ports)

/-- The linear conditions on `A_I ⊗ A_O ⊗ B_I ⊗ B_O` with dimensions `D`. -/
def InLV (W : PMat D) : Prop := GenLV W

/-- `W` is a process matrix: it satisfies the linear conditions, `W ≥ 0`, and `Tr W = d e`.
For positive `W` these are exactly the conditions under which every pair of local channels gives
total probability one (the problem's "probabilities are well-defined"). -/
def Valid (W : PMat D) : Prop :=
  InLV D W ∧ W.PosSemidef ∧ Matrix.trace W = ((D.d * D.e : ℕ) : ℂ)

/-- The cone of processes in which Alice acts before Bob: linear conditions, `T ≥ 0`, and
`R_{B_O} T = T` (no trace condition). -/
def OrderedAB (T : PMat D) : Prop :=
  InLV D T ∧ T.PosSemidef ∧ R_BO T = T

/-- The cone of processes in which Bob acts before Alice: linear conditions, `T ≥ 0`, and
`R_{A_O} T = T` (no trace condition). -/
def OrderedBA (T : PMat D) : Prop :=
  InLV D T ∧ T.PosSemidef ∧ R_AO T = T

/-- Causal separability: a process matrix that is a sum of an operator ordered `A` before `B`
and one ordered `B` before `A`. -/
def CausallySeparable (W : PMat D) : Prop :=
  Valid D W ∧ ∃ U V : PMat D, OrderedAB D U ∧ OrderedBA D V ∧ W = U + V

end

end Process

/-! ## Causal distributions (from `CausalNonpurifiability/Definitions/Causality.lean`)

OQP 43: "The condition for a bipartite probability distribution to be "causal", i.e., not to
violate any causal inequality, is that it can be decomposed into a convex combination of a
probability distribution which is no-signaling from Bob to Alice (`p^{A<B}`) and a probability
distribution which is no-signaling from Alice to Bob (`p^{B<A}`):
`p_causal = λ p^{A<B} + (1 - λ) p^{B<A}`." -/

section Causality

open Finset

/-- A real table `p x y a b`, read as the probability of outcomes `(a, b)` for settings `(x, y)`. -/
abbrev Prob (X Y A B : Type) := X → Y → A → B → ℝ

section Definitions

variable {X Y A B : Type}

/-- Every entry is nonnegative and, for every pair of settings, the outcomes sum to one. -/
def Conditional [Fintype A] [Fintype B] (p : Prob X Y A B) : Prop :=
  (∀ x y a b, 0 ≤ p x y a b) ∧ ∀ x y, ∑ a, ∑ b, p x y a b = 1

/-- No signalling from Bob to Alice: Alice's marginal does not depend on Bob's setting `y`. -/
def NS_AB [Fintype B] (p : Prob X Y A B) : Prop :=
  ∀ x y y' a, ∑ b, p x y a b = ∑ b, p x y' a b

/-- No signalling from Alice to Bob: Bob's marginal does not depend on Alice's setting `x`. -/
def NS_BA [Fintype A] (p : Prob X Y A B) : Prop :=
  ∀ x x' y b, ∑ a, p x y a b = ∑ a, p x' y a b

/-- `p` is causal: `p = λ p^{A<B} + (1 - λ) p^{B<A}` with `0 ≤ λ ≤ 1` (one `λ` for all settings),
both components probability distributions, `p^{A<B}` no-signalling from Bob to Alice and
`p^{B<A}` no-signalling from Alice to Bob. -/
def Causal [Fintype A] [Fintype B] (p : Prob X Y A B) : Prop :=
  ∃ (lam : ℝ) (pAB pBA : Prob X Y A B),
    0 ≤ lam ∧ lam ≤ 1 ∧
    Conditional pAB ∧ Conditional pBA ∧
    NS_AB pAB ∧ NS_BA pBA ∧
    ∀ x y a b, p x y a b = lam * pAB x y a b + (1 - lam) * pBA x y a b

end Definitions

end Causality

/-! ## Instruments and extensible causality
(from `CausalNonpurifiability/Definitions/InstrumentsCore.lean`)

OQP 43: "The processes are called *causal* if they do not violate causal inequalities, and they
are called *extensibly causal* if they remain causal even under extension with input systems in an
arbitrary joint quantum state [3]." -/

section Instruments

open scoped ComplexOrder Kronecker MatrixOrder

open Matrix

/-- An instrument with settings `X` and outcomes `A` from `I` to `O`: its elements are positive
matrices `M_{a|x} = J(𝒜_{a|x})ᵀ` on `I ⊗ O`, the transposed Choi matrices of the completely
positive maps `𝒜_{a|x}`, with `Tr_O ∑_a M_{a|x} = 1_I` for every setting `x`. -/
structure Instrument (I O X A : Type) [Fintype I] [Fintype O] [Fintype A] [DecidableEq I] where
  /-- The element `M_{a|x}` for setting `x` and outcome `a`. -/
  elem : X → A → Op (I × O)
  /-- Positivity of every element. -/
  positive : ∀ x a, (elem x a).PosSemidef
  /-- Normalization `Tr_O ∑_a M_{a|x} = 1_I`. -/
  normalized : ∀ x, ptraceOut (∑ a, elem x a) = 1

/-- A density operator: positive with trace one. -/
def Density {I : Type} [Fintype I] (σ : Op I) : Prop :=
  σ.PosSemidef ∧ σ.trace = 1

section ExtendInput

variable (D : Ports) {RA RB : Type}

/-- The process `W` extended by the ancilla state `σ` on `R_A ⊗ R_B`, which enters Alice's and
Bob's inputs. -/
def extendInput (W : PMat D) (σ : Op (RA × RB)) :
    Op (LabIdx (Fin D.m × RA) (Fin D.d) (Fin D.n × RB) (Fin D.e)) :=
  extended W σ

end ExtendInput

section Born

variable (D : Ports) {RA RB X Y A B : Type} [Fintype RA] [DecidableEq RA] [Fintype RB]
  [DecidableEq RB] [Fintype A] [Fintype B]

/-- The probabilities `p(a, b | x, y) = Re Tr[(W ⊗ σ)(M_{a|x} ⊗ N_{b|y})]` of the extended
process with instruments `M` of Alice (on `A_I ⊗ R_A → A_O`) and `N` of Bob
(on `B_I ⊗ R_B → B_O`). For positive `W` and `σ` the trace is real (library theorem
`bornExtended_im_zero`), so taking the real part loses nothing. -/
noncomputable def bornExtended (W : PMat D) (σ : Op (RA × RB))
    (M : Instrument (Fin D.m × RA) (Fin D.d) X A) (N : Instrument (Fin D.n × RB) (Fin D.e) Y B) :
    Prob X Y A B :=
  fun x y a b => ((extendInput D W σ * (M.elem x a ⊗ₖ N.elem y b)).trace).re

end Born

/-- **Extensibly causal** process: `W` is a process matrix and, for every finite ancilla
`R_A ⊗ R_B` (dimensions `r + 1` and `s + 1`, unbounded), every density operator `σ` on it
(entangled states included) and every pair of instruments on the extended inputs (any finite
numbers of settings and outcomes), the resulting distribution is causal. -/
def ExtensiblyCausal (D : Ports) (W : PMat D) : Prop :=
  Valid D W ∧
    ∀ (r s nx ny na nb : ℕ) (σ : Op (Fin (r + 1) × Fin (s + 1))), Density σ →
      ∀ (M : Instrument (Fin D.m × Fin (r + 1)) (Fin D.d) (Fin (nx + 1)) (Fin (na + 1)))
        (N : Instrument (Fin D.n × Fin (s + 1)) (Fin D.e) (Fin (ny + 1)) (Fin (nb + 1))),
        Causal (bornExtended D W σ M N)

end Instruments

/-! ## Purity and purifiability (from `CausalNonpurifiability/Definitions/Purity.lean`)

OQP 43: "The process matrices are called *pure* if after extending them with a global past state
from the Hilbert space `P` and a global future state from the Hilbert space `F`, they induce a
unitary transformation from the past to the future whenever unitary transformations are also
applied in the local laboratories [5]. Then a process `W ∈ P ⊗ A^1_I ⊗ A^1_O ⊗ ... ⊗ A^N_I ⊗ A^N_O
⊗ F` is called *purifiable* if one can recover it from a pure process
`S ∈ P ⊗ P' ⊗ A^1_I ⊗ A^1_O ⊗ ... ⊗ A^N_I ⊗ A^N_O ⊗ F ⊗ F'` by inputing the state `|0⟩` in `P'`
and tracing out the state from `F'`: `W = Tr_{P'F'} [S^T (|0⟩⟨0|^{P'} ⊗ I^{F'})]`."

Here `W` is an operator on `A_I ⊗ A_O ⊗ B_I ⊗ B_O`, and the past and future of `S` are the
purifying systems `P'` and `F'`. "Pure" is as in reference [5] (Araújo, Feix, Navascués,
Brukner): the local unitaries may act on additional systems of any finite size. Channels are given
here by their untransposed Choi matrices `J` indexed by `(input, output)`; the link product
carries the partial transpose on the laboratory factors, so that with trivial past and future and
no additional systems it is the Born rule `Tr[S (J_Aᵀ ⊗ J_Bᵀ)]`. -/

section Purity

open Matrix
open scoped ComplexOrder Kronecker

noncomputable section

/-- Operators on `P ⊗ (A_I ⊗ A_O ⊗ B_I ⊗ B_O) ⊗ F` with global past `P` of dimension `p + 1` and
global future `F` of dimension `f + 1`. -/
abbrev HigherOp (D : Ports) (p f : ℕ) : Type :=
  Op ((Fin (p + 1) × LabIndex D) × Fin (f + 1))

/-- Choi matrices of Alice's channels `A_I ⊗ E_A → A_O ⊗ E'_A`, with additional systems `E_A`
and `E'_A` of dimensions `a + 1` and `a' + 1`. -/
abbrev ExtChoiA (D : Ports) (a a' : ℕ) : Type :=
  Op ((Fin D.m × Fin (a + 1)) × (Fin D.d × Fin (a' + 1)))

/-- Choi matrices of Bob's channels `B_I ⊗ E_B → B_O ⊗ E'_B`, with additional systems `E_B`
and `E'_B` of dimensions `b + 1` and `b' + 1`. -/
abbrev ExtChoiB (D : Ports) (b b' : ℕ) : Type :=
  Op ((Fin D.n × Fin (b + 1)) × (Fin D.e × Fin (b' + 1)))

/-- Input index of the linked channel: the past `P` and the additional inputs `E_A`, `E_B`. -/
abbrev LinkIn (p a b : ℕ) : Type := Fin (p + 1) × (Fin (a + 1) × Fin (b + 1))

/-- Output index of the linked channel: the future `F` and the additional outputs `E'_A`,
`E'_B`. -/
abbrev LinkOut (f a' b' : ℕ) : Type := Fin (f + 1) × (Fin (a' + 1) × Fin (b' + 1))

/-- `J` is the Choi matrix of a channel: positive (complete positivity) with `Tr_O J = 1_I`
(trace preservation). -/
def ChannelChoi {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] (J : Op (I × O)) : Prop :=
  J.PosSemidef ∧ ptraceOut J = 1

/-- `J` is the Choi matrix of a unitary channel `ρ ↦ U ρ U†`:
`J_{(i,o),(j,o')} = U_{o,i} · conj(U_{o',j})` with `Uᴴ U = 1` and `U Uᴴ = 1`. -/
def UnitaryChoi {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (J : Op (I × O)) : Prop :=
  ∃ U : Matrix O I ℂ,
    Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
    ∀ i o j o', J (i, o) (j, o') = U o i * star (U o' j)

/-- The channel from `P ⊗ E_A ⊗ E_B` to `F ⊗ E'_A ⊗ E'_B` obtained by inserting Alice's channel
`J_A` and Bob's channel `J_B` into `S`: the link product `Tr_L [S^{T_L} (J_A ⊗ J_B)]`, with the
partial transpose on the laboratory factors `L = A_I A_O B_I B_O`, written entrywise. -/
def link (D : Ports) {p f a a' b b' : ℕ}
    (S : HigherOp D p f) (JA : ExtChoiA D a a') (JB : ExtChoiB D b b') :
    Op (LinkIn p a b × LinkOut f a' b') :=
  Matrix.of fun u v =>
    ∑ l : LabIndex D, ∑ l' : LabIndex D,
      S ((u.1.1, l), u.2.1) ((v.1.1, l'), v.2.1) *
        JA ((l.1.1, u.1.2.1), (l.1.2, u.2.2.1)) ((l'.1.1, v.1.2.1), (l'.1.2, v.2.2.1)) *
        JB ((l.2.1, u.1.2.2), (l.2.2, u.2.2.2)) ((l'.2.1, v.1.2.2), (l'.2.2, v.2.2.2))

/-- `S` is deterministic: `S ≥ 0`, and for all finite additional systems and all pairs of local
channels the linked map is again a channel. -/
def Deterministic (D : Ports) {p f : ℕ} (S : HigherOp D p f) : Prop :=
  S.PosSemidef ∧
  ∀ a a' b b' : ℕ,
  ∀ (JA : ExtChoiA D a a') (JB : ExtChoiB D b b'),
    ChannelChoi JA → ChannelChoi JB → ChannelChoi (link D S JA JB)

/-- `S` is pure: it is deterministic, and for all finite additional systems every pair of local
unitary channels is mapped to a unitary channel from the past to the future. -/
def Pure (D : Ports) {p f : ℕ} (S : HigherOp D p f) : Prop :=
  Deterministic D S ∧
  ∀ a a' b b' : ℕ,
  ∀ (JA : ExtChoiA D a a') (JB : ExtChoiB D b b'),
    UnitaryChoi JA → UnitaryChoi JB → UnitaryChoi (link D S JA JB)

/-- Input `|0⟩` into the past of `S` and trace out its future:
`(l, l') ↦ ∑_z S_{((0,l),z),((0,l'),z)}`, that is `Tr_F [⟨0|_P S |0⟩_P]`. -/
def reducePastFuture (D : Ports) {p f : ℕ} (S : HigherOp D p f) : PMat D :=
  Matrix.of fun l l' => ∑ z : Fin (f + 1), S ((0, l), z) ((0, l'), z)

/-- `W` is purifiable: for some finite dimensions of past and future there is a pure `S` from
which `W` is recovered by inputting `|0⟩` in the past and tracing out the future. The problem's
formula has `S^T` in place of `S`; `purifiable_iff_transpose_formula` below shows that the two
readings define the same processes. -/
def Purifiable (D : Ports) (W : PMat D) : Prop :=
  ∃ (p f : ℕ) (S : HigherOp D p f), Pure D S ∧ reducePastFuture D S = W

end

end Purity

/-! ## The four-qubit process `W_q` (from `CausalNonpurifiability/Data/Local.lean`; `Wq` itself
from `CausalNonpurifiability/StatementCore.lean`)

`W_q = (20 IIII + 10 ZIII + 10 IIZI + 5 ZIZI + 4 IZZI + 4 ZIXZ)/80`; the library builds it as the
case `m = d = n = e = 2` of a rational construction `W0 m d n e`, and `wq_pauli_form` below states
the Pauli form. -/

section Witness

open Matrix
open scoped Kronecker

/-- Laboratory index with explicit dimensions `(m, d, n, e)`. -/
abbrev Lab (m d n e : ℕ) : Type := (Fin m × Fin d) × (Fin n × Fin e)

/-- Entrywise image of a rational matrix in the complex matrices. -/
noncomputable abbrev toC {ι κ : Type*} (A : Matrix ι κ ℚ) : Matrix ι κ ℂ := A.map (algebraMap ℚ ℂ)

/-- `|k⟩⟨k|` on `Fin r` (zero when `k ≥ r`). -/
def proj (r k : ℕ) : Matrix (Fin r) (Fin r) ℚ :=
  diagonal fun i => if i.val = k then 1 else 0

/-- `|k⟩⟨l|` on `Fin r` (zero when `k ≥ r` or `l ≥ r`). -/
def unit (r k l : ℕ) : Matrix (Fin r) (Fin r) ℚ :=
  of fun i j => if i.val = k ∧ j.val = l then 1 else 0

/-- `P_r = |0⟩⟨0| + |1⟩⟨1|`. -/
def P (r : ℕ) : Matrix (Fin r) (Fin r) ℚ := proj r 0 + proj r 1

/-- `Z_r = |0⟩⟨0| - |1⟩⟨1|`. -/
def Z (r : ℕ) : Matrix (Fin r) (Fin r) ℚ := proj r 0 - proj r 1

/-- `X_r = |0⟩⟨1| + |1⟩⟨0|`. -/
def X (r : ℕ) : Matrix (Fin r) (Fin r) ℚ := unit r 0 1 + unit r 1 0

/-- `Z_r^+ = I_r - 2 |1⟩⟨1|`. -/
def Zplus (r : ℕ) : Matrix (Fin r) (Fin r) ℚ := 1 - (2 : ℚ) • proj r 1

/-- `θ_r = (3 |0⟩⟨0| + |1⟩⟨1|)/4`. -/
def theta (r : ℕ) : Matrix (Fin r) (Fin r) ℚ := (1 / 4 : ℚ) • ((3 : ℚ) • proj r 0 + proj r 1)

/-- `A ⊗ B ⊗ C ⊗ D` on `A_I ⊗ A_O ⊗ B_I ⊗ B_O`, grouped as `(A ⊗ B) ⊗ (C ⊗ D)`. -/
def kron4 {m d n e : ℕ} (A : Matrix (Fin m) (Fin m) ℚ) (B : Matrix (Fin d) (Fin d) ℚ)
    (C : Matrix (Fin n) (Fin n) ℚ) (D : Matrix (Fin e) (Fin e) ℚ) :
    Matrix (Lab m d n e) (Lab m d n e) ℚ :=
  (A ⊗ₖ B) ⊗ₖ (C ⊗ₖ D)

section Construction
variable (m d n e : ℕ)

/-- `G_A = P_m ⊗ Z_d^+ ⊗ Z_n ⊗ I_e`. -/
def GA : Matrix (Lab m d n e) (Lab m d n e) ℚ := kron4 (P m) (Zplus d) (Z n) 1

/-- `G_B = Z_m ⊗ I_d ⊗ X_n ⊗ Z_e^+`. -/
def GB : Matrix (Lab m d n e) (Lab m d n e) ℚ := kron4 (Z m) 1 (X n) (Zplus e)

variable {m n}

/-- `Q_C = C^{A_I B_I} ⊗ I^{A_O B_O}`:
`(Q_C)_{(a,o,b,t),(a',o',b',t')} = C_{(a,b),(a',b')} δ_{o o'} δ_{t t'}`. -/
def Qembed (C : Matrix (Fin m × Fin n) (Fin m × Fin n) ℚ) :
    Matrix (Lab m d n e) (Lab m d n e) ℚ :=
  of fun x y =>
    C (x.1.1, x.2.1) (y.1.1, y.2.1) * (if x.1.2 = y.1.2 then 1 else 0) *
      (if x.2.2 = y.2.2 then 1 else 0)

variable (m n)

/-- `Q_{θ_m ⊗ θ_n} = θ_m ⊗ I_d ⊗ θ_n ⊗ I_e` (in the tensor order `A_I A_O B_I B_O`). -/
def Qtheta : Matrix (Lab m d n e) (Lab m d n e) ℚ := Qembed d e (theta m ⊗ₖ theta n)

/-- `W_0 = Q_{θ_m ⊗ θ_n} + (G_A + G_B)/20`. -/
def W0 : Matrix (Lab m d n e) (Lab m d n e) ℚ :=
  Qtheta m d n e + (1 / 20 : ℚ) • (GA m d n e + GB m d n e)

end Construction

end Witness

/-- The four-qubit process `W_q = W_0` at `m = d = n = e = 2`, as a complex matrix on
`A_I ⊗ A_O ⊗ B_I ⊗ B_O`. -/
noncomputable def Wq : PMat qubits := toC (W0 2 2 2 2)

section OCB

open Matrix

/-- The process of Oreshkov, Costa and Brukner, `W_OCB = (IIII + (IZZI + ZIXZ)/√2)/4`, which
violates a causal inequality (from `CausalNonpurifiability/Definitions/OCB.lean`). -/
noncomputable def WOCB : Matrix (Lab 2 2 2 2) (Lab 2 2 2 2) ℂ :=
  ((1 / 4 : ℝ) : ℂ) • toC (kron4 1 1 1 1) +
    ((1 / (4 * Real.sqrt 2) : ℝ) : ℂ) •
      toC (kron4 1 !![1, 0; 0, -1] !![1, 0; 0, -1] 1 +
        kron4 !![1, 0; 0, -1] 1 !![0, 1; 1, 0] !![1, 0; 0, -1])

end OCB

end CausalNonpurifiability

/-! ## The statements -/

open scoped ComplexOrder Kronecker Matrix

namespace CausalNonpurifiability.OQP43

/-- **Problem 43 is answered in the negative.** OQP 43: "The question is whether or not any
extensibly causal process is purifiable." Not every extensibly causal process is purifiable: there
is an extensibly causal process on four qubit ports that is not purifiable. -/
theorem not_all_extensiblyCausal_purifiable :
    ∃ W : PMat qubits, ExtensiblyCausal qubits W ∧ ¬ Purifiable qubits W := by
  sorry

/-- **Theorem 1.1 of the paper.** `W_q` is a process matrix of full rank (positive definite); it
is extensibly causal and causally nonseparable, and it is not purifiable. -/
theorem theorem_1_1 :
    Valid qubits Wq ∧ Wq.PosDef ∧ ExtensiblyCausal qubits Wq ∧ ¬ CausallySeparable qubits Wq ∧
      ¬ Purifiable qubits Wq := by
  sorry

/-- **The Pauli form of `W_q`**:
`W_q = (20 IIII + 10 ZIII + 10 IIZI + 5 ZIZI + 4 IZZI + 4 ZIXZ)/80`, with `Z = diag(1, -1)`,
`X = [[0, 1], [1, 0]]` and words in the order `A_I A_O B_I B_O`. -/
theorem wq_pauli_form :
    Wq = toC (W0 2 2 2 2) ∧
      W0 2 2 2 2 = (1 / 80 : ℚ) • ((20 : ℚ) • kron4 1 1 1 1 +
        (10 : ℚ) • kron4 !![1, 0; 0, -1] 1 1 1 + (10 : ℚ) • kron4 1 1 !![1, 0; 0, -1] 1 +
        (5 : ℚ) • kron4 !![1, 0; 0, -1] 1 !![1, 0; 0, -1] 1 +
        (4 : ℚ) • kron4 1 !![1, 0; 0, -1] !![1, 0; 0, -1] 1 +
        (4 : ℚ) • kron4 !![1, 0; 0, -1] 1 !![0, 1; 1, 0] !![1, 0; 0, -1]) := by
  sorry

/-- **The problem's own formula.** OQP 43 recovers `W` as `Tr_{P'F'} [S^T (|0⟩⟨0|^{P'} ⊗
I^{F'})]`, with the transposed process `S^T`. A process is purifiable in that sense exactly when it
is purifiable in the sense of `Purifiable` (which uses `S` itself). -/
theorem purifiable_iff_transpose_formula (D : Ports) (W : PMat D) :
    Purifiable D W ↔
      ∃ (p f : ℕ) (S : HigherOp D p f), Pure D S ∧ (reducePastFuture D S)ᵀ = W := by
  sorry

/-- **Process matrices are the operators with well-defined probabilities.** OQP 43: "The set of
process matrices is defined by requiring that probabilities are well-defined [1,2]." For positive
`W`, the conditions in `Valid` hold exactly when every pair of local channels, given by
transposed Choi matrices `M ≥ 0` on `A_I ⊗ A_O` with `Tr_{A_O} M = 1` and `N ≥ 0` on `B_I ⊗ B_O`
with `Tr_{B_O} N = 1`, gives total probability `Tr[W (M ⊗ N)] = 1`. -/
theorem valid_iff_channels_normalized (D : Ports) {W : PMat D} (hW : W.PosSemidef) :
    Valid D W ↔ ∀ (Mt : Op (Fin D.m × Fin D.d)) (Nt : Op (Fin D.n × Fin D.e)),
      Mt.PosSemidef → ptraceOut Mt = 1 → Nt.PosSemidef → ptraceOut Nt = 1 →
      (W * (Mt ⊗ₖ Nt)).trace = 1 := by
  sorry

/-- **A purifiable process in every dimension.** For all port dimensions, the white-noise process
`I/(mn)`, in which each party receives the maximally mixed state, is a process matrix, it is
ordered both ways, and it is purifiable. -/
theorem white_process_purifiable (D : Ports) :
    Valid D ((1 / ((D.m : ℂ) * D.n)) • (1 : PMat D)) ∧
      OrderedAB D ((1 / ((D.m : ℂ) * D.n)) • (1 : PMat D)) ∧
      OrderedBA D ((1 / ((D.m : ℂ) * D.n)) • (1 : PMat D)) ∧
      Purifiable D ((1 / ((D.m : ℂ) * D.n)) • (1 : PMat D)) := by
  sorry

/-- **A distribution that is not causal.** The two-way signalling table
`p(a, b | x, y) = [a = y][b = x]` on bits is not causal. -/
theorem swap_table_not_causal :
    ¬ Causal (fun (x y a b : Fin 2) => if a = y ∧ b = x then (1 : ℝ) else 0) := by
  sorry

/-- **A process matrix that is not extensibly causal.** The process `W_OCB` of Oreshkov, Costa and
Brukner is a process matrix that is not extensibly causal. -/
theorem ocb_process_not_extensiblyCausal :
    Valid qubits WOCB ∧ ¬ ExtensiblyCausal qubits WOCB := by
  sorry

/-- **The answer for every tuple of port dimensions.** For two parties with port dimensions
`D = (m, d, n, e)`, every extensibly causal process is purifiable if and only if one of the four
dimensions is `1`. -/
theorem dimension_dichotomy (D : Ports) :
    (∀ W : PMat D, ExtensiblyCausal D W → Purifiable D W) ↔
      min D.m (min D.d (min D.n D.e)) = 1 := by
  sorry

/-- **Purifiable processes are causally separable** (Yokojima, Quintino, Soeda and Murao,
Corollary 1; Barrett, Lorenz and Oreshkov, Theorem 3; Theorem 6.1 of the paper). -/
theorem purifiable_causallySeparable (D : Ports) (W : PMat D) (hW : Valid D W)
    (hP : Purifiable D W) : CausallySeparable D W := by
  sorry

/-- **Causally ordered processes are purifiable** (Araújo, Feix, Navascués and Brukner, Section 3;
Proposition 9.2 of the paper). For all port dimensions, a process matrix in which Alice acts before
Bob, or Bob before Alice, is purifiable. Together with `purifiable_causallySeparable`, this places
the purifiable processes between the causally ordered ones and the causally separable ones; in
particular `Purifiable` contains signalling processes. -/
theorem ordered_processes_purifiable (D : Ports) (W : PMat D) (hW : Valid D W)
    (hord : OrderedAB D W ∨ OrderedBA D W) : Purifiable D W := by
  sorry

end CausalNonpurifiability.OQP43
