module

public import CausalNonpurifiability.Linear.Indices
public import CausalNonpurifiability.Linear.PartialTrace
public import CausalNonpurifiability.Definitions.ProcessCore
public import CausalNonpurifiability.Definitions.Causality

@[expose] public section


/-! Exact original statement vocabulary, separated from the surrounding correctness proofs. No declaration body or mathematical premise is changed. -/

set_option autoImplicit false

open scoped ComplexOrder Kronecker MatrixOrder

namespace CausalNonpurifiability

open Matrix

/-- An instrument in Choi coordinates (`eq:choi`, `M_{a|x} = J(𝓐_{a|x})ᵀ`): positive matrices on
`I ⊗ O` (input ⊗ output) with `Tr_O ∑_a M_{a|x} = I_I` (§2.1).  With this convention the Born
rule is `Tr[W (M ⊗ N)]` (`eq:born`) with no further transpose. -/
structure Instrument (I O X A : Type) [Fintype I] [Fintype O] [Fintype A] [DecidableEq I] where
  /-- The element `M_{a|x}` for setting `x` and outcome `a`. -/
  elem : X → A → Op (I × O)
  /-- Positivity of every element. -/
  positive : ∀ x a, (elem x a).PosSemidef
  /-- Normalization `Tr_O ∑_a M_{a|x} = I_I`. -/
  normalized : ∀ x, ptraceOut (∑ a, elem x a) = 1

/-- A density operator: positive with unit trace (the shared ancilla state `σ` of §2.2). -/
def Density {I : Type} [Fintype I] (σ : Op I) : Prop :=
  σ.PosSemidef ∧ σ.trace = 1

section ExtendInput

variable (D : Ports) {RA RB : Type}

/-- The ancilla-extended process `W ⊗ σ` in the enlarged-input party-grouped order
`((A_I × R_A) × A_O) × ((B_I × R_B) × B_O)`, with the literal entry formula
`extendInput D W σ (((ai,ra),ao),((bi,rb),bo)) (((ai',ra'),ao'),((bi',rb'),bo'))
  = W ((ai,ao),(bi,bo)) ((ai',ao'),(bi',bo')) * σ (ra,rb) (ra',rb')`
(`extendInput_apply`).  Definitionally `extended W σ`, so `GenLV.extended` and the
`R_*_extended` lemmas apply verbatim. -/
def extendInput (W : PMat D) (σ : Op (RA × RB)) :
    Op (LabIdx (Fin D.m × RA) (Fin D.d) (Fin D.n × RB) (Fin D.e)) :=
  extended W σ

end ExtendInput

section Born

variable (D : Ports) {RA RB X Y A B : Type} [Fintype RA] [DecidableEq RA] [Fintype RB]
  [DecidableEq RB] [Fintype A] [Fintype B]

/-- The extended Born rule (`eq:born` with shared ancilla, §2.2):
`p(a,b|x,y) = Re Tr[(W ⊗ σ)(M_{a|x} ⊗ N_{b|y})]`, where `M_{a|x} ⊗ₖ N_{b|y}` lives on
`((A_I × R_A) × A_O) × ((B_I × R_B) × B_O)`, the index type of `extendInput`.
The imaginary part vanishes (`bornExtended_im_zero`), so taking `re` loses nothing. -/
noncomputable def bornExtended (W : PMat D) (σ : Op (RA × RB))
    (M : Instrument (Fin D.m × RA) (Fin D.d) X A) (N : Instrument (Fin D.n × RB) (Fin D.e) Y B) :
    Prob X Y A B :=
  fun x y a b => ((extendInput D W σ * (M.elem x a ⊗ₖ N.elem y b)).trace).re

end Born

/-- **Extensible causality** (§2.2, the complete quantifier): `W` is valid and, for every finite
shared ancilla `R_A ⊗ R_B` (dimensions `r+1`, `s+1`, unbounded), every density operator `σ` on
it, and every pair of extended instruments (finite settings and outcomes, all sizes unbounded),
the *whole* extended Born distribution — one `σ`, `M`, `N` for all settings and outcomes — is
causal (`Causal`, `eq:causal-definition`).  No dimension bound and no restriction on `σ`
(entangled, singular) is imposed. -/
def ExtensiblyCausal (D : Ports) (W : PMat D) : Prop :=
  Valid D W ∧
    ∀ (r s nx ny na nb : ℕ) (σ : Op (Fin (r + 1) × Fin (s + 1))), Density σ →
      ∀ (M : Instrument (Fin D.m × Fin (r + 1)) (Fin D.d) (Fin (nx + 1)) (Fin (na + 1)))
        (N : Instrument (Fin D.n × Fin (s + 1)) (Fin D.e) (Fin (ny + 1)) (Fin (nb + 1))),
        Causal (bornExtended D W σ M N)

end CausalNonpurifiability
