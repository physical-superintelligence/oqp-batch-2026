module

public import CausalNonpurifiability.Linear.Replacement

@[expose] public section


/-! Process vocabulary with exact original definitions. Coordinate identities and process lemmas remain in Definitions.Process, outside this definition owner. -/

set_option autoImplicit false

open scoped Kronecker ComplexOrder

namespace CausalNonpurifiability

noncomputable section

section GenLV

variable {AI AO BI BO : Type} [Fintype AI] [Fintype AO] [Fintype BI] [Fintype BO]
  [DecidableEq AI] [DecidableEq AO] [DecidableEq BI] [DecidableEq BO]

/-- `W ∈ L_V` on generic laboratory indices (`eq:LV`): Hermitian and
`(1-R_{A_O}) R_{B_I B_O} W = 0` (`eq:LV-a`),
`(1-R_{B_O}) R_{A_I A_O} W = 0` (`eq:LV-b`),
`(1-R_{A_O})(1-R_{B_O}) W = 0` (`eq:LV-c`). -/
def GenLV (W : Op (LabIdx AI AO BI BO)) : Prop :=
  W.IsHermitian ∧
  R_BIBO W - R_AO (R_BIBO W) = 0 ∧
  R_AIAO W - R_BO (R_AIAO W) = 0 ∧
  W - R_AO W - R_BO W + R_AO (R_BO W) = 0

end GenLV

variable (D : Ports)

/-- `W ∈ L_V` (`eq:LV`) for a process matrix on the ports `D`: the `Fin`-coordinate
instance of `GenLV`. -/
def InLV (W : PMat D) : Prop := GenLV W

/-- Normalized valid process matrix (`eq:valid`): `W ∈ L_V`, `W ≥ 0`, `Tr W = d·e`. -/
def Valid (W : PMat D) : Prop :=
  InLV D W ∧ W.PosSemidef ∧ Matrix.trace W = ((D.d * D.e : ℕ) : ℂ)

/-- The ordered cone `O_{A≺B}` (`eq:ordered-cones`): `T ∈ L_V`, `T ≥ 0`, `R_{B_O} T = T`.
Subnormalized: no trace condition. -/
def OrderedAB (T : PMat D) : Prop :=
  InLV D T ∧ T.PosSemidef ∧ R_BO T = T

/-- The ordered cone `O_{B≺A}` (`eq:ordered-cones`): `T ∈ L_V`, `T ≥ 0`, `R_{A_O} T = T`.
Subnormalized: no trace condition. -/
def OrderedBA (T : PMat D) : Prop :=
  InLV D T ∧ T.PosSemidef ∧ R_AO T = T

/-- Causal separability (§2.1): a normalized process in `O_{A≺B} + O_{B≺A}`. -/
def CausallySeparable (W : PMat D) : Prop :=
  Valid D W ∧ ∃ U V : PMat D, OrderedAB D U ∧ OrderedBA D V ∧ W = U + V

/-- The input embedding `Q_C = C^{A_I B_I} ⊗ I^{A_O B_O}` (`eq:QC`) by its entries (Appendix C): `(Q_C)_{(a,o,b,t),(a',o',b',t')} = C_{(a,b),(a',b')} δ_{oo'} δ_{tt'}`. -/
def QC (C : Op (Fin D.m × Fin D.n)) : PMat D :=
  fun x y => C (x.1.1, x.2.1) (y.1.1, y.2.1) * (if x.1.2 = y.1.2 ∧ x.2.2 = y.2.2 then 1 else 0)

/-- The first-party ordered marginal (`eq:ordered-marginal`):
`ω_A(T) = Tr_{A_O B_I B_O} T / (d·e)`. -/
def omegaA (T : PMat D) : Op (Fin D.m) :=
  (((D.d * D.e : ℕ) : ℂ))⁻¹ • ptraceOut (Matrix.reindex (eqAI _ _ _ _) (eqAI _ _ _ _) T)

/-- The second-party ordered marginal (`eq:ordered-marginal`, "analogously"):
`ω_B(T) = Tr_{A_I A_O B_O} T / (d·e)`. -/
def omegaB (T : PMat D) : Op (Fin D.n) :=
  (((D.d * D.e : ℕ) : ℂ))⁻¹ • ptraceOut (Matrix.reindex (eqBI _ _ _ _) (eqBI _ _ _ _) T)

/-- The `B_O`-stripped operator `T̂ = Tr_{B_O} T / e` on `A_I A_O B_I` (`eq:ordered-marginal`,
`T = T̂ ⊗ I_{B_O}` for `T ∈ O_{A≺B}`). -/
def hatAB (T : PMat D) : Op ((Fin D.m × Fin D.d) × Fin D.n) :=
  ((D.e : ℂ))⁻¹ • ptraceOut (Matrix.reindex (eqBO _ _ _ _) (eqBO _ _ _ _) T)

end
end CausalNonpurifiability
