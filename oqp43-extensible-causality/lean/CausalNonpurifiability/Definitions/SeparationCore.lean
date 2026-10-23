module

public import CausalNonpurifiability.Definitions.HeisenbergCore
public import CausalNonpurifiability.Linear.Replacement

@[expose] public section


/-!
# `CausalNonpurifiability.Purification.Separation`

Steps 4–7 of the proof of Theorem 6.1 (manuscript Appendix A, `app:purcs`), in the two-part form
of `Purification/Sector.lean`.

Input: the Heisenberg-picture map `Φ† = heis U` of a unitary `U` (rows: future × inputs
`(A_I, B_I)`; columns: past × outputs `(A_O, B_O)`), the two statements of `eq:no-self`
(`Φ†(X ⊗ 1)` acts as the identity on `A_O`, `Φ†(1 ⊗ Y)` acts as the identity on `B_O`) and
`eq:LV-c` for `Φ†(Q)`, together with a family `Wf u v` of operators (the processes `W_τ` for
`τ = |u⟩⟨v|`) whose entries are matrix elements of `Φ†`.

* Step 4 — `Separation.sliceA`, `Separation.sliceB`: the operators `a X t' t`, `b Y o' o` on the
  global past with `Φ†(X ⊗ 1) = a X ⊗ 1_{A_O}` and `Φ†(1 ⊗ Y) = b Y ⊗ 1_{B_O}`
  (`heis_kronecker_one_apply`, `heis_one_kronecker_apply`). Multiplicativity of `Φ†` gives
  `Φ†(X ⊗ Y) = a X · b Y = b Y · a X` (`heis_kronecker_apply`, `heis_kronecker_apply'`,
  `sliceA_mul_sliceB_comm`).
* Steps 5–6 — `Separation.devA`, `Separation.devB`: the parts of `a X`, `b Y` that depend on the
  other party's output. `eq:LV-c` is the product relation `devA * devB = 0` (`devA_mul_devB`,
  `devB_mul_devA`).
* Step 7 — `Separation.exists_split` applies `exists_sector_split`: the vector of the global past
  is a sum `v₁ + v₂` of two orthogonal parts; `Wf v₁ v₁` does not depend on Bob's output
  (`R_BO_wf`), `Wf v₂ v₂` does not depend on Alice's output (`R_AO_wf`), and the cross terms
  vanish (`wf_eq_zero_of_cross`).

**Proof route** (the statement proved is the one needed for Theorem 6.1): the manuscript splits
the global past into sectors `L_k ⊗ R_k` with the structure theorem for finite-dimensional
`*`-algebras (`eq:algebra-split`); here the two parts of `Purification/Sector.lean` are used.

The auxiliary statements are generic in the finite index types; the endpoint
`causallySeparable_of_heis_structure` is their `Fin`-coordinate form.
-/

set_option autoImplicit false
-- Generic-index lemmas carry the uniform `[Fintype _] [DecidableEq _]` assumptions of the section.
set_option linter.unusedSectionVars false

open Matrix
open scoped ComplexOrder Kronecker

namespace CausalNonpurifiability

noncomputable section

namespace Separation

variable {F A B P O T : Type} [Fintype F] [Fintype A] [Fintype B] [Fintype P] [Fintype O]
  [Fintype T] [DecidableEq F] [DecidableEq A] [DecidableEq B] [DecidableEq P] [DecidableEq O]
  [DecidableEq T]

/-! ### Hypotheses and definitions -/

/-- `eq:no-self` for Alice: `Φ†(X ⊗ 1)` is diagonal and constant in the index of `A_O`. -/
def NoSelfA (U : Matrix (F × (A × B)) (P × (O × T)) ℂ) : Prop :=
  ∀ (X : Op A) (x' x : P) (o' o : O) (t' t : T),
    heis U (X ⊗ₖ (1 : Op B)) (x', (o', t')) (x, (o, t)) =
      if o = o' then invCard O *
        ∑ o'', heis U (X ⊗ₖ (1 : Op B)) (x', (o'', t')) (x, (o'', t)) else 0

/-- `eq:no-self` for Bob: `Φ†(1 ⊗ Y)` is diagonal and constant in the index of `B_O`. -/
def NoSelfB (U : Matrix (F × (A × B)) (P × (O × T)) ℂ) : Prop :=
  ∀ (Y : Op B) (x' x : P) (o' o : O) (t' t : T),
    heis U ((1 : Op A) ⊗ₖ Y) (x', (o', t')) (x, (o, t)) =
      if t = t' then invCard T *
        ∑ t'', heis U ((1 : Op A) ⊗ₖ Y) (x', (o', t'')) (x, (o, t'')) else 0

/-- `eq:LV-c` for `Φ†(Q)`, entrywise. -/
def LVc (U : Matrix (F × (A × B)) (P × (O × T)) ℂ) : Prop :=
  ∀ (Q : Op (A × B)) (x' x : P) (o' o : O) (t' t : T),
    heis U Q (x', (o', t')) (x, (o, t))
      - (if o = o' then invCard O * ∑ o'', heis U Q (x', (o'', t')) (x, (o'', t)) else 0)
      - (if t = t' then invCard T * ∑ t'', heis U Q (x', (o', t'')) (x, (o, t'')) else 0)
      + (if o = o' then invCard O * ∑ o'', (if t = t' then invCard T *
            ∑ t'', heis U Q (x', (o'', t'')) (x, (o'', t'')) else 0) else 0) = 0

/-- The entries of the family `Wf u v` are matrix elements of `Φ†(E₁ i' i ⊗ E₂ j' j)`. -/
def EntryForm (U : Matrix (F × (A × B)) (P × (O × T)) ℂ)
    (Wf : (P → ℂ) → (P → ℂ) → Op (LabIdx A O B T)) (E₁ : A → A → Op A) (E₂ : B → B → Op B) :
    Prop :=
  ∀ (u v : P → ℂ) (i i' : A) (o o' : O) (j j' : B) (t t' : T),
    Wf u v ((i, o), (j, t)) ((i', o'), (j', t')) =
      ∑ x, ∑ x', star (v x') *
        heis U (E₁ i' i ⊗ₖ E₂ j' j) (x', (o', t')) (x, (o, t)) * u x

/-- Alice's slice `a X t' t` of `Φ†(X ⊗ 1)` at the reference index `o₀` of `A_O`. -/
def sliceA (U : Matrix (F × (A × B)) (P × (O × T)) ℂ) (o₀ : O) (X : Op A) (t' t : T) : Op P :=
  fun x' x => heis U (X ⊗ₖ (1 : Op B)) (x', (o₀, t')) (x, (o₀, t))

/-- Bob's slice `b Y o' o` of `Φ†(1 ⊗ Y)` at the reference index `t₀` of `B_O`. -/
def sliceB (U : Matrix (F × (A × B)) (P × (O × T)) ℂ) (t₀ : T) (Y : Op B) (o' o : O) : Op P :=
  fun x' x => heis U ((1 : Op A) ⊗ₖ Y) (x', (o', t₀)) (x, (o, t₀))

/-- The mean of Alice's diagonal slices over the index of `B_O`. -/
def meanA (U : Matrix (F × (A × B)) (P × (O × T)) ℂ) (o₀ : O) (X : Op A) : Op P :=
  invCard T • ∑ t : T, sliceA U o₀ X t t

/-- The mean of Bob's diagonal slices over the index of `A_O`. -/
def meanB (U : Matrix (F × (A × B)) (P × (O × T)) ℂ) (t₀ : T) (Y : Op B) : Op P :=
  invCard O • ∑ o : O, sliceB U t₀ Y o o

/-- The part of Alice's slice that depends on Bob's output. -/
def devA (U : Matrix (F × (A × B)) (P × (O × T)) ℂ) (o₀ : O) (X : Op A) (t' t : T) : Op P :=
  sliceA U o₀ X t' t - (if t = t' then meanA U o₀ X else 0)

/-- The part of Bob's slice that depends on Alice's output. -/
def devB (U : Matrix (F × (A × B)) (P × (O × T)) ℂ) (t₀ : T) (Y : Op B) (o' o : O) : Op P :=
  sliceB U t₀ Y o' o - (if o = o' then meanB U t₀ Y else 0)

variable (U : Matrix (F × (A × B)) (P × (O × T)) ℂ)

end Separation

end

end CausalNonpurifiability
