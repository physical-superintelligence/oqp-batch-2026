module

public import CausalNonpurifiability.Full
public import CausalNonpurifiability.Boundary.Dilation

@[expose] public section


/-!
# `CausalNonpurifiability.Dichotomy`

The dimension dichotomy `eq:dichotomy` of `thm:main`:

  `[every extensibly causal process on (m,d,n,e) is purifiable] ↔ min{m,d,n,e} = 1`.

* `dichotomy_backward` — "⇐": with a one-dimensional port every valid process is causally ordered
  and has a finite purification (`thm:main` (iii), `one_dimensional_purifiable`,
  `Boundary/Dilation`); extensible causality supplies validity.
* `min_eq_one_iff`, `allPortsGE2_iff` — the arithmetic bridge between `min … = 1` and the
  port-wise hypotheses (`Ports.positive`: every port dimension is `≥ 1`).
* `dimension_dichotomy_of_purCS` — "⇒" by contrapositive from
  `dichotomy_forward_of_purCS` (`Full`), conditional on `PurificationNecessity` (`eq:purcs`).

The hypothesis is discharged by Theorem 6.1, `purification_necessity`
(`Purification/Necessity.lean`); the unconditional statement is `dimension_dichotomy`
(`Unconditional.lean`). No axiom is involved.
-/

set_option autoImplicit false

namespace CausalNonpurifiability

open Matrix

section Backward
variable (D : Ports)

/-- **`eq:dichotomy`, "⇐"** (`thm:main` (iii)): if some port is one-dimensional, every extensibly
causal process is purifiable. -/
theorem dichotomy_backward (h1 : D.m = 1 ∨ D.d = 1 ∨ D.n = 1 ∨ D.e = 1) :
    ∀ W : PMat D, ExtensiblyCausal D W → Purifiable D W :=
  fun _ hW => one_dimensional_purifiable h1 hW.1

/-- `min{m,d,n,e} = 1` iff some port is one-dimensional (all ports are `≥ 1`). -/
theorem min_eq_one_iff :
    min D.m (min D.d (min D.n D.e)) = 1 ↔ (D.m = 1 ∨ D.d = 1 ∨ D.n = 1 ∨ D.e = 1) := by
  obtain ⟨hm, hd, hn, he⟩ := D.positive
  rw [Nat.min_def, Nat.min_def, Nat.min_def]
  split_ifs <;> constructor <;> intro h <;> omega

/-- `AllPortsGE2 D` iff `min{m,d,n,e} ≠ 1` (all ports are `≥ 1`). -/
theorem allPortsGE2_iff : AllPortsGE2 D ↔ min D.m (min D.d (min D.n D.e)) ≠ 1 := by
  obtain ⟨hm, hd, hn, he⟩ := D.positive
  rw [Ne, min_eq_one_iff]
  unfold AllPortsGE2
  constructor <;> intro h <;> omega

end Backward

/-- **The dimension dichotomy** (`thm:main`, `eq:dichotomy`), conditional on the
published purification-necessity theorem (`eq:purcs`, passed as a parameter): on the port tuple
`(m, d, n, e)`, every extensibly causal process is purifiable iff `min{m,d,n,e} = 1`. -/
theorem dimension_dichotomy_of_purCS (hPurCS : PurificationNecessity) (D : Ports) :
    (∀ W : PMat D, ExtensiblyCausal D W → Purifiable D W) ↔
      min D.m (min D.d (min D.n D.e)) = 1 := by
  constructor
  · intro hall
    by_contra hne
    have hD : AllPortsGE2 D := (allPortsGE2_iff D).mpr hne
    obtain ⟨W, hEC, hnp⟩ := dichotomy_forward_of_purCS D hPurCS hD
    exact hnp (hall W hEC)
  · intro h1
    exact dichotomy_backward D ((min_eq_one_iff D).mp h1)

end CausalNonpurifiability
