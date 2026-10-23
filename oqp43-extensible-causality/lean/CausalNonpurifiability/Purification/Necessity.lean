module

public import CausalNonpurifiability.Purification.Family
public import CausalNonpurifiability.Purification.Separation
public import CausalNonpurifiability.Definitions.Hypotheses

@[expose] public section


/-!
# `CausalNonpurifiability.Purification.Necessity`

**Theorem 6.1** of the manuscript (`thm:purcs`; [YQSM, Corollary 1], [BLO, Theorem 3]): every
purifiable process is causally separable, for arbitrary local dimensions and purifying spaces `P`,
`F` of arbitrary finite dimension. This closes the hypothesis `PurificationNecessity` of the
earlier development: `purification_necessity` is a theorem, not an axiom and not a parameter.

Assembly of the proof of Appendix A (`app:purcs`):

* Step 1 — `Pure.exists_unitary` (`Purification/Unitary.lean`): `S = |𝒰⟩⟩⟨⟨𝒰|`.
* Step 2 — `procV`, `procV_lvEquations` (`Purification/Family.lean`): the operators `W_τ` satisfy
  `eq:LV`; this uses the converse of Lemma 2.3 (`Definitions/Channels.lean`) and the first clause
  of `Pure` (`Deterministic`), with trivial additional systems.
* Step 3 — `heis_no_self_A`, `heis_no_self_B`, `heis_lv_c` (`Purification/Family.lean`).
* Steps 4–7 — `causallySeparable_of_heis_structure` (`Purification/Separation.lean`), which rests
  on `exists_sector_split` (`Purification/Sector.lean`).

**Proof route.** Steps 4–6 of Appendix A quote the structure theorem for finite-dimensional
`*`-algebras (`eq:algebra-split`) and split the global past into sectors `L_k ⊗ R_k`. The formal
proof of the same statement splits the vector `|0⟩` of the global past into two orthogonal parts.
-/

set_option autoImplicit false

open Matrix
open scoped ComplexOrder Kronecker

namespace CausalNonpurifiability

/-- **Theorem 6.1** (`thm:purcs`): a purifiable process is causally separable. -/
theorem purifiable_causallySeparable (D : Ports) (W : PMat D) (hW : Valid D W)
    (hP : Purifiable D W) : CausallySeparable D W := by
  obtain ⟨p, f, S, hPure, hSW⟩ := hP
  obtain ⟨U, _, hU2, hS⟩ := hPure.exists_unitary
  have hdet : Deterministic D S := hPure.1
  have hred : W = procV U (Pi.single 0 1) (Pi.single 0 1) := by
    rw [← hSW]
    exact reducePastFuture_eq_procV U hS
  rw [hred]
  refine causallySeparable_of_heis_structure U hU2 (procV U) unitMat unitMat
    (heis_no_self_A U hS hdet) (heis_no_self_B U hS hdet) (heis_lv_c U hS hdet)
    (procV_entry U) (fun v => procV_lvEquations U hS hdet v v) (procV_posSemidef U)
    (procV_add_add U) (Pi.single 0 1) ?_
  rw [← hred]
  exact hW

/-- The hypothesis `PurificationNecessity` of the conditional endpoints holds. -/
theorem purification_necessity : PurificationNecessity :=
  purifiable_causallySeparable

end CausalNonpurifiability
