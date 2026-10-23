module

public import CGLMPBounds.Defs.Quantum

@[expose] public section


/-!
# Behaviours of two rank-one projective measurements per party on `Φ_d` (definitions)

Theorem A.4 takes the supremum of the statistical strength "over `d ≥ 2` and two rank-one PVMs per
party on `Φ_d`". A rank-one PVM on `ℂ^d` has exactly `d` nonzero elements, so its outcomes are indexed
by `Fin d`.

* `IsRankOnePVM P` : `P` is a PVM whose elements have trace one (for an orthogonal projection the trace
  equals the rank, so these are the rank-one PVMs);
* `rankOnePVMBehaviours d` : the behaviours `q(a,b|x,y) = d⁻¹ Re Tr(A x a * B y b)` of `tracialTable`
  with `A x`, `B y` rank-one PVMs on `ℂ^d`. As in `tracialTable`, `A x` is Alice's measurement in the
  transposed (tracial) form; transposition maps rank-one PVMs to rank-one PVMs, so this is the set of
  all behaviours of two rank-one PVMs per party on `Φ_d`.

This file contains definitions only (no theorems); it belongs to the statement dependency closure.
-/

namespace CGLMPBounds

noncomputable section

/-- A rank-one projective measurement on `ℂ^d` with outcomes `Fin d`: a PVM whose elements have trace
one (equivalently rank one, since they are orthogonal projections). -/
def IsRankOnePVM {d : ℕ} (P : Fin d → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  IsPVM P ∧ ∀ a, Matrix.trace (P a) = 1

/-- The behaviours of two rank-one PVMs per party on the maximally entangled state `Φ_d`. -/
def rankOnePVMBehaviours (d : ℕ) : Set (Table (Fin d) (Fin d)) :=
  {q | ∃ A B : Fin 2 → Fin d → Matrix (Fin d) (Fin d) ℂ,
    (∀ x, IsRankOnePVM (A x)) ∧ (∀ y, IsRankOnePVM (B y)) ∧ q = tracialTable A B}

end

end CGLMPBounds
