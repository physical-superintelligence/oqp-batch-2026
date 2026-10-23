module

public import Mathlib

@[expose] public section


/-!
# Literal upper-cluster and exterior-contour definitions for C.3

These are the actual root sum, trace-resolvent circle integral, exterior
pencil, fixed negative-cluster circle, and Taylor derivatives used in (C.8).
No analyticity, separation, moment identity, or convergence law is assumed.
The definitions are moved verbatim from their original proof modules.
-/

namespace CGLMPBounds.Hardy
noncomputable section

section Cluster
open Complex Metric Set
open scoped Real
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

/-- The source normalized upper-cluster trace, defined through the full
characteristic-root multiset. -/
def upperClusterTrace (A : Matrix ι ι ℂ) : ℂ :=
  (A.charpoly.roots.map (fun a => if 0 < a.im then a else 0)).sum /
    (Fintype.card ι : ℂ)

/-- Actual normalized trace-resolvent circle integral. -/
def circleClusterTrace (A : Matrix ι ι ℂ) (c : ℂ) (R : ℝ) : ℂ :=
  (∮ ζ in C(c, R), Matrix.trace (A * resolvent A ζ)) /
    (2 * Real.pi * Complex.I : ℂ) / (Fintype.card ι : ℂ)

end Cluster

section Exterior
open Complex Metric Set Filter
open scoped Topology Interval Matrix.Norms.Operator

/-- A finite explicit left-circle radius. Multiplicity is immaterial to the
radius, but will be retained in the trace integral and its root sum. -/
def negativeClusterRadius (s : Multiset ℂ) : ℝ :=
  1 + ∑ a ∈ s.toFinset, ‖a‖ ^ 2 / (2 * |a.re|)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

/-- The actual exterior pencil printed before (C.8). -/
def exteriorPencil (H Y : Matrix ι ι ℂ) (w : ℂ) : Matrix ι ι ℂ :=
  H⁻¹ * (1 - w • Y)

/-- `q(w)` is an actual positively oriented normalized contour integral.
Its definition does not use a desired Taylor coefficient or moment identity. -/
def exteriorClusterQ (H Y : Matrix ι ι ℂ) (w : ℂ) : ℂ :=
  let R := negativeClusterRadius H⁻¹.charpoly.roots
  circleClusterTrace (exteriorPencil H Y w) (-(R : ℂ)) R

end Exterior

section Taylor
open Complex Filter Metric Set
open scoped Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

/-- The actual Taylor coefficient q_m, independent of any later moment claim. -/
def exteriorTaylorCoefficient (H Y : Matrix ι ι ℂ) (m : ℕ) : ℂ :=
  iteratedDeriv m (exteriorClusterQ H Y) 0 / (m.factorial : ℂ)

end Taylor

end
end CGLMPBounds.Hardy
