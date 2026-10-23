module

public import Mathlib

@[expose] public section


/-!
# The two-input Bell scenario (definitions)

Definitions for bipartite Bell experiments with two inputs per party, following Appendix B
("Preliminaries and notation") of the manuscript. Inputs are `x y : Fin 2`; the outcome
alphabets are arbitrary finite types `α` (Alice) and `β` (Bob). The manuscript's scenario with
`d` outcomes per party is `α = β = ZMod d`.

This file contains definitions only (no theorems); it belongs to the statement dependency
closure.

* `Table α β`       : real tables `q x y a b`, read as `q(a,b|x,y)`;
* `IsBehaviour`     : nonnegative tables normalised in each context;
* `IsNoSignalling`  : the no-signalling polytope `P_d`;
* `Strategy`, `detTable` : deterministic assignments `(a₀,a₁,b₀,b₁)` and their tables `q_s`;
* `localSet`        : the Bell-local polytope `C_d`, the convex hull of the deterministic tables;
* `uniformTable`, `noisy` : uniform noise `u_d` and the mixture `v q + (1 - v) u_d`.
-/

namespace CGLMPBounds

noncomputable section

/-- A real table `q x y a b`, read as `q(a,b|x,y)`: `x` is Alice's input, `y` is Bob's input and
`a`, `b` are their outcomes. Neither positivity nor normalisation is built in. -/
abbrev Table (α β : Type*) := Fin 2 → Fin 2 → α → β → ℝ

/-- A behaviour: a nonnegative table that is normalised in each context `(x, y)`. -/
structure IsBehaviour {α β : Type*} [Fintype α] [Fintype β] (q : Table α β) : Prop where
  /-- All entries are nonnegative. -/
  nonneg : ∀ x y a b, 0 ≤ q x y a b
  /-- Each context is normalised. -/
  sum_eq_one : ∀ x y, ∑ a, ∑ b, q x y a b = 1

/-- The no-signalling polytope `P_d`: behaviours whose one-party marginals are independent of the
other party's input. -/
structure IsNoSignalling {α β : Type*} [Fintype α] [Fintype β] (q : Table α β) : Prop where
  /-- The table is a behaviour. -/
  isBehaviour : IsBehaviour q
  /-- Alice's marginal does not depend on Bob's input. -/
  margA_indep : ∀ x y y' a, ∑ b, q x y a b = ∑ b, q x y' a b
  /-- Bob's marginal does not depend on Alice's input. -/
  margB_indep : ∀ x x' y b, ∑ a, q x y a b = ∑ a, q x' y a b

/-- A deterministic assignment `(a₀, a₁, b₀, b₁)`: `s.1 x` is Alice's outcome on input `x` and
`s.2 y` is Bob's outcome on input `y`. -/
abbrev Strategy (α β : Type*) := (Fin 2 → α) × (Fin 2 → β)

/-- The deterministic table `q_s(a,b|x,y) = 1{a = a_x, b = b_y}`. -/
def detTable {α β : Type*} [DecidableEq α] [DecidableEq β] (s : Strategy α β) : Table α β :=
  fun x y a b => if a = s.1 x ∧ b = s.2 y then 1 else 0

/-- The Bell-local set (the local polytope `C_d`): the convex hull of the deterministic tables. -/
def localSet (α β : Type*) [DecidableEq α] [DecidableEq β] : Set (Table α β) :=
  convexHull ℝ (Set.range (detTable (α := α) (β := β)))

/-- The uniform table `u(a,b|x,y) = 1 / (|α| |β|)`. For `α = β = ZMod d` this is `u_d = d⁻²`. -/
def uniformTable (α β : Type*) [Fintype α] [Fintype β] : Table α β :=
  fun _ _ _ _ => 1 / ((Fintype.card α : ℝ) * (Fintype.card β : ℝ))

/-- The uniform-noise mixture `v q + (1 - v) u` at visibility `v`. -/
def noisy {α β : Type*} [Fintype α] [Fintype β] (v : ℝ) (q : Table α β) : Table α β :=
  v • q + (1 - v) • uniformTable α β

end

end CGLMPBounds
