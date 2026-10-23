module

public import CGLMPBounds.Defs.Scenario

@[expose] public section


/-!
# Statistical strength, local fraction and the four-variable minimum (definitions)

Definitions for (B.5), (B.6) and the local fraction of Appendix B of the supplement ("Preliminaries
and notation"), used by Theorem F.2 and Theorem A.4. Quantities in bits take values in `ℝ≥0∞`,
which realises the source's "usual extended-value conventions at zero probabilities".

* `relEntropy p r`  : `D(p‖r) = Σ_z p_z log₂(p_z / r_z)`, with `0 · log₂(0 / r) = 0` and
  `D(p‖r) = ∞` as soon as some `p_z ≠ 0` has `r_z = 0`;
* `statStrength μ q` : the statistical strength (B.5),
  `S_μ(q) = min_{ℓ ∈ C_d} Σ_{x,y} μ_{xy} D(q_{xy} ‖ ℓ_{xy})`, written as an infimum;
* `localFraction q`  : `LF(q) = max {α : q ≥ α L entrywise for a normalized L ∈ C_d}`, written as a
  supremum;
* `negLogTwo`, `xiMin μ` : the four-variable minimum (B.6),
  `Ξ(μ) = min {-Σ_e μ_e log₂ s_e : 0 ≤ s_e ≤ 1, Σ_e s_e = 3}`, written as an infimum, with
  `-log₂ 0 = ∞` and `0 · ∞ = 0`.

This file contains definitions only (no theorems); it belongs to the statement dependency closure.
-/

namespace CGLMPBounds

noncomputable section

open scoped ENNReal

/-- Relative entropy in bits of two finite real vectors, `D(p‖r) = Σ_z p_z log₂(p_z / r_z)`, with
the usual extended-value conventions: terms with `p_z = 0` contribute `0`, and `D(p‖r) = ∞` as soon
as some `p_z ≠ 0` has `r_z = 0`. For probability vectors the finite sum is nonnegative (Gibbs'
inequality, proved as `relEntropy_sum_nonneg`), so `ENNReal.ofReal` does not truncate it there. -/
def relEntropy {ι : Type*} [Fintype ι] (p r : ι → ℝ) : ℝ≥0∞ :=
  if ∀ z, r z = 0 → p z = 0 then ENNReal.ofReal (∑ z, p z * Real.logb 2 (p z / r z)) else ∞

/-- Statistical strength (B.5) in bits per complete trial,
`S_μ(q) = min_{ℓ ∈ C_d} Σ_{x,y} μ_{xy} D(q_{xy} ‖ ℓ_{xy})`, for a weight `μ x y` on the four input
pairs (an input law: nonnegative with total weight one) and a table `q`. Here `q_{xy}` and `ℓ_{xy}`
are the outcome distributions `(a, b) ↦ q(a,b|x,y)` and `(a, b) ↦ ℓ(a,b|x,y)` of the context
`(x, y)`. The minimum over the local set `C_d` is written as an infimum. -/
def statStrength {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (μ : Fin 2 → Fin 2 → ℝ) (q : Table α β) : ℝ≥0∞ :=
  ⨅ ℓ ∈ localSet α β, ∑ x, ∑ y, ENNReal.ofReal (μ x y) *
    relEntropy (fun z : α × β => q x y z.1 z.2) (fun z : α × β => ℓ x y z.1 z.2)

/-- The local fraction `LF(q) = max {α : q ≥ α L entrywise for a normalized L ∈ C_d}`, written as a
supremum over `α ≥ 0` (every element of `C_d` is normalized). -/
def localFraction {α β : Type*} [DecidableEq α] [DecidableEq β] (q : Table α β) : ℝ :=
  sSup {t : ℝ | 0 ≤ t ∧ ∃ L ∈ localSet α β, ∀ x y a b, t * L x y a b ≤ q x y a b}

/-- `-log₂ s`, with the value `∞` at `s = 0`. -/
def negLogTwo (s : ℝ) : ℝ≥0∞ :=
  if s = 0 then ∞ else ENNReal.ofReal (-Real.logb 2 s)

/-- The four-variable minimum (B.6),
`Ξ(μ) = min {-Σ_e μ_e log₂ s_e : 0 ≤ s_e ≤ 1, Σ_e s_e = 3}` over the four input pairs
`e = (x, y) ∈ {00, 01, 10, 11}`, with `-log₂ 0 = ∞` and `0 · ∞ = 0`; written as an infimum. -/
def xiMin (μ : Fin 2 → Fin 2 → ℝ) : ℝ≥0∞ :=
  ⨅ s ∈ {s : Fin 2 → Fin 2 → ℝ | (∀ x y, 0 ≤ s x y ∧ s x y ≤ 1) ∧ ∑ x, ∑ y, s x y = 3},
    ∑ x, ∑ y, ENNReal.ofReal (μ x y) * negLogTwo (s x y)

end

end CGLMPBounds
