module

public import CGLMPBounds.Defs.Scenario

@[expose] public section


/-!
# The Bancal–Gisin–Pironio four-outcome inequality (G.1) (definitions)

Supplement, Appendix G: "Use each party's six independent marginals, for example
`pA = (pA(0|0), pA(1|0), pA(2|0), pA(0|1), pA(1|1), pA(2|1))`, and the 36 joint probabilities with
`a, b < 3`. The affine dimension is 48. The inequality is
`F(p) = ℓ · pA + ℓ · pB + Σ_{x,y=0}^{1} Σ_{a,b=0}^{2} H_{3x+a, 3y+b} p(a, b|x, y) ≤ 0`,   (G.1)
where `ℓ = (−1, −1, 0, −1, 0, 0)` and `H` is the `6 × 6` matrix displayed there."

Both parties have the four outcomes `Fin 4`. An outcome `a < 3` is `Fin.castSucc` of `a : Fin 3`,
and the pair (input `x`, outcome `a < 3`) has coordinate index `3x + a ∈ Fin 6` (`bgpIndex`).

`F` is defined on every table. It reads Alice's marginal in the context `(x, 0)`,
`pA(a|x) = Σ_b p(a,b|x,0)`, and Bob's marginal in the context `(0, y)`, `pB(b|y) = Σ_a p(a,b|0,y)`.
On no-signalling tables these are the one-party marginals. Every table at which the source
evaluates `F` is no-signalling: the deterministic strategies, the local polytope `C₄`, and the
points `p̄`, `p⁺`.

This file contains definitions only (no theorems); it belongs to the statement dependency closure.

* `bgpL`, `bgpH` : the coefficient data `ℓ` and `H` of (G.1);
* `bgpIndex x a` : the coordinate index `3x + a`;
* `bgpFunctional p` : `F(p)`.
-/

namespace CGLMPBounds

/-- The marginal coefficients `ℓ = (−1, −1, 0, −1, 0, 0)` of (G.1). Entry `3x + a` multiplies Alice's
marginal `pA(a|x)` in `ℓ · pA`, and Bob's marginal `pB(a|x)` in `ℓ · pB`. -/
def bgpL : Fin 6 → ℤ := ![-1, -1, 0, -1, 0, 0]

/-- The joint coefficients `H` of (G.1), row by row. Entry `(3x + a, 3y + b)` multiplies
`p(a, b|x, y)`. -/
def bgpH : Fin 6 → Fin 6 → ℤ :=
  ![![0, 1, 0, 1, 0, 1],
    ![1, 0, 0, 1, 1, 0],
    ![0, 0, -1, 1, 0, 0],
    ![1, 1, 1, 1, 0, 0],
    ![0, 1, 0, 0, 0, -1],
    ![1, 0, 0, 0, -1, 0]]

/-- The coordinate index `3x + a` of input `x ∈ {0, 1}` and outcome `a ∈ {0, 1, 2}`. -/
def bgpIndex (x : Fin 2) (a : Fin 3) : Fin 6 :=
  ⟨3 * x.val + a.val, by have := x.isLt; have := a.isLt; omega⟩

noncomputable section

/-- The functional `F(p) = ℓ · pA + ℓ · pB + Σ_{x,y} Σ_{a,b<3} H_{3x+a,3y+b} p(a,b|x,y)` of (G.1),
for four outcomes per party. Alice's marginal is read in the context `(x, 0)` and Bob's in the
context `(0, y)` (see the module docstring). -/
def bgpFunctional (p : Table (Fin 4) (Fin 4)) : ℝ :=
  (∑ x : Fin 2, ∑ a : Fin 3, (bgpL (bgpIndex x a) : ℝ) * ∑ b, p x 0 a.castSucc b)
    + (∑ y : Fin 2, ∑ b : Fin 3, (bgpL (bgpIndex y b) : ℝ) * ∑ a, p 0 y a b.castSucc)
    + ∑ x : Fin 2, ∑ y : Fin 2, ∑ a : Fin 3, ∑ b : Fin 3,
        (bgpH (bgpIndex x a) (bgpIndex y b) : ℝ) * p x y a.castSucc b.castSucc

end

end CGLMPBounds
