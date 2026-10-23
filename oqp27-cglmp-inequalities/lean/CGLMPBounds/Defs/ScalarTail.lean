module

public import Mathlib

@[expose] public section


/-!
# The analytic scalar terms and geometric budget of Appendix J

Canonical supplement pp. 37–38. The finite products `Q_{k,θ}` have the source's
empty-product convention. The removable value of `E_{k,θ}` at θ=0 is explicitly
zero; evaluating the unsimplified rational formula with totalized division at
zero would give the wrong value. The identification with its continuous limit
is a separate algebraic/analytic proof obligation.

The geometric majorant and budget below are the explicit quantities in (J.3).
They do not encode or assume the source's cosecant coefficients `r_n`, their
eta-function identity, or their ten rational enclosure intervals.
-/

namespace CGLMPBounds

noncomputable section

/-- The j-th factor `(y+jθ)/(1+(j+1)θ)`; the source uses j≥1. -/
def scalarRatio (j : ℕ) (θ y : ℝ) : ℝ :=
  (y + (j : ℝ) * θ) / (1 + ((j : ℝ) + 1) * θ)

/-- `Q_{k,θ}(y)=∏_{j=1}^k (y+jθ)/(1+(j+1)θ)`, with `Q_0=1`. -/
def scalarQ (k : ℕ) (θ y : ℝ) : ℝ :=
  ∏ i ∈ Finset.range k, scalarRatio (i + 1) θ y

/-- The source scalar error term, with its removable value zero at θ=0. -/
def scalarE (k : ℕ) (θ y : ℝ) : ℝ :=
  if θ = 0 then 0 else
    ((1 + θ) * y ^ k - scalarQ k θ y) / θ
      - (((k : ℝ) + 1) * ((k : ℝ) + 2) / 2) * scalarQ k θ y
      + ((k : ℝ) * ((k : ℝ) + 1) / 2) * scalarQ (k - 1) θ y

/-- The n-th geometric error majorant `(4/3)*4^(-n)*(1+4n²)` in (J.3).
It is only a numerical majorant, not a definition of a source coefficient. -/
def scalarGeometricMajorant (n : ℕ) : ℝ :=
  (4 / 3 : ℝ) * (1 / 4 : ℝ) ^ n * (1 + 4 * (n : ℝ) ^ 2)

/-- The explicit error budget in (J.3): ten coefficient-rounding contributions
and the geometric majorant from n=11 onwards. -/
def scalarTruncationErrorBudget : ℝ :=
  (1550 : ℝ) / 10 ^ 12 + ∑' m : ℕ, scalarGeometricMajorant (m + 11)

end

end CGLMPBounds
