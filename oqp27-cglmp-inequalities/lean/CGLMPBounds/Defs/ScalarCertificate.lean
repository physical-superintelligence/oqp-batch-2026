module

public import Mathlib

@[expose] public section


/-!
# The finite polynomial certificate of Appendix J

These definitions transcribe the canonical supplement, pp. 38–39, Table J.1 and
(J.4)–(J.5). They do not assume any positivity certificate. At `θ = 0`, the division
by `θ` in `scalarNumerator` is totalized to zero; the source numerator `B_k` is
divisible by `θ²`, so this is its intended removable value. Establishing that
divisibility and the coefficient reconstruction is a proof obligation.

The ten-term rational function is only the finite approximation to `E_θ` in the
source. The infinite-series tail and its uniform bound (J.3) are separate claims.
-/

namespace CGLMPBounds

/-- The ten integers `m_n` of Table J.1, with Lean index `i = n-1`. -/
def scalarCoefficientNumerator : Fin 10 → ℤ :=
  ![261799387799, 75362478042, 19606915981, 4954856459, 1242203718,
    310774174, 77707647, 19427797, 4857004, 1214254]

/-- The fixed scale `Q = 10¹²`. -/
def scalarCoefficientScale : ℕ := 10 ^ 12

noncomputable section

/-- `D_*(θ) = ∏_{j=2}^{20} (1+jθ)`. -/
def scalarDstar (θ : ℝ) : ℝ :=
  ∏ j ∈ Finset.range 19, (1 + ((j + 2 : ℕ) : ℝ) * θ)

/-- `D_k(θ) = ∏_{j=2}^{k+1} (1+jθ)`. -/
def scalarD (k : ℕ) (θ : ℝ) : ℝ :=
  ∏ j ∈ Finset.range k, (1 + ((j + 2 : ℕ) : ℝ) * θ)

/-- `P_k(θ,y) = ∏_{j=1}^k (y+jθ)`. -/
def scalarP (k : ℕ) (θ y : ℝ) : ℝ :=
  ∏ j ∈ Finset.range k, (y + ((j + 1 : ℕ) : ℝ) * θ)

/-- `B_k` as displayed on p. 38, with real arithmetic for the two half-integer formulas. -/
def scalarB (k : ℕ) (θ y : ℝ) : ℝ :=
  (1 + θ) * y ^ k * scalarD k θ
    - (1 + (((k : ℝ) + 1) * ((k : ℝ) + 2) / 2) * θ) * scalarP k θ y
    + ((k : ℝ) * ((k : ℝ) + 1) / 2) * θ * scalarP (k - 1) θ y
        * (1 + ((k : ℝ) + 1) * θ)

/-- The polynomial factor `D_*/D_k = ∏_{j=k+2}^{20}(1+jθ)` for `k ≤ 19`. -/
def scalarDquotient (k : ℕ) (θ : ℝ) : ℝ :=
  ∏ j ∈ Finset.range (19 - k), (1 + ((k + 2 + j : ℕ) : ℝ) * θ)

/-- The integer polynomial `N(θ,y)` of Appendix J, expressed through the source's
factored formula. Totalized division fills its removable value at zero. -/
def scalarNumerator (θ y : ℝ) : ℝ :=
  ∑ i : Fin 10, (scalarCoefficientNumerator i : ℝ)
    * scalarDquotient (2 * i.val + 1) θ * (scalarB (2 * i.val + 1) θ y / θ)

/-- Domain parametrization `Y = θ+(1−2θ)u`. -/
def scalarY (θ u : ℝ) : ℝ := θ + (1 - 2 * θ) * u

/-- Domain parametrization `X_j = θ+(1−3θ)α_j`. -/
def scalarX (θ : ℝ) (α : Fin 3 → ℝ) (j : Fin 3) : ℝ :=
  θ + (1 - 3 * θ) * α j

/-- `N_△ = (1−2θ) ∑_j [N(θ,1−X_j)−N(θ,X_j)]`. -/
def scalarTriangleNumerator (θ : ℝ) (α : Fin 3 → ℝ) : ℝ :=
  (1 - 2 * θ) * ∑ j, (scalarNumerator θ (1 - scalarX θ α j)
    - scalarNumerator θ (scalarX θ α j))

end

end CGLMPBounds
