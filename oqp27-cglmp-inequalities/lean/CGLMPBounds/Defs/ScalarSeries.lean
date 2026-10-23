module

public import CGLMPBounds.Defs.ScalarCoefficients
public import CGLMPBounds.Defs.ScalarTail

@[expose] public section


namespace CGLMPBounds

noncomputable section

/-- The source term r_(i+1) E_(2i+1), with Lean's zero-based summation index. -/
def scalarSeriesTerm (i : ℕ) (θ y : ℝ) : ℝ :=
  scalarCosecantCoefficient (i + 1) * scalarE (2 * i + 1) θ y

/-- The scalar function E_theta defined by its series in Appendix J. -/
def scalarInfinite (θ y : ℝ) : ℝ := ∑' i : ℕ, scalarSeriesTerm i θ y

/-- The ten-term coefficient replacement used in (J.3)–(J.5). -/
def scalarTen (θ y : ℝ) : ℝ :=
  ∑ i : Fin 10, ((scalarCoefficientNumerator i : ℝ) / scalarCoefficientScale) *
    scalarE (2 * i.val + 1) θ y

/-- The triangular combination Omega_theta in (J.2), with x specified directly. -/
def scalarInfiniteTriangle (θ : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  (1 - 2 * θ) * ∑ j, (scalarInfinite θ (1 - x j) - scalarInfinite θ (x j))

end
end CGLMPBounds
