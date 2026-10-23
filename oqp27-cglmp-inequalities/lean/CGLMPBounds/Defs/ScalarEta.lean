module

public import CGLMPBounds.Defs.ScalarCoefficients

@[expose] public section


namespace CGLMPBounds

/-- The alternating Dirichlet series η(2n) in Appendix J, indexed from j=1. -/
noncomputable def scalarEta (n : ℕ) : ℝ :=
  ∑' j : ℕ, (-1 : ℝ) ^ j * (1 / ((j : ℝ) + 1) ^ (2 * n))

end CGLMPBounds
