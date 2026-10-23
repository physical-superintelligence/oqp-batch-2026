module

public import CGLMPBounds.Defs.ScalarCertificate
public import Mathlib.NumberTheory.Bernoulli

@[expose] public section


/-!
The exact coefficients printed in (I.1). Defining them by the printed Bernoulli
formula does not establish their identification with the analytic cosecant
series, nor the eta identity in Appendix J; those remain separate obligations.
-/

namespace CGLMPBounds

/-- The coefficient r_n from (I.1), intended for n≥1. -/
noncomputable def scalarCosecantCoefficient (n : ℕ) : ℝ :=
  2 * ((2 : ℝ) ^ (2 * n - 1) - 1) * |(bernoulli (2 * n) : ℝ)| /
    ((2 * n).factorial : ℝ) * (Real.pi / 2) ^ (2 * n - 1)

end CGLMPBounds
