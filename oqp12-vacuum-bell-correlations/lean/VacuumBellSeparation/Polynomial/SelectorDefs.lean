module

public import Mathlib

@[expose] public section


/-!
# Statement seed extracted from Polynomial/Selector

Literal declarations are unchanged; theorem conclusions remain in the implementation module.
-/

open Polynomial

namespace VacuumBellSeparation

/-- The polynomial selector `𝗉_N(z) = (1 - z)^N Σ_{k<N} C(N+k-1, k) z^k` of (7.4). -/
noncomputable def selector (N : ℕ) : ℝ[X] :=
  (1 - X) ^ N * ∑ k ∈ Finset.range N, C (((N + k - 1).choose k : ℕ) : ℝ) * X ^ k


/-- The sum of the absolute values of the coefficients of a real polynomial,
`Σ_{i ≤ deg p} |p_i|` (the `ℓ¹` norm of its coefficient vector). -/
noncomputable def coeffAbsSum (p : ℝ[X]) : ℝ :=
  ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i|


end VacuumBellSeparation
