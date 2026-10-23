module

public import ThreeCopyQutritWerner.SharpPartialTraceSum
public import ThreeCopyQutritWerner.SingularNuclearTrace

@[expose] public section


/-!
# The sharp nuclear partial-trace inequality

This joins the actual finite singular-vector reconstruction, its exact nuclear
weight sum, and the proved partial-trace coefficient bounds. It applies to
every bipartite square complex matrix, with no rank or normality restriction.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

/-- Wu--Zou's sharp quadratic partial-trace inequality, for the literal variational
nuclear norm and actual partial traces in arbitrary finite local dimensions. -/
theorem nuclearTrace_partialTrace_bound {L R : Type*}
    [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (X : Matrix (L × R) (L × R) ℂ) :
    frobSq (ptraceL X) + frobSq (ptraceR X) ≤ nuclearTrace X ^ 2 + Complex.normSq X.trace := by
  classical
  have hu (i : SingularPositiveIndex X) : vecNormSq (singularLeft X i) = 1 := by
    have h := singularLeft_braket X i i
    rw [if_pos rfl, braket_self] at h
    exact_mod_cast h
  have hv (i : SingularPositiveIndex X) : vecNormSq (singularRight X i) = 1 := by
    have h := singularRight_braket X i i
    rw [if_pos rfl, braket_self] at h
    exact_mod_cast h
  have ho (i j : SingularPositiveIndex X) (hij : i ≠ j) :
      braket (singularLeft X i) (singularLeft X j) = 0 := by
    rw [singularLeft_braket, if_neg hij]
  have he : X = ∑ i : SingularPositiveIndex X,
      (singularWeight X i : ℂ) • ketBra (singularLeft X i) (singularRight X i) := by
    ext r s
    simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, ketBra, mul_assoc] using
      singularFamily_reconstruct X r s
  have h := sharpPartialTrace_nonnegative_ray_sum_bound
    (singularLeft X) (singularRight X) (singularWeight X) hu hv ho
    (fun i => (singularWeight_pos X i).le)
  rw [← he, ← nuclearTrace_eq_sum_singularWeight X] at h
  exact h

/-- For a trace-zero transition the trace correction vanishes exactly. -/
theorem nuclearTrace_partialTrace_bound_of_trace_zero {L R : Type*}
    [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (X : Matrix (L × R) (L × R) ℂ) (hX : X.trace = 0) :
    frobSq (ptraceL X) + frobSq (ptraceR X) ≤ nuclearTrace X ^ 2 := by
  simpa only [hX, Complex.normSq_zero, add_zero] using nuclearTrace_partialTrace_bound X

end ThreeCopyQutritWerner
