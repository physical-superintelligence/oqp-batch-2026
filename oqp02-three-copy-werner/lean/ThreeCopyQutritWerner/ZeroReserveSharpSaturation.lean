module

public import ThreeCopyQutritWerner.ZeroReserveEquality
public import ThreeCopyQutritWerner.SharpPartialTraceMinors

@[expose] public section


/-!
# Actual reduced-transition equality data at a qutrit reserve zero

The three saturation equalities are linked to the literal transition matrices,
then to their actual singular families and polarized minor relations. No
transition-rank assumption or extra equality premise is introduced.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

/-- The three literal two-qutrit transition matrices, in physical site order. -/
def zeroReserveQutritTransition (u v : QutritSites → ℂ) :
    Fin 3 → Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  ![ptrace₁ (ketBra u v), ptrace₂ (ketBra u v), ptrace₃ (ketBra u v)]

/-- Every reduced transition of two orthogonal qutrit rays has ordinary trace zero. -/
theorem zeroReserveQutritTransition_trace_zero (u v : QutritSites → ℂ)
    (huv : braket u v = 0) (i : Fin 3) : (zeroReserveQutritTransition u v i).trace = 0 := by
  fin_cases i
  · exact zeroReserveTransition_site1_trace_zero u v huv
  · exact zeroReserveTransition_site2_trace_zero u v huv
  · exact zeroReserveTransition_site3_trace_zero u v huv

/-- A positive-weight reserve zero saturates the sharp partial-trace inequality
on each actual reduced transition, including its ordinary trace correction. -/
theorem zeroReserve_two_ray_eq_zero_transition_saturation (u v : QutritSites → ℂ)
    (hu : vecNormSq u = 1) (hv : vecNormSq v = 1) (huv : braket u v = 0)
    (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hz : zeroReserve ((lam : ℂ) • ketBra u u + (mu : ℂ) • ketBra v v) = 0)
    (i : Fin 3) :
    frobSq (ptraceL (zeroReserveQutritTransition u v i)) +
      frobSq (ptraceR (zeroReserveQutritTransition u v i)) =
      nuclearTrace (zeroReserveQutritTransition u v i) ^ 2 +
        Complex.normSq (zeroReserveQutritTransition u v i).trace := by
  have he := ((zeroReserve_two_ray_eq_zero_saturates u v hu hv huv lam mu hlam hmu hz).1 i).1
  rw [zeroReserveQutritTransition_trace_zero u v huv i, Complex.normSq_zero, add_zero]
  fin_cases i
  · change frobSq (ptraceL (ptrace₁ (ketBra u v))) +
        frobSq (ptraceR (ptrace₁ (ketBra u v))) = nuclearTrace (ptrace₁ (ketBra u v)) ^ 2
    rw [(zeroReserveTransition_site1_traces _).1, (zeroReserveTransition_site1_traces _).2]
    change frobSq (ptrace₁₂ (ketBra u v)) + frobSq (ptrace₁₃ (ketBra u v)) -
        frobSq (ptrace₁ (ketBra u v)) = nuclearTrace (ptrace₁ (ketBra u v)) ^ 2 -
        frobSq (ptrace₁ (ketBra u v)) at he
    linarith
  · change frobSq (ptraceL (ptrace₂ (ketBra u v))) +
        frobSq (ptraceR (ptrace₂ (ketBra u v))) = nuclearTrace (ptrace₂ (ketBra u v)) ^ 2
    rw [(zeroReserveTransition_site2_traces _).1, (zeroReserveTransition_site2_traces _).2]
    change frobSq (ptrace₁₂ (ketBra u v)) + frobSq (ptrace₂₃ (ketBra u v)) -
        frobSq (ptrace₂ (ketBra u v)) = nuclearTrace (ptrace₂ (ketBra u v)) ^ 2 -
        frobSq (ptrace₂ (ketBra u v)) at he
    linarith
  · change frobSq (ptraceL (ptrace₃ (ketBra u v))) +
        frobSq (ptraceR (ptrace₃ (ketBra u v))) = nuclearTrace (ptrace₃ (ketBra u v)) ^ 2
    rw [(zeroReserveTransition_site3_traces _).1, (zeroReserveTransition_site3_traces _).2]
    change frobSq (ptrace₁₃ (ketBra u v)) + frobSq (ptrace₂₃ (ketBra u v)) -
        frobSq (ptrace₃ (ketBra u v)) = nuclearTrace (ptrace₃ (ketBra u v)) ^ 2 -
        frobSq (ptrace₃ (ketBra u v)) at he
    linarith

/-- All singular gamma coefficients at each physical cut equal one. -/
theorem zeroReserve_two_ray_eq_zero_transition_gamma (u v : QutritSites → ℂ)
    (hu : vecNormSq u = 1) (hv : vecNormSq v = 1) (huv : braket u v = 0)
    (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hz : zeroReserve ((lam : ℂ) • ketBra u u + (mu : ℂ) • ketBra v v) = 0)
    (i : Fin 3) (p q : SingularPositiveIndex (zeroReserveQutritTransition u v i)) :
    sharpPartialTraceGamma (singularLeft (zeroReserveQutritTransition u v i) p)
      (singularRight (zeroReserveQutritTransition u v i) p)
      (singularLeft (zeroReserveQutritTransition u v i) q)
      (singularRight (zeroReserveQutritTransition u v i) q) = 1 :=
  sharpPartialTrace_singular_gamma_eq_one _
    (zeroReserve_two_ray_eq_zero_transition_saturation u v hu hv huv lam mu hlam hmu hz i) p q

/-- The actual singular maps of every reduced transition satisfy the common
complex-coefficient null polynomial at a positive-weight reserve zero. -/
theorem zeroReserve_two_ray_eq_zero_transition_common_null (u v : QutritSites → ℂ)
    (hu : vecNormSq u = 1) (hv : vecNormSq v = 1) (huv : braket u v = 0)
    (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hz : zeroReserve ((lam : ℂ) • ketBra u u + (mu : ℂ) • ketBra v v) = 0)
    (i : Fin 3) (z : SingularPositiveIndex (zeroReserveQutritTransition u v i) → ℂ) :
    sharpDoubleAnti (sharpTensorRay
      (fun r => ∑ j, z j * singularLeft (zeroReserveQutritTransition u v i) j r)
      (fun r => ∑ j, z j * singularRight (zeroReserveQutritTransition u v i) j r)) = 0 :=
  sharpPartialTrace_singular_common_combination_null _
    (zeroReserve_two_ray_eq_zero_transition_saturation u v hu hv huv lam mu hlam hmu hz i) z

/-- Every common left singular combination at every physical cut has reshape
rank at most two; no fixed local support is inferred from this pointwise fact. -/
theorem zeroReserve_two_ray_eq_zero_transition_common_rank (u v : QutritSites → ℂ)
    (hu : vecNormSq u = 1) (hv : vecNormSq v = 1) (huv : braket u v = 0)
    (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hz : zeroReserve ((lam : ℂ) • ketBra u u + (mu : ℂ) • ketBra v v) = 0)
    (i : Fin 3) (z : SingularPositiveIndex (zeroReserveQutritTransition u v i) → ℂ) :
    (sharpReshape (fun r => ∑ j,
      z j * singularLeft (zeroReserveQutritTransition u v i) j r)).rank ≤ 2 :=
  sharpPartialTrace_singular_common_reshape_rank_le_two _
    (zeroReserve_two_ray_eq_zero_transition_saturation u v hu hv huv lam mu hlam hmu hz i) z

end ThreeCopyQutritWerner
