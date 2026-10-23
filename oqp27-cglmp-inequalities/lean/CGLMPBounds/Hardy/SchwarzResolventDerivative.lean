module

public import CGLMPBounds.Hardy.SchwarzResolventSeries
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Mul

@[expose] public section


/-!
# The actual trace-resolvent derivative in the proof of (C.7)

The source p.9 differentiates Tr[(R_H(lambda)Y)^k]. The factor k comes from
cyclicity of the trace, not commutativity of the matrices. This file derives
the inverse derivative from the Banach-algebra inverse theorem and retains
every noncommutative product before applying trace cyclicity.

The contour integration-by-parts, contour inversion, and identification with
the positive-cluster functional calculus remain separate.
-/

open Complex Matrix Filter
open scoped Topology Matrix.Norms.Operator

namespace CGLMPBounds.Hardy
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

lemma hasDerivAt_matrix_resolvent (H : Matrix ι ι ℂ) {«λ» : ℂ}
    («hλ» : «λ» ∉ spectrum ℂ H) :
    HasDerivAt (resolvent H) (-(resolvent H «λ») ^ 2) «λ» := by
  let P : Matrix ι ι ℂ := algebraMap ℂ (Matrix ι ι ℂ) «λ» - H
  have hu : IsUnit P := by
    simpa only [P, spectrum.mem_iff, not_not] using «hλ»
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  letI : TopologicalSpace (Matrix ι ι ℂ) :=
    (Matrix.linftyOpNormedRing : NormedRing (Matrix ι ι ℂ)).toUniformSpace.toTopologicalSpace
  have hi : HasFDerivAt (Ring.inverse : Matrix ι ι ℂ → Matrix ι ι ℂ)
      (-ContinuousLinearMap.mulLeftRight ℂ (Matrix ι ι ℂ) (Ring.inverse P) (Ring.inverse P)) P := by
    simpa only [← Ring.inverse_of_isUnit hu, hu.unit_spec] using
      (hasFDerivAt_ringInverse (𝕜 := ℂ) hu.unit)
  have ha : HasDerivAt (fun z : ℂ => algebraMap ℂ (Matrix ι ι ℂ) z - H) 1 «λ» := by
    simpa only [Algebra.algebraMap_eq_smul_one, one_smul, id_eq] using
      ((hasDerivAt_id «λ»).smul_const (1 : Matrix ι ι ℂ)).sub_const H
  have hr : HasDerivAt (resolvent H) (-(resolvent H «λ») ^ 2) «λ» := by
    simpa only [Function.comp_def, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.mulLeftRight_apply, mul_one, P, resolvent, pow_two] using!
      hi.comp_hasDerivAt «λ» ha
  let ev : Matrix ι ι ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun M => M i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let evc : Matrix ι ι ℂ →L[ℂ] ℂ := ev.toContinuousLinearMap
  have hij := evc.hasFDerivAt.comp_hasDerivAt «λ» hr
  change HasDerivAt (fun z => resolvent H z i j) ((-(resolvent H «λ») ^ 2) i j) «λ» at hij
  exact hij

lemma hasDerivAt_trace_matrix_pow {f : ℂ → Matrix ι ι ℂ} {f' : Matrix ι ι ℂ} {z : ℂ}
    (hf : HasDerivAt f f' z) (k : ℕ) :
    HasDerivAt (fun t : ℂ => Matrix.trace (f t ^ k))
      ((k : ℂ) * Matrix.trace (f z ^ (k - 1) * f')) z := by
  let tr : Matrix ι ι ℂ →L[ℂ] ℂ := (Matrix.traceLinearMap ι ℂ ℂ).toContinuousLinearMap
  have ht := tr.hasFDerivAt.comp_hasDerivAt z (hf.fun_pow' k)
  change HasDerivAt (fun t : ℂ => Matrix.trace (f t ^ k))
    (Matrix.trace (∑ i ∈ Finset.range k, f z ^ (k.pred - i) * f' * f z ^ i)) z at ht
  have he : Matrix.trace (∑ i ∈ Finset.range k, f z ^ (k.pred - i) * f' * f z ^ i) =
      (k : ℂ) * Matrix.trace (f z ^ (k - 1) * f') := by
    rw [Matrix.trace_sum]
    have hterm : ∀ i ∈ Finset.range k,
        Matrix.trace (f z ^ (k.pred - i) * f' * f z ^ i) =
          Matrix.trace (f z ^ (k - 1) * f') := by
      intro i hi
      have hi' : i < k := Finset.mem_range.mp hi
      have hn : i + (k.pred - i) = k - 1 := by
        simp only [Nat.pred_eq_sub_one]
        omega
      rw [Matrix.trace_mul_cycle, ← pow_add, hn]
    rw [Finset.sum_congr rfl hterm]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rwa [he] at ht

/-- The exact source derivative used for integration by parts on p.9.
No assumption that the two Hermitian inputs commute is present or needed. -/
theorem hasDerivAt_trace_resolvent_mul_pow (H Y : Matrix ι ι ℂ) {«λ» : ℂ}
    («hλ» : «λ» ∉ spectrum ℂ H) {k : ℕ} (hk : 0 < k) :
    HasDerivAt (fun z : ℂ => Matrix.trace ((resolvent H z * Y) ^ k))
      (-(k : ℂ) * Matrix.trace ((resolvent H «λ» * Y) ^ k * resolvent H «λ»)) «λ» := by
  have ht := hasDerivAt_trace_matrix_pow ((hasDerivAt_matrix_resolvent H «hλ»).mul_const Y) k
  have he : (-(resolvent H «λ») ^ 2) * Y =
      -(resolvent H «λ» * (resolvent H «λ» * Y)) := by
    simp only [pow_two, neg_mul, mul_assoc]
  have hn : k - 1 + 1 = k := by omega
  convert ht using 1
  rw [he, mul_neg, Matrix.trace_neg, ← mul_assoc, Matrix.trace_mul_cycle,
    ← pow_succ', hn]
  ring

end
end CGLMPBounds.Hardy
