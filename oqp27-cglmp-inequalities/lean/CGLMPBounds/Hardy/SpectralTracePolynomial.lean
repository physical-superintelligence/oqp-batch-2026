module

public import CGLMPBounds.Defs.HolomorphicPinching
public import CGLMPBounds.Hardy.SchwarzResolventSeries
public import CGLMPBounds.Hardy.DeterminantTrace
public import CGLMPBounds.Hardy.PositivePinchingPolynomial

@[expose] public section


/-! The root-multiset definition of holomorphic trace agrees with literal
matrix-polynomial trace, even for defective matrices. Coefficient uniqueness
in the genuine convergent resolvent series supplies this identification.
No diagonalizability assumption or chosen eigenvalue enumeration is used. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Matrix Polynomial Filter
open scoped Topology Matrix.Norms.Operator
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

lemma eventually_hasSum_multiset_geometric (s : Multiset ℂ) :
    ∀ᶠ t : ℂ in 𝓝 0,
      HasSum (fun n : ℕ => (s.map (fun a => a ^ n)).sum * t ^ n)
        (s.map (fun a => 1 / (1 - t * a))).sum := by
  induction s using Multiset.induction_on with
  | empty => exact Filter.Eventually.of_forall (by intro t; simpa using hasSum_zero)
  | @cons a s ih =>
    have hc : ContinuousAt (fun t : ℂ => ‖t * a‖) 0 := by fun_prop
    have he : ∀ᶠ t : ℂ in 𝓝 0, ‖t * a‖ < 1 :=
      hc.eventually_lt continuousAt_const (by simp)
    filter_upwards [he, ih] with t ht hs
    have ha : HasSum (fun n : ℕ => a ^ n * t ^ n) (1 / (1 - t * a)) := by
      simpa only [mul_pow, mul_comm, one_div] using
        hasSum_geometric_of_norm_lt_one ht
    simpa only [Multiset.map_cons, Multiset.sum_cons, add_mul] using ha.add hs

lemma hasFPowerSeriesAt_multiset_geometric (s : Multiset ℂ) :
    HasFPowerSeriesAt (fun t : ℂ => (s.map (fun a => 1 / (1 - t * a))).sum)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => (s.map (fun a => a ^ n)).sum)) 0 := by
  apply hasFPowerSeriesAt_iff.mpr
  filter_upwards [eventually_hasSum_multiset_geometric s] with t ht
  simpa only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, zero_add, mul_comm]
    using ht

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma trace_one_sub_inverse_eq_root_geometric (A : Matrix ι ι ℂ) {t : ℂ}
    (ht : ‖t • A‖ < 1) :
    Matrix.trace (resolvent (t • A) (1 : ℂ)) =
      (A.charpoly.roots.map (fun a => 1 / (1 - t * a))).sum := by
  by_cases ht0 : t = 0
  · subst t
    simp only [zero_smul, resolvent, map_one, sub_zero, Ring.inverse_one,
      Matrix.trace_one, zero_mul, sub_zero, div_one]
    simpa only [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, mul_one]
      using congrArg (fun n : ℕ => (n : ℂ)) (charpoly_roots_card A).symm
  · have hu : IsUnit (algebraMap ℂ (Matrix ι ι ℂ) t⁻¹ - A) := by
      have hh := IsUnit.smul ((Units.mk0 t ht0)⁻¹)
        (isUnit_one_sub_of_norm_lt_one ht)
      simpa only [Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0,
        smul_sub, smul_smul, inv_mul_cancel₀ ht0, one_smul,
        Algebra.algebraMap_eq_smul_one] using hh
    have hz : t⁻¹ ∉ spectrum ℂ A := spectrum.notMem_iff.mpr hu
    have hr : resolvent (t • A) (1 : ℂ) = t⁻¹ • resolvent A t⁻¹ := by
      simpa only [Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0,
        inv_inv] using
        (spectrum.units_smul_resolvent_self (r := (Units.mk0 t ht0)⁻¹) (a := A)).symm
    rw [hr, Matrix.trace_smul, smul_eq_mul, trace_resolvent_eq_root_sum A hz]
    have hp : ∀ a ∈ A.charpoly.roots,
        t⁻¹ * (1 / (t⁻¹ - a)) = 1 / (1 - t * a) := by
      intro a ha
      have hd := sub_ne_zero.mpr (charpoly_root_ne_of_not_mem_spectrum A hz a ha)
      have hd' : 1 - t * a ≠ 0 := by
        intro he
        apply hd
        have he' : t * a = 1 := (sub_eq_zero.mp he).symm
        apply sub_eq_zero.mpr
        apply mul_left_cancel₀ ht0
        rw [mul_inv_cancel₀ ht0, he']
      field_simp [ht0, hd, hd']
    rw [← Multiset.sum_map_mul_left]
    apply congrArg Multiset.sum
    exact Multiset.map_congr rfl hp

theorem trace_pow_eq_charpoly_root_sum (A : Matrix ι ι ℂ) (n : ℕ) :
    Matrix.trace (A ^ n) = (A.charpoly.roots.map (fun a => a ^ n)).sum := by
  have h0 : (1 : ℂ) ∉ spectrum ℂ (0 : Matrix ι ι ℂ) := by
    apply spectrum.notMem_iff.mpr
    simp only [map_one, sub_zero, isUnit_one]
  have hp := hasFPowerSeriesAt_trace_affine_resolvent (0 : Matrix ι ι ℂ) A h0
  have hc : ContinuousAt (fun t : ℂ => ‖t • A‖) 0 := by fun_prop
  have he : ∀ᶠ t : ℂ in 𝓝 0,
      Matrix.trace (resolvent (0 + t • A) (1 : ℂ)) =
        (A.charpoly.roots.map (fun a => 1 / (1 - t * a))).sum := by
    filter_upwards [hc.eventually_lt continuousAt_const (show ‖(0 : ℂ) • A‖ < 1 by simp)]
      with t ht
    simpa only [zero_add] using trace_one_sub_inverse_eq_root_geometric A ht
  have heq := (hp.congr he).eq_formalMultilinearSeries
    (hasFPowerSeriesAt_multiset_geometric A.charpoly.roots)
  have hn := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) heq
  simpa only [FormalMultilinearSeries.coeff_ofScalars, resolvent, map_one, sub_zero,
    Ring.inverse_one, one_mul, mul_one] using hn

lemma multiset_sum_polynomial_eval (s : Multiset ℂ) (f : ℂ[X]) :
    (s.map f.eval).sum =
      ∑ k ∈ f.support, f.coeff k * (s.map (fun a => a ^ k)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, mul_add, Finset.sum_add_distrib,
      ← ih]
    congr 1
    conv_lhs => rw [f.as_sum_support_C_mul_X_pow]
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]

theorem normalizedSpectralTrace_polynomial (f : ℂ[X]) (A : Matrix ι ι ℂ) :
    normalizedSpectralTrace f.eval A = normalizedPolynomialTrace f A := by
  rw [normalizedSpectralTrace, multiset_sum_polynomial_eval, Finset.sum_div,
    normalizedPolynomialTrace_eq_sum_trace]
  apply Finset.sum_congr rfl
  intro k _
  rw [← trace_pow_eq_charpoly_root_sum]
  ring

end
end CGLMPBounds.Hardy
