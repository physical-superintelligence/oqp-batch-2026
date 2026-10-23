module

public import CGLMPBounds.Defs.PartitionPairForm
public import CGLMPBounds.Partition.CircularCountExpectation
public import CGLMPBounds.Partition.CyclicPairForm

@[expose] public section


/-! The actual expectation of the scalar-subtracted circular pair
integrand, at fixed s<t, is the literal source edge form with genuine
count atom masses. No triangle/probability integral interchange is used
or assumed by this finite-measure calculation. -/

namespace CGLMPBounds.Partition
open Set MeasureTheory
open scoped Matrix
noncomputable section

private lemma circular_pair_linear_sum {d r : ℕ} (hd : 0 < d)
    (V : Fin d → Circulation.Mat r) (T : Fin d → ℝ) (A B : ℝ)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    (∑ a : Fin d,
      (A * (1 - (Circulation.corr (circularAssignmentStep hd V a T s)
        (circularAssignmentStep hd V a T t)).re) +
      B * (Circulation.corr (circularAssignmentStep hd V a T s)
        (circularAssignmentStep hd V a T t)).im)) =
    ∑ a : Fin d,
      (A * (1 - (Circulation.corr (V a)
        (sourceCyclicExtension hd V (a.val + boundaryArcCount d s (t - s) T))).re) +
      B * (Circulation.corr (V a)
        (sourceCyclicExtension hd V (a.val + boundaryArcCount d s (t - s) T))).im) := by
  simp only [mul_sub, mul_one, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Complex.re_sum, ← Complex.im_sum]
  rw [circularAssignmentStep_correlation_sum hd V T hs hst ht]

private lemma cyclic_identity_pair_value {d r : ℕ} (hd : 0 < d) (hr : 0 < r)
    (a : Fin d) {h : ℕ} (hh : h ≤ d) (A B : ℝ) :
    A * (1 - (Circulation.corr (1 : Circulation.Mat r)
      (sourceCyclicExtension hd (fun _ => 1) (a.val + h))).re) +
    B * (Circulation.corr (1 : Circulation.Mat r)
      (sourceCyclicExtension hd (fun _ => 1) (a.val + h))).im =
      if a.val + h < d then 0 else A - B := by
  rw [sourceCyclicExtension_one_turn hd (fun _ => (1 : Circulation.Mat r)) a hh]
  have hc : Circulation.corr (1 : Circulation.Mat r) 1 = 1 := by
    simp [Circulation.corr, Circulation.tr, Nat.ne_of_gt hr]
  split_ifs with hlt
  · simp [hc]
  · rw [corr_negative_I_right, hc]
    simp [sub_eq_add_neg]

theorem circularStepPair_expected_sub_scalar {d r : ℕ} (hd : 0 < d) (hr : 0 < r)
    (μ : Measure (Fin d → ℝ)) [IsFiniteMeasure μ]
    (V : Fin d → Circulation.Mat r) (hV : ∀ j, (V j)ᴴ * V j = 1)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ 1) :
    (∫ T, ∑ a : Fin d,
      (stepPairIntegrand (circularAssignmentStep hd V a T) (s, t) -
        stepPairIntegrand (circularAssignmentStep hd (fun _ => (1 : Circulation.Mat r)) a T)
          (s, t)) ∂μ) =
      scalarEdgeForm (fun h =>
        scalarSecant (t - s) * μ.real {T | boundaryArcCount d s (t - s) T = h} +
          scalarSecant (1 - t + s) * μ.real {T | boundaryArcCount d s (t - s) T = d - h}) V := by
  let A := scalarSecant (t - s)
  let B := scalarSecant (1 - t + s)
  let F : ℕ → ℝ := fun h => ∑ a : Fin d,
    (A * (1 - (Circulation.corr (V a) (sourceCyclicExtension hd V (a.val + h))).re) +
      B * (Circulation.corr (V a) (sourceCyclicExtension hd V (a.val + h))).im -
        (if a.val + h < d then 0 else A - B))
  have he (T : Fin d → ℝ) :
      (∑ a : Fin d,
        (stepPairIntegrand (circularAssignmentStep hd V a T) (s, t) -
          stepPairIntegrand (circularAssignmentStep hd (fun _ => (1 : Circulation.Mat r)) a T)
            (s, t))) = F (boundaryArcCount d s (t - s) T) := by
    simp only [stepPairIntegrand, if_pos hst, Finset.sum_sub_distrib]
    rw [circular_pair_linear_sum hd V T A B hs hst.le ht,
      circular_pair_linear_sum hd (fun _ => (1 : Circulation.Mat r)) T A B hs hst.le ht]
    simp_rw [cyclic_identity_pair_value hd hr _ (boundaryArcCount_le d s (t - s) T) A B]
    exact (Finset.sum_sub_distrib _ _).symm
  rw [integral_congr_ae (Filter.Eventually.of_forall he),
    integral_function_finite_count μ (boundaryArcCount d s (t - s)) d
      (measurable_boundaryArcCount d s (t - s)) (boundaryArcCount_le d s (t - s)) F]
  simp only [smul_eq_mul]
  exact cyclic_count_pair_sum_eq_scalarEdgeForm hd hr V hV
    (fun h => μ.real {T | boundaryArcCount d s (t - s) T = h}) A B

end
end CGLMPBounds.Partition
