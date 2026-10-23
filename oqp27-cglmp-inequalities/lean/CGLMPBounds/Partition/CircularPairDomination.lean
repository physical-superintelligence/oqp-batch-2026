module

public import CGLMPBounds.Partition.UniformPairPoleBound
public import CGLMPBounds.Partition.CircularTriangleIdentity
public import CGLMPBounds.Partition.CircularCorrelationShift
public import CGLMPBounds.Partition.CircularBranch

@[expose] public section


/-! Uniform absolute-integral control of the literal circular pair kernel.
A change in the count forces a crossed boundary. The two integrable poles
are charged to the finite list of crossed boundaries; their integrals
have a bound independent of all boundary locations. -/

namespace CGLMPBounds.Partition
open Set MeasureTheory
open scoped Matrix
noncomputable section

private def pairPole (p : ℝ × ℝ) : ℝ :=
  1 / (2 * (p.2 - p.1)) + 1 / (2 * (1 - p.2 + p.1))

private def crossingPole (b : ℝ) : ℝ × ℝ → ℝ :=
  (Ioo (0 : ℝ) b ×ˢ Ioo b 1).indicator pairPole

private lemma crossingPole_nonneg (b : ℝ) (p : ℝ × ℝ) : 0 ≤ crossingPole b p := by
  classical
  by_cases hp : p ∈ Ioo (0 : ℝ) b ×ˢ Ioo b 1
  · simp only [crossingPole, indicator_of_mem hp, pairPole]
    have hx : 0 < p.2 - p.1 := by linarith [hp.1.2, hp.2.1]
    have hy : 0 < 1 - p.2 + p.1 := by linarith [hp.1.1, hp.2.2]
    positivity
  · simp only [crossingPole, indicator_of_notMem hp, le_refl]

private lemma crossingPole_integrable_bound (b : ℝ) (hb : b ∈ Icc (0 : ℝ) 1) :
    Integrable (crossingPole b)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) ∧
    (∫ p, crossingPole b p
      ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))) ≤ 2 := by
  have hsub : Ioo (0 : ℝ) b ×ˢ Ioo b 1 ⊆ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 := by
    intro p hp
    exact ⟨⟨hp.1.1, hp.1.2.trans_le hb.2⟩, ⟨hb.1.trans_lt hp.2.1, hp.2.2⟩⟩
  have he : (((volume.restrict (Ioo (0 : ℝ) 1)).prod
      (volume.restrict (Ioo (0 : ℝ) 1))).restrict (Ioo (0 : ℝ) b ×ˢ Ioo b 1)) =
      (volume.restrict (Ioo (0 : ℝ) b)).prod (volume.restrict (Ioo b 1)) := by
    rw [Measure.prod_restrict, Measure.restrict_restrict_of_subset hsub,
      Measure.prod_restrict]
  constructor
  · rw [crossingPole, integrable_indicator_iff (measurableSet_Ioo.prod measurableSet_Ioo)]
    rw [IntegrableOn, he]
    exact pair_endpoint_poles_integrable b hb
  · rw [crossingPole, integral_indicator (measurableSet_Ioo.prod measurableSet_Ioo), he]
    exact pair_endpoint_poles_integral_le_two b hb

lemma boundaryArcCount_ne_exists_crossing (d : ℕ) (T : Fin d → ℝ)
    {s t : ℝ} (hst : s ≤ t) (hne : boundaryArcCount d 0 s T ≠ boundaryArcCount d 0 t T) :
    ∃ j : Fin d, s ≤ Int.fract (T j) ∧ Int.fract (T j) < t := by
  classical
  by_contra hn
  push_neg at hn
  apply hne
  unfold boundaryArcCount
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, sub_zero]
  constructor
  · exact fun h => h.trans_le hst
  · intro h
    by_contra hs
    exact (not_lt.mpr (hn j (le_of_not_gt hs))) h

set_option maxHeartbeats 1000000 in
lemma measurable_circularStepPair_joint {d r : ℕ} (hd : 0 < d)
    (V : Fin d → Circulation.Mat r) (a : Fin d) :
    Measurable (fun p : (Fin d → ℝ) × (ℝ × ℝ) =>
      stepPairIntegrand (circularAssignmentStep hd V a p.1) p.2) := by
  have hleft : Measurable (fun p : (Fin d → ℝ) × (ℝ × ℝ) => (p.1, p.2.1)) := by
    fun_prop
  have hright : Measurable (fun p : (Fin d → ℝ) × (ℝ × ℝ) => (p.1, p.2.2)) := by
    fun_prop
  have hs : Measurable (fun p : (Fin d → ℝ) × (ℝ × ℝ) =>
      circularAssignmentStep hd V a p.1 p.2.1) := by
    simpa only [Function.comp_def] using
      (measurable_circularAssignmentStep_joint hd V a).comp hleft
  have ht : Measurable (fun p : (Fin d → ℝ) × (ℝ × ℝ) =>
      circularAssignmentStep hd V a p.1 p.2.2) := by
    simpa only [Function.comp_def] using
      (measurable_circularAssignmentStep_joint hd V a).comp hright
  have hsij (i j : Fin r) : Measurable
      (fun p : (Fin d → ℝ) × (ℝ × ℝ) =>
        circularAssignmentStep hd V a p.1 p.2.1 i j) := hs.eval.eval
  have htij (i j : Fin r) : Measurable
      (fun p : (Fin d → ℝ) × (ℝ × ℝ) =>
        circularAssignmentStep hd V a p.1 p.2.2 i j) := ht.eval.eval
  have hsum : Measurable (fun p : (Fin d → ℝ) × (ℝ × ℝ) =>
      ∑ i : Fin r, ∑ k : Fin r,
        star (circularAssignmentStep hd V a p.1 p.2.1 k i) *
          circularAssignmentStep hd V a p.1 p.2.2 k i) := by
    apply Finset.measurable_fun_sum
    intro i _
    apply Finset.measurable_fun_sum
    intro k _
    exact (continuous_star.measurable.comp (hsij k i)).mul (htij k i)
  have hcorr : Measurable (fun p : (Fin d → ℝ) × (ℝ × ℝ) =>
      Circulation.corr (circularAssignmentStep hd V a p.1 p.2.1)
        (circularAssignmentStep hd V a p.1 p.2.2)) := by
    simpa only [Circulation.corr, Circulation.tr, Matrix.trace,
      Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply] using
      hsum.div_const (r : ℂ)
  have hsec : Measurable scalarSecant := by
    unfold scalarSecant
    fun_prop
  have hdiff : Measurable (fun p : (Fin d → ℝ) × (ℝ × ℝ) => p.2.2 - p.2.1) :=
    measurable_snd.snd.sub measurable_snd.fst
  have hback : Measurable (fun p : (Fin d → ℝ) × (ℝ × ℝ) => 1 - p.2.2 + p.2.1) :=
    (measurable_const.sub measurable_snd.snd).add measurable_snd.fst
  unfold stepPairIntegrand
  exact Measurable.ite (measurableSet_lt measurable_snd.fst measurable_snd.snd)
    (((hsec.comp hdiff).mul (measurable_const.sub hcorr.re)).add
      ((hsec.comp hback).mul hcorr.im)) measurable_const

private lemma scalar_pair_norm_le_poles {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (ht : t < 1) (z : ℂ) :
    ‖scalarSecant (t - s) * (1 - z.re) + scalarSecant (1 - t + s) * z.im‖ ≤
      4 * ‖z - 1‖ * pairPole (s, t) := by
  let K : ℂ := -(scalarSecant (t - s) : ℂ) / 4 +
    Complex.I * (scalarSecant (1 - (t - s)) : ℂ) / 4
  have he : scalarSecant (t - s) * (1 - z.re) +
      scalarSecant (1 - t + s) * z.im = 4 * (K * (star z - 1)).re := by
    have h := quarterBranch_pair_kernel_real (t - s) z
    dsimp only [K]
    rw [show 1 - (t - s) = 1 - t + s by ring] at h ⊢
    linarith
  have hK : ‖K‖ ≤ pairPole (s, t) := by
    simpa only [K, pairPole, show 1 - (t - s) = 1 - t + s by ring] using
      quarterBranch_limit_kernel_norm_le (show t - s ∈ Ioo (0 : ℝ) 1 by constructor <;> linarith)
  rw [he, norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  calc
    _ ≤ 4 * ‖K * (star z - 1)‖ :=
      mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num)
    _ = 4 * ‖K‖ * ‖z - 1‖ := by
      have hz : star z - (1 : ℂ) = star (z - 1) := by simp only [star_sub, star_one]
      rw [norm_mul, hz, norm_star]
      ring
    _ ≤ 4 * ‖z - 1‖ * pairPole (s, t) := by
      calc
        _ ≤ 4 * pairPole (s, t) * ‖z - 1‖ := by gcongr
        _ = _ := by ring

set_option maxHeartbeats 1000000 in
/-- A genuine uniform L1 bound for every boundary configuration. The
constant is finite and depends only on the finite tuple and its label. -/
theorem circularStepPair_uniform_integral_norm_bound {d r : ℕ}
    (hd : 0 < d) (hr : 0 < r) (V : Fin d → Circulation.Mat r)
    (hV : ∀ j, (V j)ᴴ * V j = 1) (a : Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : Fin d → ℝ,
      (∫ p : ℝ × ℝ, ‖stepPairIntegrand (circularAssignmentStep hd V a T) p‖
        ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))) ≤ C := by
  classical
  let B : ℝ := ∑ n ∈ Finset.range (d + 1), ∑ m ∈ Finset.range (d + 1),
    ‖Circulation.corr (sourceCyclicExtension hd V (a.val + n))
      (sourceCyclicExtension hd V (a.val + m)) - 1‖
  have hB : 0 ≤ B := by positivity
  have hcorr (T : Fin d → ℝ) (s t : ℝ) :
      ‖Circulation.corr (circularAssignmentStep hd V a T s)
        (circularAssignmentStep hd V a T t) - 1‖ ≤ B := by
    have hn := Finset.mem_range.mpr (Nat.lt_succ_of_le (boundaryArcCount_le d 0 s T))
    have hm := Finset.mem_range.mpr (Nat.lt_succ_of_le (boundaryArcCount_le d 0 t T))
    change ‖Circulation.corr (sourceCyclicExtension hd V (a.val + boundaryArcCount d 0 s T))
      (sourceCyclicExtension hd V (a.val + boundaryArcCount d 0 t T)) - 1‖ ≤ B
    have hrow :
        ‖Circulation.corr (sourceCyclicExtension hd V (a.val + boundaryArcCount d 0 s T))
          (sourceCyclicExtension hd V (a.val + boundaryArcCount d 0 t T)) - 1‖ ≤
        ∑ m ∈ Finset.range (d + 1),
          ‖Circulation.corr (sourceCyclicExtension hd V (a.val + boundaryArcCount d 0 s T))
            (sourceCyclicExtension hd V (a.val + m)) - 1‖ :=
      Finset.single_le_sum (f := fun m =>
        ‖Circulation.corr (sourceCyclicExtension hd V (a.val + boundaryArcCount d 0 s T))
          (sourceCyclicExtension hd V (a.val + m)) - 1‖)
        (fun _ _ => norm_nonneg _) hm
    have hrows :
        (∑ m ∈ Finset.range (d + 1),
          ‖Circulation.corr (sourceCyclicExtension hd V (a.val + boundaryArcCount d 0 s T))
            (sourceCyclicExtension hd V (a.val + m)) - 1‖) ≤ B :=
      Finset.single_le_sum (f := fun n => ∑ m ∈ Finset.range (d + 1),
        ‖Circulation.corr (sourceCyclicExtension hd V (a.val + n))
          (sourceCyclicExtension hd V (a.val + m)) - 1‖)
        (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hn
    exact hrow.trans hrows
  refine ⟨8 * B * d, by positivity, ?_⟩
  intro T
  let μ : Measure (ℝ × ℝ) :=
    (volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))
  let G : ℝ × ℝ → ℝ := fun p => ∑ j : Fin d, crossingPole (Int.fract (T j)) p
  have hGi : Integrable G μ := integrable_finset_sum _ (fun j _ =>
    (crossingPole_integrable_bound _ ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩).1)
  have hGn (p : ℝ × ℝ) : 0 ≤ G p := Finset.sum_nonneg (fun j _ => crossingPole_nonneg _ _)
  have hGint : (∫ p, G p ∂μ) ≤ 2 * d := by
    rw [show (∫ p, G p ∂μ) = ∑ j : Fin d, ∫ p, crossingPole (Int.fract (T j)) p ∂μ by
      exact integral_finset_sum _ (fun j _ =>
        (crossingPole_integrable_bound _ ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩).1)]
    calc
      _ ≤ ∑ _j : Fin d, (2 : ℝ) := Finset.sum_le_sum (fun j _ =>
        (crossingPole_integrable_bound _ ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩).2)
      _ = _ := by simp; ring
  have hoff : ∀ᵐ p : ℝ × ℝ ∂μ, ∀ j : Fin d, p.1 ≠ Int.fract (T j) := by
    apply ae_all_iff.mpr
    intro j
    exact (Measure.quasiMeasurePreserving_fst
      (μ := volume.restrict (Ioo (0 : ℝ) 1))
      (ν := volume.restrict (Ioo (0 : ℝ) 1))).ae
        (ae_restrict_of_ae (volume.ae_ne (Int.fract (T j))))
  have hin : ∀ᵐ p : ℝ × ℝ ∂μ, p.1 ∈ Ioo (0 : ℝ) 1 ∧ p.2 ∈ Ioo (0 : ℝ) 1 := by
    dsimp only [μ]
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)
  have hmajor : ∀ᵐ p : ℝ × ℝ ∂μ,
      ‖stepPairIntegrand (circularAssignmentStep hd V a T) p‖ ≤ 4 * B * G p := by
    filter_upwards [hoff, hin] with p hoff hp
    by_cases hst : p.1 < p.2
    · by_cases hc : boundaryArcCount d 0 p.1 T = boundaryArcCount d 0 p.2 T
      · have he : circularAssignmentStep hd V a T p.1 = circularAssignmentStep hd V a T p.2 := by
          simp only [circularAssignmentStep_eq_cyclicExtension, hc]
        have hself : Circulation.corr (circularAssignmentStep hd V a T p.2)
            (circularAssignmentStep hd V a T p.2) = 1 := by
          simp [Circulation.corr, Circulation.tr,
            circularAssignmentStep_unitary hd V hV a T p.2, Nat.ne_of_gt hr]
        simp only [stepPairIntegrand, if_pos hst, he, hself, Complex.one_re,
          Complex.one_im, sub_self, mul_zero, add_zero, norm_zero]
        exact mul_nonneg (mul_nonneg (by norm_num) hB) (hGn p)
      · obtain ⟨j, hjs, hjt⟩ := boundaryArcCount_ne_exists_crossing d T hst.le hc
        have hj : p ∈ Ioo (0 : ℝ) (Int.fract (T j)) ×ˢ Ioo (Int.fract (T j)) 1 :=
          ⟨⟨hp.1.1, lt_of_le_of_ne hjs (hoff j)⟩, ⟨hjt, hp.2.2⟩⟩
        have hGP : pairPole p ≤ G p := by
          calc
            _ = crossingPole (Int.fract (T j)) p := by simp only [crossingPole, indicator_of_mem hj]
            _ ≤ G p := Finset.single_le_sum
              (f := fun j : Fin d => crossingPole (Int.fract (T j)) p)
              (fun _ _ => crossingPole_nonneg _ _) (Finset.mem_univ j)
        have hP : 0 ≤ pairPole p := by
          have he : pairPole p = crossingPole (Int.fract (T j)) p := by
            simp only [crossingPole, indicator_of_mem hj]
          rw [he]; exact crossingPole_nonneg _ _
        unfold stepPairIntegrand
        rw [if_pos hst]
        apply (scalar_pair_norm_le_poles hp.1.1 hst hp.2.2 _).trans
        calc
          _ ≤ 4 * B * pairPole p := by gcongr; exact hcorr T p.1 p.2
          _ ≤ 4 * B * G p := by gcongr
    · simp only [stepPairIntegrand, if_neg hst, norm_zero]
      exact mul_nonneg (mul_nonneg (by norm_num) hB) (hGn p)
  have hL := (circularAssignmentStep_pair_integrable hd hr V hV a T).norm
  calc
    _ ≤ ∫ p, 4 * B * G p ∂μ := integral_mono_ae hL (hGi.const_mul (4 * B)) hmajor
    _ = 4 * B * ∫ p, G p ∂μ := integral_const_mul _ _
    _ ≤ 8 * B * d := by
      calc
        _ ≤ 4 * B * (2 * d) := by gcongr
        _ = _ := by ring

/-- Absolute integrability holds jointly for every finite distribution
of the actual boundary points, so the D.3 interchange can use Fubini. -/
theorem circularStepPair_integrable_prod {d r : ℕ} (hd : 0 < d) (hr : 0 < r)
    (V : Fin d → Circulation.Mat r) (hV : ∀ j, (V j)ᴴ * V j = 1) (a : Fin d)
    (μ : Measure (Fin d → ℝ)) [IsFiniteMeasure μ] :
    Integrable (fun p : (Fin d → ℝ) × (ℝ × ℝ) =>
      stepPairIntegrand (circularAssignmentStep hd V a p.1) p.2)
      (μ.prod ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))) := by
  have hm : AEStronglyMeasurable
      (fun p : (Fin d → ℝ) × (ℝ × ℝ) =>
        stepPairIntegrand (circularAssignmentStep hd V a p.1) p.2)
      (μ.prod ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))) :=
    (measurable_circularStepPair_joint hd V a).aestronglyMeasurable
  apply (integrable_prod_iff hm).mpr
  constructor
  · exact Filter.Eventually.of_forall (circularAssignmentStep_pair_integrable hd hr V hV a)
  · obtain ⟨C, hC, hbound⟩ := circularStepPair_uniform_integral_norm_bound hd hr V hV a
    apply (integrable_const C).mono' hm.norm.integral_prod_right'
    filter_upwards [] with T
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact hbound T

end
end CGLMPBounds.Partition
