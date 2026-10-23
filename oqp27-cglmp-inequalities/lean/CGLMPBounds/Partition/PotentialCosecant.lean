module

public import CGLMPBounds.Partition.SincRegularity
public import CGLMPBounds.Certificates.ScalarSteinSeries

@[expose] public section


/-! Nonnegative fourth derivative of the actual removable u*csc(πu/2).
The positive-side proof reuses the proved coefficient series as mathematics,
not as an additional hypothesis. Evenness and continuity handle the negative
side and the removable center. -/

namespace CGLMPBounds.Partition
open Filter Set
open scoped Topology
open CGLMPBounds.Certificates
noncomputable section

def regularizedCosecantMoment (u : ℝ) : ℝ :=
  (2 / Real.pi) / Real.sinc ((Real.pi / 2) * u)

lemma regularizedCosecantMoment_even (u : ℝ) :
    regularizedCosecantMoment (-u) = regularizedCosecantMoment u := by
  simp [regularizedCosecantMoment, Real.sinc_neg]

lemma analyticAt_regularizedCosecantMoment {u : ℝ} (hu : |u| ≤ 1) :
    AnalyticAt ℝ regularizedCosecantMoment u := by
  have hs : 0 < Real.sinc ((Real.pi / 2) * u) := by
    apply Real.sinc_pos
    rw [abs_mul, abs_of_pos (show 0 < Real.pi / 2 by positivity)]
    have h := mul_le_mul_of_nonneg_left hu (show 0 ≤ Real.pi / 2 by positivity)
    nlinarith [Real.pi_pos]
  exact analyticAt_const.div ((analyticAt_real_sinc _).comp (by fun_prop)) hs.ne'

lemma regularizedCosecantMoment_eq_regular {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) (3 / 2)) :
    regularizedCosecantMoment u = 2 / Real.pi + u * scalarRegularAnalytic u := by
  have hu0 : u ≠ 0 := hu.1.ne'
  have ha0 : Real.pi / 2 * u ≠ 0 := mul_ne_zero (by positivity) hu0
  have hs : Real.sin ((Real.pi / 2) * u) ≠ 0 := by
    apply (Real.sin_pos_of_pos_of_lt_pi _ _).ne'
    · exact mul_pos (by positivity) hu.1
    · nlinarith [Real.pi_pos, hu.2]
  unfold regularizedCosecantMoment scalarRegularAnalytic
  rw [Real.sinc_of_ne_zero ha0]
  field_simp [Real.pi_ne_zero, hu0, hs]
  <;> ring

lemma scalarRegularDerivativeSeries_nonneg (m : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ scalarRegularDerivativeSeries m u := by
  apply tsum_nonneg
  intro i
  unfold scalarRegularDerivativeTerm scalarPowerDerivative
  exact mul_nonneg (scalarCosecantCoefficient_pos_lt (i + 1) (by omega)).1.le
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hu _))

lemma scalarRegularAnalytic_contDiffAt {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) (3 / 2)) :
    ContDiffAt ℝ 4 scalarRegularAnalytic u := by
  have hs : Real.sin ((Real.pi / 2) * u) ≠ 0 := by
    apply (Real.sin_pos_of_pos_of_lt_pi _ _).ne'
    · exact mul_pos (by positivity) hu.1
    · nlinarith [Real.pi_pos, hu.2]
  have hz : (Real.pi / 2) * u ≠ 0 := mul_ne_zero (by positivity) hu.1.ne'
  have hsin : AnalyticAt ℝ (fun t : ℝ => Real.sin ((Real.pi / 2) * t)) u := by
    fun_prop
  have hlin : AnalyticAt ℝ (fun t : ℝ => (Real.pi / 2) * t) u := by fun_prop
  unfold scalarRegularAnalytic
  exact ((analyticAt_const.div hsin hs).sub (analyticAt_const.div hlin hz)).contDiffAt

lemma regularizedCosecantMoment_fourth_nonneg_pos {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) (3 / 2)) :
    0 ≤ iteratedDeriv 4 regularizedCosecantMoment u := by
  have he : regularizedCosecantMoment =ᶠ[𝓝 u]
      (fun t => 2 / Real.pi + t * scalarRegularAnalytic t) := by
    filter_upwards [isOpen_Ioo.mem_nhds hu] with t ht
    exact regularizedCosecantMoment_eq_regular ht
  rw [he.iteratedDeriv_eq 4, iteratedDeriv_const_add (by norm_num : 0 < 4)]
  have hd : iteratedDeriv 4 (fun t => t * scalarRegularAnalytic t) u =
      u * iteratedDeriv 4 scalarRegularAnalytic u +
        4 * iteratedDeriv 3 scalarRegularAnalytic u := by
    rw [iteratedDeriv_fun_mul (by fun_prop) (scalarRegularAnalytic_contDiffAt hu)]
    norm_num [Finset.sum_range_succ, iteratedDeriv_fun_id]
  rw [hd, scalarRegularAnalytic_iteratedDeriv 4 hu,
    scalarRegularAnalytic_iteratedDeriv 3 hu]
  exact add_nonneg (mul_nonneg hu.1.le (scalarRegularDerivativeSeries_nonneg 4 hu.1.le))
    (mul_nonneg (by norm_num) (scalarRegularDerivativeSeries_nonneg 3 hu.1.le))

lemma regularizedCosecantMoment_fourth_even (u : ℝ) :
    iteratedDeriv 4 regularizedCosecantMoment (-u) =
      iteratedDeriv 4 regularizedCosecantMoment u := by
  have he : (fun t => regularizedCosecantMoment (-t)) = regularizedCosecantMoment :=
    funext regularizedCosecantMoment_even
  have h := iteratedDeriv_comp_neg 4 regularizedCosecantMoment u
  rw [he] at h
  norm_num at h
  exact h.symm

lemma regularizedCosecantMoment_fourth_continuousOn :
    ContinuousOn (iteratedDeriv 4 regularizedCosecantMoment) (Icc (-1 : ℝ) 1) := by
  have hc : ContDiffOn ℝ ⊤ regularizedCosecantMoment (Icc (-1 : ℝ) 1) := by
    intro u hu
    exact (analyticAt_regularizedCosecantMoment (abs_le.mpr hu)).contDiffAt.contDiffWithinAt
  have hd := hc.continuousOn_iteratedDerivWithin (m := 4) (by simp)
    (uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 1))
  apply hd.congr
  intro u hu
  exact (iteratedDerivWithin_eq_iteratedDeriv
    (uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 1))
    (analyticAt_regularizedCosecantMoment (abs_le.mpr hu)).contDiffAt hu).symm

lemma regularizedCosecantMoment_fourth_nonneg_zero :
    0 ≤ iteratedDeriv 4 regularizedCosecantMoment 0 := by
  have hc := regularizedCosecantMoment_fourth_continuousOn.continuousAt
    (Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1))
  apply ge_of_tendsto (hc.tendsto.mono_left nhdsWithin_le_nhds :
    Tendsto (iteratedDeriv 4 regularizedCosecantMoment) (𝓝[>] (0 : ℝ))
      (𝓝 (iteratedDeriv 4 regularizedCosecantMoment 0)))
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with u hu
  exact regularizedCosecantMoment_fourth_nonneg_pos ⟨hu.1, by linarith [hu.2]⟩

/-- The cosecant contribution needed in the source's positive fourth derivative. -/
theorem regularizedCosecantMoment_fourth_nonneg {u : ℝ} (hu : |u| ≤ 1 / 2) :
    0 ≤ iteratedDeriv 4 regularizedCosecantMoment u := by
  rcases lt_trichotomy u 0 with hu0 | rfl | hu0
  · rw [← regularizedCosecantMoment_fourth_even]
    exact regularizedCosecantMoment_fourth_nonneg_pos
      ⟨neg_pos.mpr hu0, by linarith [(abs_le.mp hu).1]⟩
  · exact regularizedCosecantMoment_fourth_nonneg_zero
  · exact regularizedCosecantMoment_fourth_nonneg_pos
      ⟨hu0, by linarith [(abs_le.mp hu).2]⟩

end
end CGLMPBounds.Partition
