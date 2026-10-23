module

public import CGLMPBounds.Partition.PotentialCotangent
public import CGLMPBounds.Certificates.ScalarPartitionContinuity

@[expose] public section


/-! Continuity supplies the removable center in the actual cotangent second
 derivative. This completes that local calculus ingredient. -/

namespace CGLMPBounds.Partition
open Set Filter
open scoped Topology
open CGLMPBounds.Certificates
noncomputable section

lemma regularizedCotangentMoment_second_continuousOn :
    ContinuousOn (iteratedDeriv 2 (fun t : ℝ => regularizedCotangentMoment t / Real.pi))
      (Icc (-1 : ℝ) 1) := by
  have ha (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
      AnalyticAt ℝ (fun t : ℝ => regularizedCotangentMoment t / Real.pi) u :=
    (analyticAt_regularizedCotangentMoment (abs_le.mpr hu)).div_const
  have hc : ContDiffOn ℝ ⊤ (fun t : ℝ => regularizedCotangentMoment t / Real.pi)
      (Icc (-1 : ℝ) 1) := fun u hu => (ha u hu).contDiffAt.contDiffWithinAt
  have hd := hc.continuousOn_iteratedDerivWithin (m := 2) (by simp)
    (uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 1))
  apply hd.congr
  intro u hu
  exact (iteratedDerivWithin_eq_iteratedDeriv
    (uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 1)) (ha u hu).contDiffAt hu).symm

lemma regularizedCotangentMoment_second_zero :
    iteratedDeriv 2 (fun t : ℝ => regularizedCotangentMoment t / Real.pi) 0 = -(1 / 3 : ℝ) := by
  have hl := regularizedCotangentMoment_second_continuousOn.continuousAt
    (Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1))
  have hr : ContinuousAt (fun u : ℝ => -scalarCotangentRemainder ((Real.pi / 2) * u)) 0 := by
    have harg : ContinuousAt (fun u : ℝ => (Real.pi / 2) * u) 0 := by fun_prop
    simpa only [Function.comp_def] using ((scalarCotangentRemainder_continuousAt
      (by simpa using Real.pi_pos : |(Real.pi / 2) * (0 : ℝ)| < Real.pi)).comp harg).fun_neg
  have he : (iteratedDeriv 2 (fun t : ℝ => regularizedCotangentMoment t / Real.pi))
      =ᶠ[𝓝[>] (0 : ℝ)] (fun u => -scalarCotangentRemainder ((Real.pi / 2) * u)) := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with u hu
    apply regularizedCotangentMoment_second_nonzero hu.1.ne'
    apply (Real.sin_pos_of_pos_of_lt_pi _ _).ne'
    · exact mul_pos (by positivity : 0 < Real.pi / 2) hu.1
    · nlinarith [Real.pi_pos, hu.2]
  have hl' := hl.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hr' := hr.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have he0 := tendsto_nhds_unique
    (hl' : Tendsto (iteratedDeriv 2 (fun t : ℝ => regularizedCotangentMoment t / Real.pi))
      (𝓝[>] (0 : ℝ)) (𝓝 (iteratedDeriv 2 (fun t : ℝ => regularizedCotangentMoment t / Real.pi) 0)))
    (hr'.congr' he.symm)
  simpa [scalarCotangentRemainder] using he0

/-- The actual source cotangent derivative, including the removable center. -/
theorem regularizedCotangentMoment_second {u : ℝ} (hu : |u| ≤ 1 / 2) :
    iteratedDeriv 2 (fun t : ℝ => regularizedCotangentMoment t / Real.pi) u =
      -scalarCotangentRemainder ((Real.pi / 2) * u) := by
  by_cases hu0 : u = 0
  · subst u
    simpa [scalarCotangentRemainder] using regularizedCotangentMoment_second_zero
  · apply regularizedCotangentMoment_second_nonzero hu0
    have harg : (Real.pi / 2) * u ≠ 0 := mul_ne_zero (by positivity) hu0
    have hsmall : |(Real.pi / 2) * u| < Real.pi := by
      rw [abs_mul, abs_of_pos (show 0 < Real.pi / 2 by positivity)]
      have h := mul_le_mul_of_nonneg_left hu (show 0 ≤ Real.pi / 2 by positivity)
      nlinarith [Real.pi_pos]
    have h := (Real.sinc_pos hsmall).ne'
    rw [Real.sinc_of_ne_zero harg] at h
    exact (div_ne_zero_iff.mp h).1

end
end CGLMPBounds.Partition
