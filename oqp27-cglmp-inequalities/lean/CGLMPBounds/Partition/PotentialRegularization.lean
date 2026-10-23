module

public import CGLMPBounds.Defs.PartitionPotential
public import CGLMPBounds.Partition.SincRegularity

@[expose] public section


/-! Analytic shifted candidate for the literal D.5 removable expression.
The equality with partitionPotential is a separate, still-open bridge.
This module proves regularity of the actual displayed shifted function,
without assuming or claiming that bridge. -/

namespace CGLMPBounds.Partition
noncomputable section

def regularizedPartitionPotential (x : ℝ) : ℝ :=
  ((x - 1 / 2) ^ 2 - 1 / 4) / 2 +
    ((2 / Real.pi) / Real.sinc (Real.pi * (x - 1 / 2) / 2) -
      2 * (x - 1 / 2) * Real.sin (Real.pi * (x - 1 / 2) / 2)) /
        (Real.sqrt 2 * Real.pi)

lemma partition_sinc_pos {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    0 < Real.sinc (Real.pi * (x - 1 / 2) / 2) := by
  apply Real.sinc_pos
  rw [abs_lt]
  constructor <;> nlinarith [Real.pi_pos, hx.1, hx.2]

theorem analyticAt_regularizedPartitionPotential {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    AnalyticAt ℝ regularizedPartitionPotential x := by
  have hs : AnalyticAt ℝ (fun y : ℝ => Real.sinc (Real.pi * (y - 1 / 2) / 2)) x :=
    (analyticAt_real_sinc _).comp (by fun_prop)
  have hs0 := (partition_sinc_pos hx).ne'
  have hq : AnalyticAt ℝ
      (fun y : ℝ => (2 / Real.pi) / Real.sinc (Real.pi * (y - 1 / 2) / 2)) x :=
    analyticAt_const.div hs hs0
  have hpoly : AnalyticAt ℝ (fun y : ℝ => ((y - 1 / 2) ^ 2 - 1 / 4) / 2) x := by
    fun_prop
  have hscale : Real.sqrt 2 * Real.pi ≠ 0 := by positivity
  unfold regularizedPartitionPotential
  exact hpoly.add ((hq.sub (by fun_prop)).div analyticAt_const hscale)

theorem regularizedPartitionPotential_contDiffOn :
    ContDiffOn ℝ ⊤ regularizedPartitionPotential (Set.Icc (0 : ℝ) 1) := by
  intro x hx
  exact (analyticAt_regularizedPartitionPotential hx).contDiffAt.contDiffWithinAt

theorem regularizedPartitionPotential_half :
    regularizedPartitionPotential (1 / 2) = Real.sqrt 2 / Real.pi ^ 2 - 1 / 8 := by
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  norm_num only [regularizedPartitionPotential, sub_self, zero_pow, mul_zero,
    zero_div, Real.sinc_zero, Real.sin_zero, mul_zero, div_one, sub_zero]
  field_simp [hp, hs]
  nlinarith [hs2]

end
end CGLMPBounds.Partition
