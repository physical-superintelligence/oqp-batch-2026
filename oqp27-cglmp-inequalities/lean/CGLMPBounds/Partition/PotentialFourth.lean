module

public import CGLMPBounds.Partition.PotentialCosecant
public import CGLMPBounds.Partition.PotentialSine
public import CGLMPBounds.Partition.PotentialFourierSummable

@[expose] public section


/-! The actual positive fourth derivative behind D.9. The centered analytic
formula is first differentiated, then transferred to the literal guarded
potential. Endpoint values are derivatives within the compact interval. -/

namespace CGLMPBounds.Partition
open Set Filter
open scoped Topology
noncomputable section

def centeredPartitionPotential (u : ℝ) : ℝ :=
  (u ^ 2 - 1 / 4) / 2 +
    (regularizedCosecantMoment u +
      2 * (-u * Real.sin ((Real.pi / 2) * u))) / (Real.sqrt 2 * Real.pi)

lemma regularizedPartitionPotential_eq_centered :
    regularizedPartitionPotential = fun x => centeredPartitionPotential (x - 1 / 2) := by
  funext x
  unfold regularizedPartitionPotential centeredPartitionPotential regularizedCosecantMoment
  rw [show Real.pi * (x - 1 / 2) / 2 = (Real.pi / 2) * (x - 1 / 2) by ring]
  ring

lemma centeredPartitionPotential_fourth {u : ℝ} (hu : |u| ≤ 1 / 2) :
    iteratedDeriv 4 centeredPartitionPotential u =
      (iteratedDeriv 4 regularizedCosecantMoment u +
        2 * iteratedDeriv 4 (fun t : ℝ => -t * Real.sin ((Real.pi / 2) * t)) u) /
          (Real.sqrt 2 * Real.pi) := by
  have hc : ContDiffAt ℝ 4 regularizedCosecantMoment u :=
    (analyticAt_regularizedCosecantMoment (hu.trans (by norm_num))).contDiffAt
  have hs : ContDiffAt ℝ 4
      (fun t : ℝ => -t * Real.sin ((Real.pi / 2) * t)) u := by fun_prop
  have hp : iteratedDeriv 4 (fun t : ℝ => (t ^ 2 - 1 / 4) / 2) u = 0 := by
    simp_rw [div_eq_mul_inv]
    rw [iteratedDeriv_mul_const_field,
      iteratedDeriv_fun_sub (by fun_prop) (by fun_prop)]
    norm_num [iteratedDeriv_pow, iteratedDeriv_const]
  unfold centeredPartitionPotential
  rw [iteratedDeriv_fun_add (by fun_prop) ((hc.add (contDiffAt_const.mul hs)).div_const _), hp]
  rw [iteratedDeriv_div_const,
    iteratedDeriv_fun_add hc (contDiffAt_const.mul hs), iteratedDeriv_const_mul_field]
  simp only [zero_add]

/-- Strict positivity throughout the source's shifted compact interval. -/
theorem centeredPartitionPotential_fourth_pos {u : ℝ} (hu : |u| ≤ 1 / 2) :
    0 < iteratedDeriv 4 centeredPartitionPotential u := by
  rw [centeredPartitionPotential_fourth hu]
  apply div_pos
  · exact add_pos_of_nonneg_of_pos (regularizedCosecantMoment_fourth_nonneg hu)
      (mul_pos (by norm_num) (source_negative_sine_moment_fourth_pos hu))
  · positivity

theorem regularizedPartitionPotential_fourth_pos {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    0 < iteratedDeriv 4 regularizedPartitionPotential x := by
  rw [regularizedPartitionPotential_eq_centered, iteratedDeriv_comp_sub_const]
  apply centeredPartitionPotential_fourth_pos
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2]

lemma partitionPotential_fourthWithin_pos {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    0 < iteratedDerivWithin 4 partitionPotential (Icc (0 : ℝ) 1) x := by
  have he : EqOn partitionPotential regularizedPartitionPotential (Icc (0 : ℝ) 1) :=
    fun _ ht => partitionPotential_eq_regularized ht
  rw [iteratedDerivWithin_congr he hx,
    iteratedDerivWithin_eq_iteratedDeriv
      (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1))
      (analyticAt_regularizedPartitionPotential hx).contDiffAt hx]
  exact regularizedPartitionPotential_fourth_pos hx

/-- The ordinary derivative needed in the literal Fourier integral is positive
on the open interval. -/
theorem partitionPotential_fourth_pos {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 < iteratedDeriv 4 partitionPotential x := by
  rw [← partitionPotential_iteratedDerivWithin_eq hx 4]
  exact partitionPotential_fourthWithin_pos ⟨hx.1.le, hx.2.le⟩

end
end CGLMPBounds.Partition
