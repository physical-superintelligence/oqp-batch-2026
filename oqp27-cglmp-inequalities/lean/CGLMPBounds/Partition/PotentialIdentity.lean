module

public import CGLMPBounds.Partition.PotentialRegularization
public import CGLMPBounds.Partition.PotentialSymmetry

@[expose] public section


/-! Identification of the analytic shifted expression with the literal
source D.5 potential on [0,1]. The resulting smoothness is about the actual
guarded potential, not only an auxiliary formula. -/

namespace CGLMPBounds.Partition
noncomputable section

lemma regularizedPartitionPotential_symm (x : ℝ) :
    regularizedPartitionPotential (1 - x) = regularizedPartitionPotential x := by
  unfold regularizedPartitionPotential
  rw [show 1 - x - 1 / 2 = -(x - 1 / 2) by ring,
    show Real.pi * -(x - 1 / 2) / 2 = -(Real.pi * (x - 1 / 2) / 2) by ring,
    Real.sinc_neg, Real.sin_neg]
  ring

lemma regularizedPartitionPotential_zero : regularizedPartitionPotential 0 = 0 := by
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold regularizedPartitionPotential
  rw [show Real.pi * (0 - 1 / 2) / 2 = -(Real.pi / 4) by ring,
    Real.sinc_neg, Real.sin_neg,
    Real.sinc_of_ne_zero (show Real.pi / 4 ≠ 0 by positivity), Real.sin_pi_div_four]
  field_simp [hp, hs]
  nlinarith [hs2]

lemma partitionPotential_eq_regularized_interior {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) (hhalf : x ≠ 1 / 2) :
    partitionPotential x = regularizedPartitionPotential x := by
  let z : ℝ := Real.pi * (x - 1 / 2) / 2
  have hp := Real.pi_ne_zero
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  have hsqrt2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hz : z ≠ 0 := by
    dsimp [z]
    exact div_ne_zero (mul_ne_zero hp (sub_ne_zero.mpr hhalf)) (by norm_num)
  have hzabs : |z| < Real.pi := by
    rw [abs_lt]
    dsimp [z]
    constructor <;> nlinarith [Real.pi_pos, hx.1, hx.2]
  have hsz : Real.sin z ≠ 0 := by
    have h := (Real.sinc_pos hzabs).ne'
    rw [Real.sinc_of_ne_zero hz] at h
    exact (div_ne_zero_iff.mp h).1
  have hsin : Real.sin (Real.pi * x / 2) ≠ 0 := by
    apply (Real.sin_pos_of_pos_of_lt_pi _ _).ne'
    · exact div_pos (mul_pos Real.pi_pos hx.1) (by norm_num)
    · nlinarith [Real.pi_pos, hx.2]
  have hcos : Real.cos (Real.pi * x / 2) ≠ 0 := by
    apply (Real.cos_pos_of_mem_Ioo _).ne'
    constructor <;> nlinarith [Real.pi_pos, hx.1, hx.2]
  have hangle : Real.pi * x / 2 = z + Real.pi / 4 := by dsimp [z]; ring
  have hs : Real.sin (Real.pi * x / 2) =
      (Real.sin z + Real.cos z) * Real.sqrt 2 / 2 := by
    rw [hangle, Real.sin_add, Real.sin_pi_div_four, Real.cos_pi_div_four]
    ring
  have hc : Real.cos (Real.pi * x / 2) =
      (Real.cos z - Real.sin z) * Real.sqrt 2 / 2 := by
    rw [hangle, Real.cos_add, Real.sin_pi_div_four, Real.cos_pi_div_four]
    ring
  have hprod : Real.sin (Real.pi * x / 2) * Real.cos (Real.pi * x / 2) =
      (1 - 2 * Real.sin z ^ 2) / 2 := by
    calc
      _ = Real.sqrt 2 ^ 2 / 4 * (Real.cos z ^ 2 - Real.sin z ^ 2) := by
        rw [hs, hc]
        ring
      _ = _ := by rw [hsqrt2]; nlinarith [Real.sin_sq_add_cos_sq z]
  have hden : 1 / Real.cos (Real.pi * x / 2) - 1 / Real.sin (Real.pi * x / 2) =
      (Real.sqrt 2 * Real.sin z) /
        (Real.sin (Real.pi * x / 2) * Real.cos (Real.pi * x / 2)) := by
    field_simp [hsin, hcos]
    rw [hs, hc]
    ring
  have hcos2 : 1 - 2 * Real.sin z ^ 2 ≠ 0 := by
    intro h
    have hzprod := mul_ne_zero hsin hcos
    rw [hprod, h, zero_div] at hzprod
    exact hzprod rfl
  simp only [partitionPotential, if_neg (not_or_intro hx.1.ne' hx.2.ne), if_neg hhalf,
    regularizedPartitionPotential]
  change -(x * (1 - x)) / 2 + (2 * x - 1) /
    (Real.pi * (1 / Real.cos (Real.pi * x / 2) - 1 / Real.sin (Real.pi * x / 2))) =
    ((x - 1 / 2) ^ 2 - 1 / 4) / 2 +
      ((2 / Real.pi) / Real.sinc z - 2 * (x - 1 / 2) * Real.sin z) /
        (Real.sqrt 2 * Real.pi)
  rw [hden, hprod, Real.sinc_of_ne_zero hz]
  field_simp [hp, hsqrt, hsz, hcos2, hz]
  dsimp [z]
  ring

theorem partitionPotential_eq_regularized {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    partitionPotential x = regularizedPartitionPotential x := by
  by_cases hx0 : x = 0
  · subst x
    rw [partitionPotential_zero, regularizedPartitionPotential_zero]
  by_cases hx1 : x = 1
  · subst x
    rw [partitionPotential_one,
      show (1 : ℝ) = 1 - 0 by ring, regularizedPartitionPotential_symm,
      regularizedPartitionPotential_zero]
  by_cases hxh : x = 1 / 2
  · subst x
    rw [partitionPotential_half, regularizedPartitionPotential_half]
  exact partitionPotential_eq_regularized_interior
    ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), lt_of_le_of_ne hx.2 hx1⟩ hxh

theorem partitionPotential_contDiffOn :
    ContDiffOn ℝ ⊤ partitionPotential (Set.Icc (0 : ℝ) 1) := by
  apply regularizedPartitionPotential_contDiffOn.congr
  intro x hx
  exact partitionPotential_eq_regularized hx

end
end CGLMPBounds.Partition
