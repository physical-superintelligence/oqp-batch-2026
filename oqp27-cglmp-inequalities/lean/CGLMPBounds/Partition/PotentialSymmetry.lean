module

public import CGLMPBounds.Defs.PartitionPotential

@[expose] public section


/-! Literal values and reflection symmetry of the D.5 potential.
Smoothness across the removable points and the positive Fourier expansion
are separate obligations. -/

namespace CGLMPBounds.Partition
noncomputable section

@[simp] theorem partitionPotential_zero : partitionPotential 0 = 0 := by
  simp [partitionPotential]

@[simp] theorem partitionPotential_one : partitionPotential 1 = 0 := by
  simp [partitionPotential]

theorem partitionPotential_half :
    partitionPotential (1 / 2) = Real.sqrt 2 / Real.pi ^ 2 - 1 / 8 := by
  norm_num [partitionPotential]

theorem partitionPotential_symm (x : ℝ) :
    partitionPotential (1 - x) = partitionPotential x := by
  by_cases hx0 : x = 0
  · subst x
    simp
  by_cases hx1 : x = 1
  · subst x
    simp
  by_cases hxh : x = 1 / 2
  · rw [hxh]
    congr 1
    ring
  have hy0 : 1 - x ≠ 0 := by intro h; apply hx1; linarith
  have hy1 : 1 - x ≠ 1 := by intro h; apply hx0; linarith
  have hyh : 1 - x ≠ 1 / 2 := by intro h; apply hxh; linarith
  simp only [partitionPotential, if_neg (not_or_intro hx0 hx1), if_neg hxh,
    if_neg (not_or_intro hy0 hy1), if_neg hyh]
  rw [show Real.pi * (1 - x) / 2 = Real.pi / 2 - Real.pi * x / 2 by ring,
    Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
  rw [show 1 / Real.sin (Real.pi * x / 2) - 1 / Real.cos (Real.pi * x / 2) =
    -(1 / Real.cos (Real.pi * x / 2) - 1 / Real.sin (Real.pi * x / 2)) by ring,
    mul_neg, div_neg]
  ring

end
end CGLMPBounds.Partition
