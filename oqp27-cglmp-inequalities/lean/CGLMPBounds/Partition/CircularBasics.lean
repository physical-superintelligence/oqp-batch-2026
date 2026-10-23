module

public import CGLMPBounds.Defs.CircularPartition
public import CGLMPBounds.Partition.ArcCountGeometry

@[expose] public section


/-! Pointwise fourth-root algebra for the actual circular assignment.
The label wrap contributes -i and preserves both unitarity and fourth
powers. No analytic Hardy claim is used. -/

namespace CGLMPBounds.Partition
open scoped Matrix
noncomputable section

lemma negative_I_power_fourth (n : ℕ) : ((-Complex.I) ^ n) ^ 4 = 1 := by
  rw [← pow_mul, Nat.mul_comm n 4, pow_mul]
  have h : (-Complex.I) ^ 4 = 1 := by norm_num [pow_succ, Complex.I_sq]
  rw [h, one_pow]

lemma negative_I_power_unitary (n : ℕ) : star ((-Complex.I) ^ n) * (-Complex.I) ^ n = 1 := by
  rw [star_pow, ← mul_pow]
  have h : star (-Complex.I) * (-Complex.I) = 1 := by simp [Complex.I_sq]
  rw [h, one_pow]

theorem circularAssignmentStep_fourth {d r : ℕ} (hd : 0 < d)
    (V : Fin d → Circulation.Mat r) (hfour : ∀ j, V j ^ 4 = 1)
    (a : Fin d) (T : Fin d → ℝ) (t : ℝ) :
    circularAssignmentStep hd V a T t ^ 4 = 1 := by
  simp only [circularAssignmentStep, smul_pow, hfour, negative_I_power_fourth, one_smul]

theorem circularAssignmentStep_unitary {d r : ℕ} (hd : 0 < d)
    (V : Fin d → Circulation.Mat r) (hunit : ∀ j, (V j)ᴴ * V j = 1)
    (a : Fin d) (T : Fin d → ℝ) (t : ℝ) :
    (circularAssignmentStep hd V a T t)ᴴ * circularAssignmentStep hd V a T t = 1 := by
  have hphase (k : ℕ) : (-Complex.I) ^ k * star ((-Complex.I) ^ k) = 1 :=
    (mul_comm _ _).trans (negative_I_power_unitary k)
  simp only [circularAssignmentStep, Matrix.conjTranspose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, hunit, hphase, one_smul]

theorem circularAssignmentBranch_fourth {d r : ℕ} (hd : 0 < d)
    (V : Fin d → Circulation.Mat r) (hfour : ∀ j, V j ^ 4 = 1)
    (a : Fin d) (T : Fin d → ℝ) (t : ℝ) :
    circularAssignmentBranch hd V a T t ^ 4 =
      Complex.exp (((-2 * Real.pi * t : ℝ) : ℂ) * Complex.I) •
        (1 : Circulation.Mat r) := by
  rw [circularAssignmentBranch, smul_pow, ← Matrix.conjTranspose_pow,
    circularAssignmentStep_fourth hd V hfour, Matrix.conjTranspose_one,
    ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

end
end CGLMPBounds.Partition
