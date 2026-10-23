module

public import CGLMPBounds.Partition.CircularBasics

@[expose] public section


/-! Measurability and pointwise unitarity of the literal circular branch,
preparing the actual hypotheses of C.6. No Hardy lower bound is assumed. -/

namespace CGLMPBounds.Partition
open MeasureTheory
open scoped Matrix
noncomputable section

theorem measurable_boundaryArcCount_joint (d : ℕ) :
    Measurable (fun p : (Fin d → ℝ) × ℝ => boundaryArcCount d 0 p.2 p.1) := by
  classical
  unfold boundaryArcCount
  simp only [Finset.card_filter]
  apply Finset.measurable_fun_sum
  intro i _
  exact Measurable.ite (measurableSet_lt (by fun_prop) measurable_snd)
    measurable_const measurable_const

theorem measurable_circularAssignmentStep_joint {d r : ℕ} (hd : 0 < d)
    (V : Fin d → Circulation.Mat r) (a : Fin d) :
    Measurable (fun p : (Fin d → ℝ) × ℝ => circularAssignmentStep hd V a p.1 p.2) := by
  let G : ℕ → Circulation.Mat r := fun k =>
    (-Complex.I) ^ ((a.val + k) / d) • V ⟨(a.val + k) % d, Nat.mod_lt _ hd⟩
  exact (measurable_of_countable G).comp (measurable_boundaryArcCount_joint d)

theorem measurable_circularAssignmentBranch_joint {d r : ℕ} (hd : 0 < d)
    (V : Fin d → Circulation.Mat r) (a : Fin d) :
    Measurable (fun p : (Fin d → ℝ) × ℝ => circularAssignmentBranch hd V a p.1 p.2) := by
  have hs := measurable_circularAssignmentStep_joint hd V a
  unfold circularAssignmentBranch
  fun_prop

theorem circularAssignmentBranch_unitary {d r : ℕ} (hd : 0 < d)
    (V : Fin d → Circulation.Mat r) (hunit : ∀ j, (V j)ᴴ * V j = 1)
    (a : Fin d) (T : Fin d → ℝ) (t : ℝ) :
    (circularAssignmentBranch hd V a T t)ᴴ * circularAssignmentBranch hd V a T t = 1 := by
  have hs : circularAssignmentStep hd V a T t *
      (circularAssignmentStep hd V a T t)ᴴ = 1 :=
    (Matrix.mul_eq_one_comm_of_card_eq (Fin r) (Fin r) ℂ rfl).mp
      (circularAssignmentStep_unitary hd V hunit a T t)
  have hp : star (Complex.exp (((-Real.pi * t / 2 : ℝ) : ℂ) * Complex.I)) *
      Complex.exp (((-Real.pi * t / 2 : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [Complex.star_def, Complex.conj_mul']
    simp [Complex.norm_exp]
  have hp' := (mul_comm _ _).trans hp
  simp only [circularAssignmentBranch, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, hs, hp', one_smul]

end
end CGLMPBounds.Partition
