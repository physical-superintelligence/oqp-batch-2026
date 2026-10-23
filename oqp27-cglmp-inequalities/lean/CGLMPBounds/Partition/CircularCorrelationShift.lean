module

public import CGLMPBounds.Defs.PartitionCyclic
public import CGLMPBounds.Partition.ArcCountGeometry
public import Mathlib.Data.Nat.Periodic

@[expose] public section


/-! Actual common-origin cancellation in the circular assignment. A
finite label average depends only on the number of boundaries in the
arc between the two points. The -i wrap phase is retained. -/

namespace CGLMPBounds.Partition
open scoped Matrix
noncomputable section

lemma sourceCyclicExtension_base {d r : ℕ} (hd : 0 < d)
    (V : Fin d → Circulation.Mat r) (a : Fin d) :
    sourceCyclicExtension hd V a.val = V a := by
  simp [sourceCyclicExtension, Nat.div_eq_of_lt a.isLt, Nat.mod_eq_of_lt a.isLt]

lemma sourceCyclicExtension_add_period {d r : ℕ} (hd : 0 < d)
    (V : Fin d → Circulation.Mat r) (n : ℕ) :
    sourceCyclicExtension hd V (n + d) = (-Complex.I) • sourceCyclicExtension hd V n := by
  simp only [sourceCyclicExtension, Nat.add_div_right _ hd, Nat.add_mod_right,
    pow_succ, smul_smul]
  congr 1
  ring

lemma corr_common_negative_I {r : ℕ} (V W : Circulation.Mat r) :
    Circulation.corr ((-Complex.I) • V) ((-Complex.I) • W) = Circulation.corr V W := by
  unfold Circulation.corr
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have he : (-Complex.I) * star (-Complex.I) = 1 := by simp [Complex.I_sq]
  rw [he, one_smul]

lemma cyclic_extension_correlation_periodic {d r : ℕ} (hd : 0 < d)
    (V : Fin d → Circulation.Mat r) (h : ℕ) :
    Function.Periodic (fun n : ℕ =>
      Circulation.corr (sourceCyclicExtension hd V n) (sourceCyclicExtension hd V (n + h))) d := by
  intro n
  dsimp only
  rw [show n + d + h = (n + h) + d by omega,
    sourceCyclicExtension_add_period, sourceCyclicExtension_add_period,
    corr_common_negative_I]

lemma finite_periodic_sum_shift {d : ℕ} (hd : 0 < d)
    {E : Type*} [AddCommMonoid E] (f : ℕ → E) (hf : Function.Periodic f d) (m : ℕ) :
    (∑ a : Fin d, f (a.val + m)) = ∑ a : Fin d, f a.val := by
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  let shift : Fin d := ⟨m % d, Nat.mod_lt _ hd⟩
  apply Fintype.sum_equiv (Equiv.addRight shift)
  intro a
  change f (a.val + m) = f ((a + shift).val)
  have he : (a + shift).val = (a.val + m) % d := by
    simp [Fin.val_add, shift, Nat.add_mod]
  rw [he]
  exact (hf.map_mod_nat (a.val + m)).symm

lemma circularAssignmentStep_eq_cyclicExtension {d r : ℕ} (hd : 0 < d)
    (V : Fin d → Circulation.Mat r) (a : Fin d) (T : Fin d → ℝ) (t : ℝ) :
    circularAssignmentStep hd V a T t =
      sourceCyclicExtension hd V (a.val + boundaryArcCount d 0 t T) := rfl

/-- Literal label-average invariance removes the boundaries before s.
The surviving extension retains the source phase on crossing label d. -/
theorem circularAssignmentStep_correlation_sum {d r : ℕ} (hd : 0 < d)
    (V : Fin d → Circulation.Mat r) (T : Fin d → ℝ)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    (∑ a : Fin d,
      Circulation.corr (circularAssignmentStep hd V a T s)
        (circularAssignmentStep hd V a T t)) =
      ∑ a : Fin d, Circulation.corr (V a)
        (sourceCyclicExtension hd V (a.val + boundaryArcCount d s (t - s) T)) := by
  let m := boundaryArcCount d 0 s T
  let h := boundaryArcCount d s (t - s) T
  have hcount : boundaryArcCount d 0 t T = m + h := by
    simpa only [m, h, Nat.add_comm] using
      (boundaryArcCount_add_initial d T hs hst ht).symm
  simp only [circularAssignmentStep_eq_cyclicExtension, hcount]
  have he (a : Fin d) : a.val + (m + h) = (a.val + m) + h := by omega
  simp only [he]
  rw [finite_periodic_sum_shift hd
    (fun n => Circulation.corr (sourceCyclicExtension hd V n)
      (sourceCyclicExtension hd V (n + h)))
    (cyclic_extension_correlation_periodic hd V h) m]
  simp only [sourceCyclicExtension_base, h]

end
end CGLMPBounds.Partition
