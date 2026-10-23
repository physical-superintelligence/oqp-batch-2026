module

public import CGLMPBounds.Defs.CircularPartition

@[expose] public section


/-! Finite coefficient integration for the literal scalar edge form.
These lemmas make no Hardy positivity assertion. -/

namespace CGLMPBounds.Partition
open Set MeasureTheory
noncomputable section

theorem scalarEdgeForm_intervalIntegrable {d r : ℕ} (w : ℕ → ℝ → ℝ)
    (hw : ∀ h, 0 < h → h < d → IntervalIntegrable (w h) volume 0 1)
    (V : Fin d → Circulation.Mat r) :
    IntervalIntegrable (fun x => scalarEdgeForm (fun h => w h x) V) volume 0 1 := by
  let f (i j : Fin d) (x : ℝ) := if i < j then
    w (j.val - i.val) x * (1 - (Circulation.corr (V i) (V j)).re) +
      w (d - (j.val - i.val)) x * (Circulation.corr (V i) (V j)).im else 0
  have hi (i j : Fin d) : IntervalIntegrable (f i j) volume 0 1 := by
    dsimp only [f]
    by_cases hij : i < j
    · simp only [if_pos hij]
      have h₁ : 0 < j.val - i.val := by have := i.isLt; have := j.isLt; omega
      have h₂ : j.val - i.val < d := by have := j.isLt; omega
      exact ((hw _ h₁ h₂).mul_const _).add ((hw _ (by omega) (by omega)).mul_const _)
    · simpa only [if_neg hij] using intervalIntegrable_const
  simpa only [scalarEdgeForm, Finset.sum_fn, f] using
    (IntervalIntegrable.sum Finset.univ (fun i _ =>
      IntervalIntegrable.sum Finset.univ (fun j _ => hi i j)))

theorem scalarEdgeForm_integral {d r : ℕ} (w : ℕ → ℝ → ℝ)
    (hw : ∀ h, 0 < h → h < d → IntervalIntegrable (w h) volume 0 1)
    (V : Fin d → Circulation.Mat r) :
    (∫ x in (0 : ℝ)..1, scalarEdgeForm (fun h => w h x) V) =
      scalarEdgeForm (fun h => ∫ x in (0 : ℝ)..1, w h x) V := by
  have hi (i j : Fin d) : IntervalIntegrable (fun x => if i < j then
      w (j.val - i.val) x * (1 - (Circulation.corr (V i) (V j)).re) +
      w (d - (j.val - i.val)) x * (Circulation.corr (V i) (V j)).im else 0) volume 0 1 := by
    by_cases hij : i < j
    · simp only [if_pos hij]
      have h₁ : 0 < j.val - i.val := by have := i.isLt; have := j.isLt; omega
      have h₂ : j.val - i.val < d := by have := j.isLt; omega
      exact ((hw _ h₁ h₂).mul_const _).add ((hw _ (by omega) (by omega)).mul_const _)
    · simpa only [if_neg hij] using intervalIntegrable_const
  unfold scalarEdgeForm
  rw [intervalIntegral.integral_finsetSum (fun i _ => by simpa only [Finset.sum_fn] using IntervalIntegrable.sum Finset.univ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [intervalIntegral.integral_finsetSum (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j
  · simp only [if_pos hij]
    have h₁ : 0 < j.val - i.val := by have := i.isLt; have := j.isLt; omega
    have h₂ : j.val - i.val < d := by have := j.isLt; omega
    rw [intervalIntegral.integral_add ((hw _ h₁ h₂).mul_const _)
      ((hw _ (by omega) (by omega)).mul_const _),
      intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
  · simp only [if_neg hij, intervalIntegral.integral_zero]

theorem scalarEdgeForm_const_mul {d r : ℕ} (c : ℝ) (w : ℕ → ℝ)
    (V : Fin d → Circulation.Mat r) :
    c * scalarEdgeForm w V = scalarEdgeForm (fun h => c * w h) V := by
  unfold scalarEdgeForm
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

end
end CGLMPBounds.Partition
