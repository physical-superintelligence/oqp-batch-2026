module

public import Mathlib

@[expose] public section


/-! A reusable compact second integration-by-parts identity. Both functions
vanish at the two endpoints; only genuine smoothness is assumed. -/

namespace CGLMPBounds.Partition
open Set MeasureTheory
noncomputable section

theorem integral_second_within_transfer {f g : ℝ → ℝ}
    (hf : ContDiffOn ℝ ⊤ f (Icc (0 : ℝ) 1))
    (hg : ContDiffOn ℝ ⊤ g (Icc (0 : ℝ) 1))
    (hf0 : f 0 = 0) (hf1 : f 1 = 0) (hg0 : g 0 = 0) (hg1 : g 1 = 0) :
    (∫ x in (0 : ℝ)..1, f x * iteratedDerivWithin 2 g (Icc (0 : ℝ) 1) x) =
      ∫ x in (0 : ℝ)..1, g x * iteratedDerivWithin 2 f (Icc (0 : ℝ) 1) x := by
  let D : (ℝ → ℝ) → ℕ → ℝ → ℝ := fun h m => iteratedDerivWithin m h (Icc (0 : ℝ) 1)
  have hc {h : ℝ → ℝ} (hh : ContDiffOn ℝ ⊤ h (Icc (0 : ℝ) 1)) (m : ℕ) :
      ContinuousOn (D h m) (Icc (0 : ℝ) 1) :=
    hh.continuousOn_iteratedDerivWithin (by simp)
      (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1))
  have hi {h : ℝ → ℝ} (hh : ContDiffOn ℝ ⊤ h (Icc (0 : ℝ) 1)) (m : ℕ) :
      IntervalIntegrable (D h m) volume 0 1 :=
    (hc hh m).intervalIntegrable_of_Icc (by norm_num)
  have hd {h : ℝ → ℝ} (hh : ContDiffOn ℝ ⊤ h (Icc (0 : ℝ) 1))
      (m : ℕ) (x : ℝ) (hx : x ∈ uIcc (0 : ℝ) 1) :
      HasDerivWithinAt (D h m) (D h (m + 1) x) (uIcc (0 : ℝ) 1) x := by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx ⊢
    have h := (hh.differentiableOn_iteratedDerivWithin (m := m) (by simp)
      (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1)) x hx).hasDerivWithinAt
    simpa only [D, iteratedDerivWithin_succ] using h
  have h1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    (a := (0 : ℝ)) (b := 1) (hd hf 0) (hd hg 1) (hi hf 1) (hi hg 2)
  have h2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    (a := (0 : ℝ)) (b := 1) (hd hg 0) (hd hf 1) (hi hg 1) (hi hf 2)
  simp only [D, iteratedDerivWithin_zero, hf0, hf1, hg0, hg1, zero_mul, sub_zero, zero_sub] at h1 h2
  rw [h1, h2]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  ring

end
end CGLMPBounds.Partition
