module

public import CGLMPBounds.Partition.AbelPairCoefficient
public import CGLMPBounds.Partition.ConsecutiveFourierCoefficient
public import CGLMPBounds.Partition.MatrixPairExpansion

@[expose] public section


/-! Finite matrix pairing and honest geometric sum/integral interchange
for the D.2 Abel regularization. All cell coefficients are explicit
interval integrals. -/

namespace CGLMPBounds.Partition
open Set MeasureTheory
open scoped Matrix
noncomputable section

theorem consecutivePartition_damped_pair_hasSum {d r : ℕ} (hr : 0 < r)
    (ℓ : ConsecutivePartition d) (V : Fin d → Circulation.Mat r)
    (hV : ∀ j, (V j)ᴴ * V j = 1) (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    let a : ℕ → Fin d → ℂ := fun n j =>
      ∫ t in (ℓ.boundary j.castSucc)..(ℓ.boundary j.succ),
        Complex.exp (((( (2 * Real.pi * (n : ℝ) + 3 * Real.pi / 2) * t : ℝ) : ℂ)) * Complex.I)
    let K : Fin d → Fin d → ℂ := fun j k =>
      ∫ p : ℝ × ℝ, quarterBranchAbelKernel q (p.2 - p.1)
        ∂((volume.restrict (Ioo (ℓ.boundary j.castSucc) (ℓ.boundary j.succ))).prod
          (volume.restrict (Ioo (ℓ.boundary k.castSucc) (ℓ.boundary k.succ))))
    HasSum (fun n : ℕ =>
      (Circulation.hsSq (∑ j, a n j • (V j)ᴴ) - ‖∑ j, a n j‖ ^ 2) * q ^ n)
      (2 * ∑ j : Fin d, ∑ k : Fin d, if j < k then
        (K j k * (star (Circulation.corr (V j) (V k)) - 1)).re else 0) := by
  dsimp only
  let a : ℕ → Fin d → ℂ := fun n j =>
    ∫ t in (ℓ.boundary j.castSucc)..(ℓ.boundary j.succ),
      Complex.exp (((( (2 * Real.pi * (n : ℝ) + 3 * Real.pi / 2) * t : ℝ) : ℂ)) * Complex.I)
  let K : Fin d → Fin d → ℂ := fun j k =>
    ∫ p : ℝ × ℝ, quarterBranchAbelKernel q (p.2 - p.1)
      ∂((volume.restrict (Ioo (ℓ.boundary j.castSucc) (ℓ.boundary j.succ))).prod
        (volume.restrict (Ioo (ℓ.boundary k.castSucc) (ℓ.boundary k.succ))))
  have hb (j : Fin d) : ℓ.boundary j.castSucc ≤ ℓ.boundary j.succ :=
    ℓ.monotone_boundary (by exact_mod_cast (show j.val ≤ j.val + 1 by omega))
  have hpair (j k : Fin d) :
      HasSum (fun n : ℕ => (q : ℂ) ^ n * (star (a n j) * a n k)) (K j k) :=
    quarterBranchAbelKernel_coefficient_series_hasSum (hb j) (hb k) q hq₀ hq₁
  have hrpair (j k : Fin d) :
      HasSum (fun n : ℕ =>
        (star (a n j) * a n k * (star (Circulation.corr (V j) (V k)) - 1)).re * q ^ n)
        (K j k * (star (Circulation.corr (V j) (V k)) - 1)).re := by
    have h := Complex.hasSum_re
      ((hpair j k).mul_right (star (Circulation.corr (V j) (V k)) - 1))
    apply h.congr_fun
    intro n
    rw [← Complex.ofReal_pow]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hcond (j k : Fin d) : HasSum (fun n : ℕ =>
      if j < k then
        (star (a n j) * a n k * (star (Circulation.corr (V j) (V k)) - 1)).re * q ^ n
      else 0)
      (if j < k then (K j k * (star (Circulation.corr (V j) (V k)) - 1)).re else 0) := by
    by_cases hjk : j < k
    · simpa only [if_pos hjk] using hrpair j k
    · simp only [if_neg hjk]
      exact hasSum_zero
  have hsum := (hasSum_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin d))) =>
    hasSum_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin d))) => hcond j k))).mul_left 2
  apply hsum.congr_fun
  intro n
  rw [hsSq_weighted_unitary_daggers_sub_scalar hr (a n) V hV]
  simp only [Finset.sum_mul, ite_mul, zero_mul, mul_assoc]

end
end CGLMPBounds.Partition
