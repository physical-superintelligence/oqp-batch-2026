module

public import CGLMPBounds.Hardy.SchwarzPositiveCluster

@[expose] public section


/-! Explicit disk geometry for the holomorphic inversion in C.7. For a real
center c and radius r with c²>r², the image circle has center c/(c²-r²)
and radius r/(c²-r²). This is an interior-to-interior map: inversion preserves
positive boundary orientation here because the original disk excludes zero.
The differential, rather than orientation reversal, supplies the minus sign. -/

open Complex Metric Set

namespace CGLMPBounds.Hardy
noncomputable section

lemma inverse_disk_squared_equation {c r : ℝ} {z : ℂ}
    (hΔ : c ^ 2 - r ^ 2 ≠ 0) (hz : z ≠ 0) :
    ‖z‖ ^ 2 * (dist z⁻¹ (c : ℂ) ^ 2 - r ^ 2) =
      (c ^ 2 - r ^ 2) *
        (dist z ((c / (c ^ 2 - r ^ 2) : ℝ) : ℂ) ^ 2 -
          (r / (c ^ 2 - r ^ 2)) ^ 2) := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  rw [dist_sq_positive_real_center, dist_sq_positive_real_center,
    norm_inv, inv_pow, Complex.inv_re, ← Complex.sq_norm]
  field_simp [hn, hΔ]
  <;> ring

lemma inverse_mem_real_ball_iff {c r : ℝ} {z : ℂ}
    (hr : 0 ≤ r) (hΔ : 0 < c ^ 2 - r ^ 2) (hz : z ≠ 0) :
    z⁻¹ ∈ ball (c : ℂ) r ↔
      z ∈ ball ((c / (c ^ 2 - r ^ 2) : ℝ) : ℂ) (r / (c ^ 2 - r ^ 2)) := by
  have hn : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
  have hs : 0 ≤ r / (c ^ 2 - r ^ 2) := div_nonneg hr hΔ.le
  have he := inverse_disk_squared_equation hΔ.ne' hz
  rw [Metric.mem_ball, Metric.mem_ball,
    ← sq_lt_sq₀ dist_nonneg hr, ← sq_lt_sq₀ dist_nonneg hs,
    ← sub_neg]
  calc
    _ ↔ ‖z‖ ^ 2 * (dist z⁻¹ (c : ℂ) ^ 2 - r ^ 2) < ‖z‖ ^ 2 * 0 :=
      (mul_lt_mul_iff_of_pos_left hn).symm
    _ ↔ (c ^ 2 - r ^ 2) *
        (dist z ((c / (c ^ 2 - r ^ 2) : ℝ) : ℂ) ^ 2 -
          (r / (c ^ 2 - r ^ 2)) ^ 2) < (c ^ 2 - r ^ 2) * 0 := by
      rw [he, mul_zero, mul_zero]
    _ ↔ _ := (mul_lt_mul_iff_of_pos_left hΔ).trans sub_neg

lemma inverse_mem_real_closedBall_iff {c r : ℝ} {z : ℂ}
    (hr : 0 ≤ r) (hΔ : 0 < c ^ 2 - r ^ 2) (hz : z ≠ 0) :
    z⁻¹ ∈ closedBall (c : ℂ) r ↔
      z ∈ closedBall ((c / (c ^ 2 - r ^ 2) : ℝ) : ℂ) (r / (c ^ 2 - r ^ 2)) := by
  have hn : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
  have hs : 0 ≤ r / (c ^ 2 - r ^ 2) := div_nonneg hr hΔ.le
  have he := inverse_disk_squared_equation hΔ.ne' hz
  rw [Metric.mem_closedBall, Metric.mem_closedBall,
    ← sq_le_sq₀ dist_nonneg hr, ← sq_le_sq₀ dist_nonneg hs,
    ← sub_nonpos]
  calc
    _ ↔ ‖z‖ ^ 2 * (dist z⁻¹ (c : ℂ) ^ 2 - r ^ 2) ≤ ‖z‖ ^ 2 * 0 :=
      (mul_le_mul_iff_of_pos_left hn).symm
    _ ↔ (c ^ 2 - r ^ 2) *
        (dist z ((c / (c ^ 2 - r ^ 2) : ℝ) : ℂ) ^ 2 -
          (r / (c ^ 2 - r ^ 2)) ^ 2) ≤ (c ^ 2 - r ^ 2) * 0 := by
      rw [he, mul_zero, mul_zero]
    _ ↔ _ := (mul_le_mul_iff_of_pos_left hΔ).trans sub_nonpos

lemma inverse_mem_real_sphere_iff {c r : ℝ} {z : ℂ}
    (hr : 0 ≤ r) (hΔ : 0 < c ^ 2 - r ^ 2) (hz : z ≠ 0) :
    z⁻¹ ∈ sphere (c : ℂ) r ↔
      z ∈ sphere ((c / (c ^ 2 - r ^ 2) : ℝ) : ℂ) (r / (c ^ 2 - r ^ 2)) := by
  rw [← Metric.closedBall_sdiff_ball, ← Metric.closedBall_sdiff_ball]
  simp only [Set.mem_diff, inverse_mem_real_ball_iff hr hΔ hz,
    inverse_mem_real_closedBall_iff hr hΔ hz]

lemma zero_not_mem_inverse_real_disk {c r : ℝ}
    (hr : 0 ≤ r) (hΔ : 0 < c ^ 2 - r ^ 2) :
    (0 : ℂ) ∉ closedBall ((c / (c ^ 2 - r ^ 2) : ℝ) : ℂ)
      (r / (c ^ 2 - r ^ 2)) := by
  have hc : r < |c| := (sq_lt_sq₀ hr (abs_nonneg c)).mp (by nlinarith [sq_abs c])
  intro hzero
  have hle : |c| / (c ^ 2 - r ^ 2) ≤ r / (c ^ 2 - r ^ 2) := by
    simpa only [Metric.mem_closedBall, dist_zero_left, Complex.norm_real,
      Real.norm_eq_abs, abs_div, abs_of_pos hΔ] using hzero
  exact (not_le_of_gt hc) ((div_le_div_iff_of_pos_right hΔ).mp hle)

end
end CGLMPBounds.Hardy
