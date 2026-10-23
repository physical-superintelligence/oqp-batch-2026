module

public import CGLMPBounds.Hardy.SchwarzMomentSeparatingCircle
public import CGLMPBounds.Hardy.PositivePinchingDiagonal
public import CGLMPBounds.Hardy.TwoNodeBoundaryCases

@[expose] public section


/-! The actual trace-density moment of a two-node Hermitian diagonal matrix
is the finite ordered-cycle sum of actual contour residues. Circle integrability
is proved for every summand before applying integral linearity. -/

open Complex Metric Set Matrix
namespace CGLMPBounds.Hardy
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem diagonal_two_node_contour_eq_cycle_residues (σ : ι → Bool)
    (Y : Matrix ι ι ℂ) (m : ℕ) {a b : ℝ} (hab : a ≠ b) :
    (∮ z in C((a : ℂ), |a - b| / 2), z ^ m * Matrix.trace ((resolvent
      (Matrix.diagonal (fun i => if σ i then (a : ℂ) else (b : ℂ))) z * Y) ^ (m + 2))) /
        (2 * Real.pi * Complex.I : ℂ) =
      ∑ v : Fin (m + 2) → ι, matrixIndexCycleWeight Y (m + 1) v *
        twoNodeResidue (cyclePositiveCount σ v) (m + 2 - cyclePositiveCount σ v) a b := by
  let p := fun v : Fin (m + 2) → ι => cyclePositiveCount σ v
  let q := fun v : Fin (m + 2) → ι => m + 2 - p v
  let w := fun v : Fin (m + 2) → ι => matrixIndexCycleWeight Y (m + 1) v
  let F := fun (v : Fin (m + 2) → ι) (z : ℂ) =>
    w v * (z ^ m / ((z - (a : ℂ)) ^ p v * (z - (b : ℂ)) ^ q v))
  have hdeg (v : Fin (m + 2) → ι) : p v + q v - 2 = m := by
    have hp := cyclePositiveCount_le σ v
    dsimp [p, q]
    omega
  have hi (v : Fin (m + 2) → ι) : CircleIntegrable (F v) (a : ℂ) (|a - b| / 2) := by
    have h := (twoNode_rational_circleIntegrable (p v) (q v) hab).continuousOn_mul
      (g := fun _ => w v) continuousOn_const
    simpa only [F, Pi.mul_apply, hdeg v] using! h
  have heq : (∮ z in C((a : ℂ), |a - b| / 2), z ^ m * Matrix.trace ((resolvent
      (Matrix.diagonal (fun i => if σ i then (a : ℂ) else (b : ℂ))) z * Y) ^ (m + 2))) =
      ∮ z in C((a : ℂ), |a - b| / 2), ∑ v : Fin (m + 2) → ι, F v z := by
    apply circleIntegral.integral_congr (twoNode_radius_pos hab).le
    intro z hz
    have hza : z ≠ (a : ℂ) := by
      intro he
      subst z
      have hd := Metric.mem_sphere.mp hz
      simp only [dist_self] at hd
      exact (ne_of_gt (twoNode_radius_pos hab)) hd.symm
    have hzb := twoNode_closedBall_ne_right hab (sphere_subset_closedBall hz)
    dsimp only
    rw [diagonal_two_node_weighted_resolvent_trace σ Y m (a : ℂ) (b : ℂ) hza hzb]
    apply Finset.sum_congr rfl
    intro v _
    dsimp [F, p, q, w]
    ring
  rw [heq, circleIntegral.integral_fun_sum (fun v _ => hi v), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro v _
  rw [show F v = fun z : ℂ => w v *
      (z ^ m / ((z - (a : ℂ)) ^ p v * (z - (b : ℂ)) ^ q v)) from rfl,
    circleIntegral.integral_const_mul]
  change _ = w v * twoNodeResidue (p v) (q v) a b
  unfold twoNodeResidue
  rw [hdeg v]
  ring

theorem diagonal_two_node_traceDensity_moment (σ : ι → Bool)
    {Y : Matrix ι ι ℂ} (hY : Y.IsHermitian) (m : ℕ)
    {a b : ℝ} (ha : 0 < a) (hb : b < 0) :
    ((∫ y : ℝ, y ^ m * traceDensity
      (Matrix.diagonal (fun i => if σ i then (a : ℂ) else (b : ℂ))) Y y : ℝ) : ℂ) =
      (1 / ((Fintype.card ι : ℂ) * ((m + 2 : ℕ) : ℂ))) *
        ∑ v : Fin (m + 2) → ι, matrixIndexCycleWeight Y (m + 1) v *
          twoNodeResidue (cyclePositiveCount σ v) (m + 2 - cyclePositiveCount σ v) a b := by
  let H : Matrix ι ι ℂ := Matrix.diagonal (fun i => if σ i then (a : ℂ) else (b : ℂ))
  have hH : H.IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro i
    cases hi : σ i <;> simp [hi, isSelfAdjoint_iff]
  have hd : ∀ i, (if σ i then (a : ℂ) else (b : ℂ)) ≠ 0 := by
    intro i
    have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne
    cases hi : σ i <;> simp [hi, ha0, hb0]
  have hdet : IsUnit H.det := by
    apply Matrix.isUnit_det_of_left_inverse
      (B := Matrix.diagonal (fun i => (if σ i then (a : ℂ) else (b : ℂ))⁻¹))
    dsimp only [H]
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      change (if σ i then (a : ℂ) else (b : ℂ))⁻¹ *
        (if σ i then (a : ℂ) else (b : ℂ)) = 1
      exact inv_mul_cancel₀ (hd i)
    · simp [Matrix.diagonal_apply, Matrix.one_apply, hij]
  have hab : a ≠ b := by linarith
  have hc := traceDensity_moment_eq_separating_circle hH hY hdet m
    (twoNode_radius_pos hab).le
    (fun z hz => (two_node_diagonal_circle_selects_positive σ ha hb hz).1)
    (fun z hz => (two_node_diagonal_circle_selects_positive σ ha hb hz).2)
  change ((∫ y : ℝ, y ^ m * traceDensity H Y y : ℝ) : ℂ) = _
  rw [hc]
  calc
    _ = (1 / ((m + 2 : ℕ) : ℂ)) *
        ((∮ z in C((a : ℂ), |a - b| / 2),
          z ^ m * Matrix.trace ((resolvent H z * Y) ^ (m + 2))) /
          (2 * Real.pi * Complex.I : ℂ)) / (Fintype.card ι : ℂ) := by ring
    _ = _ := by
      rw [show H = Matrix.diagonal (fun i => if σ i then (a : ℂ) else (b : ℂ)) from rfl,
        diagonal_two_node_contour_eq_cycle_residues σ Y m hab]
      ring

end
end CGLMPBounds.Hardy
