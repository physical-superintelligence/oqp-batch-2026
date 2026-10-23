module

public import CGLMPBounds.Hardy.PositivePinchingAlgebra
public import CGLMPBounds.Hardy.DiagonalTwoNodeExpansion
public import CGLMPBounds.Hardy.TwoNodeResidue

@[expose] public section


/-! The two genuine spectral nodes of a shifted diagonal involution and the
actual small circle selecting its positive node. -/

open Complex Metric Set Matrix
namespace CGLMPBounds.Hardy
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem involutionFromSigns_isHermitian (σ : ι → Bool) :
    (involutionFromSigns σ).IsHermitian := by
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  cases h : σ i <;> simp [h, isSelfAdjoint_iff]

theorem involutionFromSigns_sq (σ : ι → Bool) : (involutionFromSigns σ) ^ 2 = 1 := by
  rw [pow_two, involutionFromSigns, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    cases h : σ i <;> simp [h, Matrix.diagonal_apply, Matrix.one_apply]
  · simp [Matrix.diagonal_apply, Matrix.one_apply, hij]

theorem involutionFromSigns_shift_inverse (σ : ι → Bool) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    (involutionFromSigns σ - (x : ℂ) • (1 : Matrix ι ι ℂ))⁻¹ =
      Matrix.diagonal (fun i => if σ i then (((1 - x)⁻¹ : ℝ) : ℂ)
        else ((-(1 + x)⁻¹ : ℝ) : ℂ)) := by
  have hshift : involutionFromSigns σ - (x : ℂ) • (1 : Matrix ι ι ℂ) =
      Matrix.diagonal (fun i => (if σ i then (1 : ℂ) else -1) - (x : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [involutionFromSigns, Matrix.diagonal_apply, Matrix.one_apply]
    · simp [involutionFromSigns, Matrix.diagonal_apply, Matrix.one_apply, hij]
  have hA : 1 - (x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (sub_pos.mpr hx.2)
  have hB : 1 + (x : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (show (0 : ℝ) < 1 + x by linarith [hx.1]))
  have hd : ∀ i, (if σ i then (1 : ℂ) else -1) - (x : ℂ) ≠ 0 := by
    intro i
    cases h : σ i
    · simp only [h, Bool.false_eq_true, ↓reduceIte]
      intro he
      apply hB
      linear_combination -he
    · simpa only [h, ↓reduceIte] using hA
  rw [hshift, diagonal_inverse_of_ne_zero _ hd]
  congr 1
  funext i
  cases h : σ i
  · simp only [h, Bool.false_eq_true, ↓reduceIte, Complex.ofReal_neg,
      Complex.ofReal_inv, Complex.ofReal_add, Complex.ofReal_one]
    have he : -(1 : ℂ) - x = -(1 + (x : ℂ)) := by ring
    rw [he, inv_neg]
  · simp only [h, ↓reduceIte, Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one]

theorem two_node_diagonal_circle_selects_positive (σ : ι → Bool)
    {a b : ℝ} (ha : 0 < a) (hb : b < 0) {z : ℂ}
    (hz : z ∈ (Matrix.diagonal (fun i => if σ i then (a : ℂ) else (b : ℂ))).charpoly.roots) :
    z ∉ sphere (a : ℂ) (|a - b| / 2) ∧
      (z ∈ ball (a : ℂ) (|a - b| / 2) ↔ 0 < z.re) := by
  have hab : a ≠ b := by linarith
  have hR := twoNode_radius_pos hab
  have hs := Matrix.mem_spectrum_of_isRoot_charpoly (Polynomial.isRoot_of_mem_roots hz)
  rw [spectrum_diagonal] at hs
  obtain ⟨i, rfl⟩ := hs
  cases hi : σ i
  · simp only [hi, Bool.false_eq_true, ↓reduceIte, Complex.ofReal_re]
    have hd : dist (b : ℂ) (a : ℂ) = |a - b| := by
      simpa only [Real.dist_eq, abs_sub_comm] using Complex.isometry_ofReal.dist_eq b a
    constructor
    · intro h
      have he := Metric.mem_sphere.mp h
      rw [hd] at he
      linarith
    · constructor
      · intro h
        have he := Metric.mem_ball.mp h
        rw [hd] at he
        linarith
      · intro h
        linarith
  · simp only [hi, ↓reduceIte, Complex.ofReal_re]
    constructor
    · simpa only [Metric.mem_sphere, dist_self] using (ne_of_gt hR).symm
    · simp only [Metric.mem_ball, dist_self, hR, ha]

end
end CGLMPBounds.Hardy
