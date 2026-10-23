module

public import CGLMPBounds.Hardy.DiagonalTwoNodeMoments
public import CGLMPBounds.Hardy.PositivePinchingTwoNode

@[expose] public section


/-! The literal C.13 formula in a basis where B is diagonal with entries ±1.
It follows from actual C.7 moments, actual ordered resolvent trace expansion,
and the genuine C.9 contour residues, including zero contributions from the
unmixed cycles. No cycle identity is a hypothesis of the final endpoint. -/

namespace CGLMPBounds.Hardy
noncomputable section
open MeasureTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma inverse_involution_residue_for_count (m p : ℕ) (hp : p ≤ m + 2)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    twoNodeResidue p (m + 2 - p) ((1 - x)⁻¹) (-(1 + x)⁻¹) /
      (1 - (x : ℂ) ^ 2) =
    if 1 ≤ p ∧ p < m + 2 then
      (m.choose (p - 1) : ℂ) * (1 - (x : ℂ)) ^ (p - 1) *
        (1 + (x : ℂ)) ^ (m + 2 - p - 1) / (2 : ℂ) ^ (m + 1)
    else 0 := by
  have ha : 0 < (1 - x)⁻¹ := inv_pos.mpr (sub_pos.mpr hx.2)
  have hb : -(1 + x)⁻¹ < 0 :=
    neg_lt_zero.mpr (inv_pos.mpr (show 0 < 1 + x by linarith [hx.1]))
  have hab : (1 - x)⁻¹ ≠ -(1 + x)⁻¹ := by linarith
  by_cases hp0 : p = 0
  · subst p
    rw [twoNodeResidue_zero_left _ hab]
    simp
  by_cases hpall : p = m + 2
  · subst p
    rw [Nat.sub_self, twoNodeResidue_zero_right _ (by omega) hab]
    simp
  have hmixed : 1 ≤ p ∧ p < m + 2 := by omega
  rw [if_pos hmixed]
  exact twoNodeResidue_inverse_involution_nodes m p (m + 2 - p)
    hmixed.1 (by omega) (by omega) hx

theorem positivePinching_diagonal_cycle_moment [Nonempty ι]
    (σ : ι → Bool) {Y : Matrix ι ι ℂ} (hY : Y.IsHermitian)
    (m : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ((∫ y : ℝ, y ^ m * positivePinchingDensity (involutionFromSigns σ) Y (x, y) : ℝ) : ℂ) =
      pinchingCycleMoment σ Y m x := by
  let a : ℝ := (1 - x)⁻¹
  let b : ℝ := -(1 + x)⁻¹
  let H : Matrix ι ι ℂ := Matrix.diagonal (fun i => if σ i then (a : ℂ) else (b : ℂ))
  let p := fun v : Fin (m + 2) → ι => cyclePositiveCount σ v
  let w := fun v : Fin (m + 2) → ι => matrixIndexCycleWeight Y (m + 1) v
  let T := fun v : Fin (m + 2) → ι =>
    if 1 ≤ p v ∧ p v < m + 2 then
      (m.choose (p v - 1) : ℂ) * (1 - (x : ℂ)) ^ (p v - 1) *
        (1 + (x : ℂ)) ^ (m + 2 - p v - 1) * w v
    else 0
  have hfun : (fun y : ℝ => y ^ m * positivePinchingDensity (involutionFromSigns σ) Y (x, y)) =
      (fun y : ℝ => (y ^ m * traceDensity H Y y) / (1 - x ^ 2)) := by
    funext y
    simp only [positivePinchingDensity, hx, if_pos]
    rw [positivePinching_omega_eq_traceDensity (involutionFromSigns_sq σ) hx,
      involutionFromSigns_shift_inverse σ hx]
    change y ^ m * (traceDensity H Y y / (1 - x ^ 2)) = _
    ring
  rw [hfun, integral_div, Complex.ofReal_div]
  have ha : 0 < a := inv_pos.mpr (sub_pos.mpr hx.2)
  have hb : b < 0 := neg_lt_zero.mpr
    (inv_pos.mpr (show (0 : ℝ) < 1 + x by linarith [hx.1]))
  have hm := diagonal_two_node_traceDensity_moment σ hY m ha hb
  change ((∫ y : ℝ, y ^ m * traceDensity H Y y : ℝ) : ℂ) /
    ((1 - x ^ 2 : ℝ) : ℂ) = _
  rw [hm, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow]
  change ((1 / ((Fintype.card ι : ℂ) * ((m + 2 : ℕ) : ℂ))) *
      ∑ v : Fin (m + 2) → ι, w v * twoNodeResidue (p v) (m + 2 - p v) a b) /
      (1 - (x : ℂ) ^ 2) = _
  calc
    _ = (1 / ((Fintype.card ι : ℂ) * ((m + 2 : ℕ) : ℂ))) *
        ∑ v : Fin (m + 2) → ι, w v *
          (twoNodeResidue (p v) (m + 2 - p v) a b / (1 - (x : ℂ) ^ 2)) := by
      simp only [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ = (1 / ((Fintype.card ι : ℂ) * ((m + 2 : ℕ) : ℂ))) *
        ((∑ v : Fin (m + 2) → ι, T v) / (2 : ℂ) ^ (m + 1)) := by
      congr 1
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro v _
      rw [show twoNodeResidue (p v) (m + 2 - p v) a b / (1 - (x : ℂ) ^ 2) =
          if 1 ≤ p v ∧ p v < m + 2 then
            (m.choose (p v - 1) : ℂ) * (1 - (x : ℂ)) ^ (p v - 1) *
              (1 + (x : ℂ)) ^ (m + 2 - p v - 1) / (2 : ℂ) ^ (m + 1)
          else 0 from inverse_involution_residue_for_count m (p v) (cyclePositiveCount_le σ v) hx]
      dsimp only [T]
      by_cases hpv : 1 ≤ p v ∧ p v < m + 2
      · simp only [if_pos hpv]
        ring
      · simp only [if_neg hpv]
        ring
    _ = pinchingCycleMoment σ Y m x := by
      change (1 / ((Fintype.card ι : ℂ) * ((m + 2 : ℕ) : ℂ))) *
        ((∑ v : Fin (m + 2) → ι, T v) / (2 : ℂ) ^ (m + 1)) =
        (1 / ((Fintype.card ι : ℂ) * ((m + 2 : ℕ) : ℂ) * 2 ^ (m + 1))) *
          ∑ v : Fin (m + 2) → ι, T v
      simp only [div_mul_eq_div_div]
      ring

end
end CGLMPBounds.Hardy
