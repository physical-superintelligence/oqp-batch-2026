module

public import ThreeCopyQutritWerner.BinaryPartitionNormalize

@[expose] public section


/-!
# Exact half-norm rank-one normalization

The fixed coefficient 1/sqrt(2) has no residual complex phase: the phase of
the original rank-one matrix is absorbed into its first unit vector.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

theorem binaryPartition_rank_one_half_norm
    {n : Type*} [Fintype n] (T : Matrix n n ℂ)
    (hT : T.rank ≤ 1) (hN : frobSq T = 1 / 2) :
    ∃ x y : n → ℂ, vecNormSq x = 1 ∧ vecNormSq y = 1 ∧
      T = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • ketBra x y := by
  obtain ⟨u, v, huv⟩ := exists_eq_ketBra_of_rank_le_one T hT
  have hu : ∃ i, u i ≠ 0 := by
    by_contra hn
    push_neg at hn
    simp [huv, frobSq, ketBra, hn] at hN
  have hv : ∃ i, v i ≠ 0 := by
    by_contra hn
    push_neg at hn
    simp [huv, frobSq, ketBra, hn] at hN
  obtain ⟨x, α, hx, hux⟩ := TwoPlane.exists_unit_factor u hu
  obtain ⟨y, β, hy, hvy⟩ := TwoPlane.exists_unit_factor v hv
  let z : ℂ := α * conj β
  have he : T = z • ketBra x y := by
    rw [huv]
    ext i j
    simp only [ketBra, hux, hvy, map_mul, Matrix.smul_apply, smul_eq_mul]
    dsimp [z]
    ring
  have hz : Complex.normSq z = 1 / 2 := by
    rw [he, frobSq_smul, frobSq_ketBra_vecNormSq, hx, hy, one_mul, mul_one] at hN
    exact hN
  let w : ℂ := (Real.sqrt 2 : ℂ) * z
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsne : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)))
  have hw : Complex.normSq w = 1 := by
    dsimp [w]
    rw [Complex.normSq_mul, Complex.normSq_ofReal, hs, hz]
    norm_num
  have hwz : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * w = z := by
    dsimp [w]
    rw [Complex.ofReal_inv, ← mul_assoc, inv_mul_cancel₀ hsne, one_mul]
  refine ⟨(fun i => w * x i), y, ?_, hy, ?_⟩
  · calc
      vecNormSq (fun i => w * x i) = Complex.normSq w * vecNormSq x := by
        simp only [vecNormSq, Complex.normSq_mul, Finset.mul_sum]
      _ = 1 := by rw [hw, hx, one_mul]
  · rw [he]
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, ketBra]
    calc
      z * (x i * conj (y j)) =
          ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * w) * (x i * conj (y j)) := by rw [hwz]
      _ = _ := by ring

end ThreeCopyQutritWerner
