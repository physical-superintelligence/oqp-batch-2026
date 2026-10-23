module

public import ThreeCopyQutritWerner.SharpQutritDiagonalSupport

@[expose] public section


/-!
# Actual coordinate support for one exterior coefficient

At sharp saturation the square of the original encoded matrix acts on every
column of Y by the coefficient square sum. A single nonzero coefficient then
excludes its missing qutrit coordinate on both physical row registers.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

/-- The actual extremizer lies in the largest squared-eigenvalue space,
expressed as a matrix equation in the original physical coordinates. -/
theorem sharpQutritDiagonal_saturation_square_action
    (d : Fin 3 → ℝ) (hd : ∀ i, 0 ≤ d i)
    (Y : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) (hY : Y.rank ≤ 2)
    (hQ : sharpDoubleAnti Y = sharpQutritAntiEncode (Matrix.diagonal (fun i => (d i : ℂ))))
    (hs : frobSq (sharpDoubleAnti Y) = frobSq Y / 2) (hpos : 0 < frobSq Y) :
    sharpQutritAntiEncode (Matrix.diagonal (fun i => (d i : ℂ))) *
      (sharpQutritAntiEncode (Matrix.diagonal (fun i => (d i : ℂ))) * Y) =
        ((∑ i, d i ^ 2 : ℝ) : ℂ) • Y := by
  let V := sharpQutritDiagonalFrame d
  let W := Matrix.diagonal (fun j => (sharpQutritDiagonalWeight d j : ℂ))
  let A := Vᴴ * Y
  let S : ℝ := ∑ i, d i ^ 2
  have hm := sharpQutritDiagonal_saturation_middle_zero d hd Y hY hQ hs hpos
  have hw := sharpQutritDiagonalWeight_sq_le_sum_of_middle_zero d hm
  have he : W * (W * A) = (S : ℂ) • A := by
    ext j p
    simp only [W, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]
    by_cases hj : sharpQutritDiagonalWeight d j ^ 2 < S
    · have hz : A j p = 0 :=
        sharpQutritDiagonal_saturation_submax_row_zero d hd Y hY hQ hs hpos j hj p
      rw [hz]
      simp
    · have hjr : sharpQutritDiagonalWeight d j ^ 2 = S :=
        le_antisymm (hw j) (le_of_not_gt hj)
      have hjc : (sharpQutritDiagonalWeight d j : ℂ) ^ 2 = (S : ℂ) := by
        exact_mod_cast hjr
      calc
        _ = (sharpQutritDiagonalWeight d j : ℂ) ^ 2 * A j p := by ring
        _ = _ := by rw [hjc]
  have hV : Vᴴ * V = 1 := sharpQutritDiagonalFrame_gram d
  have hcomp : V * Vᴴ = 1 := sharpQutritDiagonalFrame_complete d
  calc
    _ = (V * W * Vᴴ) * ((V * W * Vᴴ) * Y) := by
      rw [sharpQutritDiagonalFrame_factorization]
    _ = V * (W * ((Vᴴ * V) * (W * A))) := by
      simp only [A, Matrix.mul_assoc]
    _ = V * (W * (W * A)) := by rw [hV, Matrix.one_mul]
    _ = V * ((S : ℂ) • A) := by rw [he]
    _ = (S : ℂ) • Y := by
      rw [Matrix.mul_smul]
      simp only [A, ← Matrix.mul_assoc, hcomp, Matrix.one_mul]

/-- A single diagonal exterior coefficient has zero physical rows on its
missing coordinate, directly in the literal exterior encoding. -/
theorem sharpQutritAntiEncode_single_rows_zero
    (d : Fin 3 → ℝ) (a : Fin 3) (hd : ∀ b, b ≠ a → d b = 0)
    (i j : Fin 3) (p : Fin 3 × Fin 3) (hij : i = a ∨ j = a) :
    sharpQutritAntiEncode (Matrix.diagonal (fun b => (d b : ℂ))) (i, j) p = 0 := by
  have ha : ∀ k, sharpQutritWedgeBasis a a k = 0 := by
    intro k
    fin_cases a <;> fin_cases k <;> norm_num [sharpQutritWedgeBasis]
  unfold sharpQutritAntiEncode
  apply Finset.sum_eq_zero
  intro b _
  apply Finset.sum_eq_zero
  intro c _
  by_cases hbc : b = c
  · subst c
    rw [Matrix.diagonal_apply_eq]
    by_cases hba : b = a
    · subst b
      rcases hij with rfl | rfl <;> simp [ha]
    · rw [hd b hba, Complex.ofReal_zero, mul_zero, zero_mul]
  · rw [Matrix.diagonal_apply_ne _ hbc, mul_zero, zero_mul]

/-- The support of the actual sharp extremizer omits the missing coordinate
on both local row registers. No spectral-support assumption is supplied. -/
theorem sharpQutritDiagonal_saturation_single_rows_zero
    (d : Fin 3 → ℝ) (hd : ∀ i, 0 ≤ d i)
    (Y : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) (hY : Y.rank ≤ 2)
    (hQ : sharpDoubleAnti Y = sharpQutritAntiEncode (Matrix.diagonal (fun i => (d i : ℂ))))
    (hs : frobSq (sharpDoubleAnti Y) = frobSq Y / 2) (hpos : 0 < frobSq Y)
    (a : Fin 3) (ha : ∀ b, b ≠ a → d b = 0)
    (i j : Fin 3) (p : Fin 3 × Fin 3) (hij : i = a ∨ j = a) : Y (i, j) p = 0 := by
  let Z := sharpQutritAntiEncode (Matrix.diagonal (fun b => (d b : ℂ)))
  have he := sharpQutritDiagonal_saturation_square_action d hd Y hY hQ hs hpos
  have hr : (Z * (Z * Y)) (i, j) p = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro q _
    rw [show Z (i, j) q = 0 from sharpQutritAntiEncode_single_rows_zero d a ha i j q hij,
      zero_mul]
  have hS : 0 < ∑ b, d b ^ 2 := by
    have hZ : frobSq Z = 4 * ∑ b, d b ^ 2 := by
      change frobSq (sharpQutritAntiEncode (Matrix.diagonal (fun b => (d b : ℂ)))) = _
      rw [sharpQutritAntiEncode_frobSq]
      simp [frobSq, Matrix.diagonal_apply, apply_ite, Complex.normSq_ofReal, pow_two]
    rw [hQ] at hs
    change frobSq Z = frobSq Y / 2 at hs
    linarith
  have hc : ((∑ b, d b ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hS)
  have heij := congrFun (congrFun he (i, j)) p
  change (Z * (Z * Y)) (i, j) p = ((∑ b, d b ^ 2 : ℝ) : ℂ) * Y (i, j) p at heij
  rw [hr] at heij
  exact (mul_eq_zero.mp heij.symm).resolve_left hc

end ThreeCopyQutritWerner
