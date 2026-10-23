module

public import ThreeCopyQutritWerner.SharpQutritDiagonalRows
public import ThreeCopyQutritWerner.RankTwoSpectralSupport

@[expose] public section


/-!
# Physical row support from actual qutrit sharp saturation

The actual middle central eigenvalue vanishes at saturation. Its trace and
square sum then put every full-basis squared weight below the original
coefficient square sum. Strictly smaller external weights annihilate actual
physical off-diagonal rows, through the two literal normalized pair vectors.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

/-- Actual sharp saturation forces the actual ordered middle eigenvalue to zero. -/
theorem sharpQutritDiagonal_saturation_middle_zero
    (d : Fin 3 → ℝ) (hd : ∀ i, 0 ≤ d i)
    (Y : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) (hY : Y.rank ≤ 2)
    (hQ : sharpDoubleAnti Y = sharpQutritAntiEncode (Matrix.diagonal (fun i => (d i : ℂ))))
    (hs : frobSq (sharpDoubleAnti Y) = frobSq Y / 2) (hpos : 0 < frobSq Y) :
    sharpQutritCentralOrdered d 1 = 0 := by
  let Z := sharpQutritAntiEncode (Matrix.diagonal (fun i => (d i : ℂ)))
  have hfix : sharpDoubleAnti Z = Z := sharpQutritAntiEncode_fixed _
  have ht : (Zᴴ * Y).trace = (frobSq Z : ℂ) := by
    rw [← hsInner_eq_trace]
    calc
      hsInner Z Y = hsInner (sharpDoubleAnti Z) Y := by rw [hfix]
      _ = hsInner Z (sharpDoubleAnti Y) := sharpDoubleAnti_selfadjoint Z Y
      _ = hsInner Z Z := by rw [hQ]
      _ = (frobSq Z : ℂ) := (ofReal_frobSq Z).symm
  have hZ : frobSq Z = 4 * ∑ i, d i ^ 2 := by
    change frobSq (sharpQutritAntiEncode (Matrix.diagonal (fun i => (d i : ℂ)))) = _
    rw [sharpQutritAntiEncode_frobSq]
    simp [frobSq, Matrix.diagonal_apply, apply_ite, Complex.normSq_ofReal, pow_two]
  have hov := sharpQutritDiagonal_rank_two_overlap_le d hd Y hY
  change Complex.normSq (Zᴴ * Y).trace ≤ _ at hov
  rw [ht, Complex.normSq_ofReal] at hov
  rw [hQ] at hs
  change frobSq Z = frobSq Y / 2 at hs
  have hbound : frobSq Z / 2 ≤
      2 * (∑ i, d i ^ 2) - sharpQutritCentralOrdered d 1 ^ 2 := by
    apply le_of_mul_le_mul_right (a := frobSq Y) ?_ hpos
    have he : frobSq Z / 2 * frobSq Y = frobSq Z * frobSq Z := by
      rw [show frobSq Y = 2 * frobSq Z by linarith]
      ring
    rw [he]
    exact hov
  apply sq_eq_zero_iff.mp
  linarith [sq_nonneg (sharpQutritCentralOrdered d 1)]

/-- With the actual middle weight zero, each of the nine actual squared
weights is at most the original coefficient square sum. -/
theorem sharpQutritDiagonalWeight_sq_le_sum_of_middle_zero
    (d : Fin 3 → ℝ) (hm : sharpQutritCentralOrdered d 1 = 0)
    (j : SharpQutritDiagonalIndex) :
    sharpQutritDiagonalWeight d j ^ 2 ≤ ∑ i, d i ^ 2 := by
  have ht := sharpQutritCentralOrdered_sum d
  have hsq := sharpQutritCentralOrdered_sum_sq d
  simp only [Fin.sum_univ_three, hm, zero_pow (by decide : 2 ≠ 0),
    zero_add, add_zero] at ht hsq
  have he : sharpQutritCentralOrdered d 2 = -sharpQutritCentralOrdered d 0 := by
    linarith
  have h0 : sharpQutritCentralOrdered d 0 ^ 2 = ∑ i, d i ^ 2 := by
    rw [he] at hsq
    simp only [neg_sq] at hsq
    simpa only [Fin.sum_univ_three] using (show sharpQutritCentralOrdered d 0 ^ 2 =
      d 0 ^ 2 + d 1 ^ 2 + d 2 ^ 2 by linarith)
  rcases j with j | ⟨j, s⟩
  · fin_cases j
    · exact h0.le
    · change sharpQutritCentralOrdered d 1 ^ 2 ≤ _
      rw [hm, zero_pow (by decide : 2 ≠ 0)]
      exact Finset.sum_nonneg (fun i _ => sq_nonneg (d i))
    · change sharpQutritCentralOrdered d 2 ^ 2 ≤ _
      rw [he, neg_sq, h0]
  · change sharpQutritExternalWeight d j s ^ 2 ≤ _
    rw [sharpQutritExternalWeight_sq]
    exact Finset.single_le_sum (fun i _ => sq_nonneg (d i)) (Finset.mem_univ j)

/-- Exact normalized external spectral row in the original physical entries. -/
theorem sharpQutritDiagonalFrame_external_row
    (d : Fin 3 → ℝ) (Y : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (a : Fin 3) (s : Fin 2) (p : Fin 3 × Fin 3) :
    ((sharpQutritDiagonalFrame d)ᴴ * Y) (Sum.inr (a, s)) p =
      (Real.sqrt (1 / 2) : ℂ) *
        (Y (sharpQutritWedgeFirst a, sharpQutritWedgeSecond a) p +
          (if s = 0 then 1 else -1) *
            Y (sharpQutritWedgeSecond a, sharpQutritWedgeFirst a) p) := by
  fin_cases a <;> fin_cases s <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, sharpQutritDiagonalFrame,
      sharpQutritDiagonalVector, sharpQutritExternalPair, sharpQutritWedgeFirst,
      sharpQutritWedgeSecond, Fintype.sum_prod_type, Fin.sum_univ_three,
      Pi.smul_apply, smul_eq_mul] <;> ring

/-- The two external signs detect both original off-diagonal coordinates. -/
theorem sharpQutritDiagonalFrame_external_zero_forces_diagonal_rows
    (d : Fin 3 → ℝ) (Y : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (hz : ∀ a s p, ((sharpQutritDiagonalFrame d)ᴴ * Y) (Sum.inr (a, s)) p = 0) :
    ∀ i j p, i ≠ j → Y (i, j) p = 0 := by
  have hn : (Real.sqrt (1 / 2) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 1 / 2)))
  have hp : ∀ a p,
      Y (sharpQutritWedgeFirst a, sharpQutritWedgeSecond a) p = 0 ∧
      Y (sharpQutritWedgeSecond a, sharpQutritWedgeFirst a) p = 0 := by
    intro a p
    have h0 := hz a 0 p
    have h1 := hz a 1 p
    rw [sharpQutritDiagonalFrame_external_row] at h0 h1
    simp only [if_pos rfl, ite_true, if_neg (show (1 : Fin 2) ≠ 0 by decide),
      one_mul, neg_one_mul] at h0 h1
    have hplus := (mul_eq_zero.mp h0).resolve_left hn
    have hminus := (mul_eq_zero.mp h1).resolve_left hn
    constructor
    · linear_combination (1 / 2 : ℂ) * hplus + (1 / 2 : ℂ) * hminus
    · linear_combination (1 / 2 : ℂ) * hplus - (1 / 2 : ℂ) * hminus
  intro i j p hij
  fin_cases i <;> fin_cases j <;>
    first
    | exact (hij rfl).elim
    | simpa [sharpQutritWedgeFirst, sharpQutritWedgeSecond] using (hp 0 p).1
    | simpa [sharpQutritWedgeFirst, sharpQutritWedgeSecond] using (hp 0 p).2
    | simpa [sharpQutritWedgeFirst, sharpQutritWedgeSecond] using (hp 1 p).1
    | simpa [sharpQutritWedgeFirst, sharpQutritWedgeSecond] using (hp 1 p).2
    | simpa [sharpQutritWedgeFirst, sharpQutritWedgeSecond] using (hp 2 p).1
    | simpa [sharpQutritWedgeFirst, sharpQutritWedgeSecond] using (hp 2 p).2

/-- Actual sharp saturation annihilates every strict submaximal row in the
actual full physical eigenbasis. -/
theorem sharpQutritDiagonal_saturation_submax_row_zero
    (d : Fin 3 → ℝ) (hd : ∀ i, 0 ≤ d i)
    (Y : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) (hY : Y.rank ≤ 2)
    (hQ : sharpDoubleAnti Y = sharpQutritAntiEncode (Matrix.diagonal (fun i => (d i : ℂ))))
    (hs : frobSq (sharpDoubleAnti Y) = frobSq Y / 2) (hpos : 0 < frobSq Y)
    (j : SharpQutritDiagonalIndex) (hj : sharpQutritDiagonalWeight d j ^ 2 < ∑ i, d i ^ 2)
    (p : Fin 3 × Fin 3) : ((sharpQutritDiagonalFrame d)ᴴ * Y) j p = 0 := by
  have hm := sharpQutritDiagonal_saturation_middle_zero d hd Y hY hQ hs hpos
  let Z := sharpQutritAntiEncode (Matrix.diagonal (fun i => (d i : ℂ)))
  have hfix : sharpDoubleAnti Z = Z := sharpQutritAntiEncode_fixed _
  have ht : (Zᴴ * Y).trace = (frobSq Z : ℂ) := by
    rw [← hsInner_eq_trace]
    calc
      hsInner Z Y = hsInner (sharpDoubleAnti Z) Y := by rw [hfix]
      _ = hsInner Z (sharpDoubleAnti Y) := sharpDoubleAnti_selfadjoint Z Y
      _ = hsInner Z Z := by rw [hQ]
      _ = (frobSq Z : ℂ) := (ofReal_frobSq Z).symm
  have hZ : frobSq Z = 4 * ∑ i, d i ^ 2 := by
    change frobSq (sharpQutritAntiEncode (Matrix.diagonal (fun i => (d i : ℂ)))) = _
    rw [sharpQutritAntiEncode_frobSq]
    simp [frobSq, Matrix.diagonal_apply, apply_ite, Complex.normSq_ofReal, pow_two]
  have hnorm : frobSq Y = 8 * ∑ i, d i ^ 2 := by
    rw [hQ] at hs
    change frobSq Z = frobSq Y / 2 at hs
    linarith
  apply rankTwo_spectral_overlap_eq_submax_rows_zero
    (sharpQutritDiagonalFrame d) (sharpQutritDiagonalFrame_gram d)
    (sharpQutritDiagonalWeight d) (∑ i, d i ^ 2)
    (Finset.sum_nonneg (fun i _ => sq_nonneg (d i)))
    (sharpQutritDiagonalWeight_sq_le_sum_of_middle_zero d hm) Y hY hpos ?_ j hj p
  rw [← sharpQutritDiagonalFrame_factorization]
  change Complex.normSq (Zᴴ * Y).trace = _
  rw [ht, Complex.normSq_ofReal, hZ, hnorm]
  ring

/-- Strictness for the three external coefficient weights yields physical
diagonal-row support, derived from the original rank and saturation hypotheses. -/
theorem sharpQutritDiagonal_saturation_strict_external_rows
    (d : Fin 3 → ℝ) (hd : ∀ i, 0 ≤ d i)
    (Y : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) (hY : Y.rank ≤ 2)
    (hQ : sharpDoubleAnti Y = sharpQutritAntiEncode (Matrix.diagonal (fun i => (d i : ℂ))))
    (hs : frobSq (sharpDoubleAnti Y) = frobSq Y / 2) (hpos : 0 < frobSq Y)
    (he : ∀ a, d a ^ 2 < ∑ i, d i ^ 2) :
    ∀ i j p, i ≠ j → Y (i, j) p = 0 := by
  apply sharpQutritDiagonalFrame_external_zero_forces_diagonal_rows d Y
  intro a s p
  apply sharpQutritDiagonal_saturation_submax_row_zero d hd Y hY hQ hs hpos
  simpa only [sharpQutritDiagonalWeight, Sum.elim_inr,
    sharpQutritExternalWeight_sq] using he a

/-- Singular reshapes of every actual range vector exclude two nonzero
exterior coefficients. Physical support is derived, with no pencil premise. -/
theorem sharpQutritDiagonal_saturation_singular_range_single_coefficient
    (d : Fin 3 → ℝ) (hd : ∀ i, 0 ≤ d i)
    (Y : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) (hY : Y.rank ≤ 2)
    (hQ : sharpDoubleAnti Y = sharpQutritAntiEncode (Matrix.diagonal (fun i => (d i : ℂ))))
    (hs : frobSq (sharpDoubleAnti Y) = frobSq Y / 2) (hpos : 0 < frobSq Y)
    (hrange : ∀ v : Fin 3 × Fin 3 → ℂ, (sharpReshape (Y *ᵥ v)).det = 0) :
    (d 1 = 0 ∧ d 2 = 0) ∨ (d 0 = 0 ∧ d 2 = 0) ∨ (d 0 = 0 ∧ d 1 = 0) := by
  by_contra hn
  have he : ∀ a, d a ^ 2 < ∑ i, d i ^ 2 := by
    intro a
    by_contra! h
    simp only [Fin.sum_univ_three] at h
    fin_cases a
    · change d 0 ^ 2 + d 1 ^ 2 + d 2 ^ 2 ≤ d 0 ^ 2 at h
      have h1 : d 1 = 0 := sq_eq_zero_iff.mp (by nlinarith [sq_nonneg (d 2)])
      have h2 : d 2 = 0 := sq_eq_zero_iff.mp (by nlinarith [sq_nonneg (d 1)])
      exact hn (Or.inl ⟨h1, h2⟩)
    · change d 0 ^ 2 + d 1 ^ 2 + d 2 ^ 2 ≤ d 1 ^ 2 at h
      have h0 : d 0 = 0 := sq_eq_zero_iff.mp (by nlinarith [sq_nonneg (d 2)])
      have h2 : d 2 = 0 := sq_eq_zero_iff.mp (by nlinarith [sq_nonneg (d 0)])
      exact hn (Or.inr (Or.inl ⟨h0, h2⟩))
    · change d 0 ^ 2 + d 1 ^ 2 + d 2 ^ 2 ≤ d 2 ^ 2 at h
      have h0 : d 0 = 0 := sq_eq_zero_iff.mp (by nlinarith [sq_nonneg (d 1)])
      have h1 : d 1 = 0 := sq_eq_zero_iff.mp (by nlinarith [sq_nonneg (d 0)])
      exact hn (Or.inr (Or.inr ⟨h0, h1⟩))
  have hrows := sharpQutritDiagonal_saturation_strict_external_rows d hd Y hY hQ hs hpos he
  exact hn (sharpQutritDiagonalRows_singular_range_forces_single_coefficient
    d hd Y hrows hQ hs hrange)

end ThreeCopyQutritWerner
