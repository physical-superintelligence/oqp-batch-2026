module

public import ThreeCopyQutritWerner.SharpQutritDiagonalOverlap
public import ThreeCopyQutritWerner.RankOne

@[expose] public section


/-!
# Diagonal-row saturation and a concrete full-rank range vector

If a sharp extremizer has only physical diagonal rows, its actual projection
pairing forces it to equal twice the embedded central block. The image of one
explicit vector then has a diagonal reshape whose determinant is recorded
exactly, without classifying a pencil of singular matrices.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

/-- The central block embedded on both original physical diagonal coordinates. -/
def sharpQutritCentralEmbed (H : Matrix (Fin 3) (Fin 3) ℂ) :
    Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  fun p q => if p.1 = p.2 ∧ q.1 = q.2 then H p.1 q.1 else 0

/-- Embedding the central coordinates preserves their literal Frobenius norm. -/
theorem sharpQutritCentralEmbed_frobSq (H : Matrix (Fin 3) (Fin 3) ℂ) :
    frobSq (sharpQutritCentralEmbed H) = frobSq H := by
  simp [frobSq, sharpQutritCentralEmbed, Fintype.sum_prod_type, Fin.sum_univ_three]

set_option maxRecDepth 2048 in
/-- On a physical diagonal row, the encoded matrix is exactly the central
embedding, including all zero off-diagonal-column entries. -/
theorem sharpQutritAntiEncode_diagonal_row (d : Fin 3 → ℝ) (i : Fin 3)
    (p : Fin 3 × Fin 3) :
    sharpQutritAntiEncode (Matrix.diagonal (fun a => (d a : ℂ))) (i, i) p =
      sharpQutritCentralEmbed (sharpQutritCentralBlock (fun a => (d a : ℂ))) (i, i) p := by
  rcases p with ⟨j, k⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [sharpQutritAntiEncode, sharpQutritWedgeBasis, Matrix.diagonal_apply,
      sharpQutritCentralEmbed, sharpQutritCentralBlock, Fin.sum_univ_three]

/-- A matrix supported on physical diagonal rows has the same pairing with
the encoded projection and with its original central block. -/
theorem sharpQutritCentralEmbed_pairing
    (d : Fin 3 → ℝ) (Y : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (hrows : ∀ i j p, i ≠ j → Y (i, j) p = 0) :
    hsInner (sharpQutritCentralEmbed (sharpQutritCentralBlock (fun a => (d a : ℂ)))) Y =
      hsInner (sharpQutritAntiEncode (Matrix.diagonal (fun a => (d a : ℂ)))) Y := by
  unfold hsInner
  apply Finset.sum_congr rfl
  rintro ⟨i, j⟩ _
  apply Finset.sum_congr rfl
  intro p _
  by_cases hij : i = j
  · subst j
    rw [sharpQutritAntiEncode_diagonal_row]
  · rw [hrows i j p hij, mul_zero, mul_zero]

/-- Sharp projection saturation and diagonal-row support force an exact
matrix identity, with the original normalization factor two. -/
theorem sharpQutritDiagonalRows_saturation_eq_twice_central
    (d : Fin 3 → ℝ) (Y : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (hrows : ∀ i j p, i ≠ j → Y (i, j) p = 0)
    (hQ : sharpDoubleAnti Y = sharpQutritAntiEncode (Matrix.diagonal (fun i => (d i : ℂ))))
    (hs : frobSq (sharpDoubleAnti Y) = frobSq Y / 2) :
    Y = (2 : ℂ) • sharpQutritCentralEmbed
      (sharpQutritCentralBlock (fun i => (d i : ℂ))) := by
  let Z := sharpQutritAntiEncode (Matrix.diagonal (fun i => (d i : ℂ)))
  let D := sharpQutritCentralEmbed (sharpQutritCentralBlock (fun i => (d i : ℂ)))
  have hZ : frobSq Z = 4 * ∑ i, d i ^ 2 := by
    change frobSq (sharpQutritAntiEncode (Matrix.diagonal (fun i => (d i : ℂ)))) = _
    rw [sharpQutritAntiEncode_frobSq]
    simp [frobSq, Matrix.diagonal_apply, apply_ite, Complex.normSq_ofReal, pow_two]
  have hD : frobSq D = 2 * ∑ i, d i ^ 2 := by
    change frobSq (sharpQutritCentralEmbed
      (sharpQutritCentralBlock (fun i => (d i : ℂ)))) = _
    rw [sharpQutritCentralEmbed_frobSq, sharpQutritCentralBlock_frobSq]
  have hp : (hsInner D Y).re = frobSq Z := by
    rw [sharpQutritCentralEmbed_pairing d Y hrows]
    change (hsInner Z Y).re = _
    have hfix : sharpDoubleAnti Z = Z := sharpQutritAntiEncode_fixed _
    calc
      (hsInner Z Y).re = (hsInner (sharpDoubleAnti Z) Y).re := by rw [hfix]
      _ = (hsInner Z (sharpDoubleAnti Y)).re := by
        rw [sharpDoubleAnti_selfadjoint]
      _ = (hsInner Z Z).re := by rw [hQ]
      _ = frobSq Z := zeroReserve_hsInner_self_re Z
  rw [hQ] at hs
  change frobSq Z = frobSq Y / 2 at hs
  have hnorm : frobSq (Y - (2 : ℂ) • D) = 0 := by
    have he : ((1 : ℝ) : ℂ) • Y + ((-2 : ℝ) : ℂ) • D = Y - (2 : ℂ) • D := by
      simp [sub_eq_add_neg]
    have hm := zeroReserve_frobSq_real_mix Y D 1 (-2)
    rw [he, hsInner_re_comm Y D, hp] at hm
    norm_num at hm
    linarith
  exact sub_eq_zero.mp (matrix_eq_zero_of_frobSq_eq_zero _ hnorm)

/-- The single test vector used for the concrete range obstruction. -/
def sharpQutritDiagonalOnes (p : Fin 3 × Fin 3) : ℂ := if p.1 = p.2 then 1 else 0

/-- Exact determinant of the reshape of one actual image vector of twice the
central block. It is nonzero as soon as all three pair sums are positive. -/
theorem sharpQutritTwiceCentral_range_det (d : Fin 3 → ℝ) :
    (sharpReshape (((2 : ℂ) • sharpQutritCentralEmbed
      (sharpQutritCentralBlock (fun i => (d i : ℂ)))) *ᵥ sharpQutritDiagonalOnes)).det =
        8 * ((d 1 + d 2 : ℝ) : ℂ) * ((d 0 + d 2 : ℝ) : ℂ) *
          ((d 0 + d 1 : ℝ) : ℂ) := by
  simp [sharpReshape, sharpQutritCentralEmbed, sharpQutritCentralBlock,
    sharpQutritDiagonalOnes, Matrix.det_fin_three, Matrix.mulVec, dotProduct,
    Matrix.smul_apply, smul_eq_mul, Fintype.sum_prod_type, Fin.sum_univ_three]
  ring

/-- If every actual range vector has singular reshape, diagonal-row sharp
saturation permits at most one nonzero nonnegative exterior coefficient.
The contradiction uses only the displayed single image vector. -/
theorem sharpQutritDiagonalRows_singular_range_forces_single_coefficient
    (d : Fin 3 → ℝ) (hd : ∀ i, 0 ≤ d i)
    (Y : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (hrows : ∀ i j p, i ≠ j → Y (i, j) p = 0)
    (hQ : sharpDoubleAnti Y = sharpQutritAntiEncode (Matrix.diagonal (fun i => (d i : ℂ))))
    (hs : frobSq (sharpDoubleAnti Y) = frobSq Y / 2)
    (hrange : ∀ v : Fin 3 × Fin 3 → ℂ, (sharpReshape (Y *ᵥ v)).det = 0) :
    (d 1 = 0 ∧ d 2 = 0) ∨ (d 0 = 0 ∧ d 2 = 0) ∨ (d 0 = 0 ∧ d 1 = 0) := by
  have hY := sharpQutritDiagonalRows_saturation_eq_twice_central d Y hrows hQ hs
  have hdet := hrange sharpQutritDiagonalOnes
  rw [hY, sharpQutritTwiceCentral_range_det] at hdet
  have hr : 8 * (d 1 + d 2) * (d 0 + d 2) * (d 0 + d 1) = (0 : ℝ) := by
    exact_mod_cast hdet
  have hp8 : (8 : ℝ) * ((d 1 + d 2) * (d 0 + d 2) * (d 0 + d 1)) = 0 := by
    convert hr using 1 <;> ring
  have hp : (d 1 + d 2) * (d 0 + d 2) * (d 0 + d 1) = 0 :=
    (mul_eq_zero.mp hp8).resolve_left (by norm_num)
  rcases mul_eq_zero.mp hp with h01 | h2
  · rcases mul_eq_zero.mp h01 with h0 | h1
    · exact Or.inl ⟨by linarith [hd 1, hd 2], by linarith [hd 1, hd 2]⟩
    · exact Or.inr (Or.inl ⟨by linarith [hd 0, hd 2], by linarith [hd 0, hd 2]⟩)
  · exact Or.inr (Or.inr ⟨by linarith [hd 0, hd 1], by linarith [hd 0, hd 1]⟩)

end ThreeCopyQutritWerner
