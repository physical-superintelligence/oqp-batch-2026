module

public import ThreeCopyQutritWerner.TwoCutSOS
public import ThreeCopyQutritWerner.Embedding

@[expose] public section


/-!
# Literal second compounds for the positive rank-two reserve route

This is the second exterior-power operator represented in the full ordered-pair
coordinate spaces. Each entry is half a two-by-two minor. The factor one half
makes composition literal: the two orientations of each intermediate pair
otherwise count twice. Restriction to the normalized antisymmetric basis has
exactly the usual minor entries, and the ambient matrix is zero on symmetric
inputs. Its squared Frobenius norm is therefore the usual second-compound norm.

These finite identities discharge algebraic ingredients of Wu--Zou, Lemma 5.1.
They do not assert the nuclear-norm bound or the positive rank-two reserve.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

/-- The second compound in redundant ordered-pair coordinates, with its exact normalization. -/
def zeroReserveCompound {m n : Type*} (X : Matrix m n ℂ) :
    Matrix (m × m) (n × n) ℂ :=
  fun r c => (X r.1 c.1 * X r.2 c.2 - X r.1 c.2 * X r.2 c.1) / 2

/-- Both coordinate pairs are alternating. -/
theorem zeroReserveCompound_swap_rows {m n : Type*} (X : Matrix m n ℂ)
    (i j : m) (c : n × n) :
    zeroReserveCompound X (j, i) c = -zeroReserveCompound X (i, j) c := by
  unfold zeroReserveCompound
  ring

theorem zeroReserveCompound_swap_cols {m n : Type*} (X : Matrix m n ℂ)
    (r : m × m) (i j : n) :
    zeroReserveCompound X r (j, i) = -zeroReserveCompound X r (i, j) := by
  unfold zeroReserveCompound
  ring

/-- The adjoint convention is exactly the ordinary complex exterior-power convention. -/
theorem zeroReserveCompound_conjTranspose {m n : Type*} (X : Matrix m n ℂ) :
    zeroReserveCompound Xᴴ = (zeroReserveCompound X)ᴴ := by
  ext r c
  simp only [zeroReserveCompound, Matrix.conjTranspose_apply, Complex.star_def, map_div₀, map_sub,
    map_mul, map_ofNat]
  ring

private theorem sum_minor_product {k : Type*} [Fintype k] (a b c d : k → ℂ) :
    (∑ i, ∑ j, (a i * b j - a j * b i) * (c i * d j - c j * d i)) =
      2 * ((∑ i, a i * c i) * (∑ j, b j * d j) -
        (∑ i, a i * d i) * (∑ j, b j * c j)) := by
  have hp (f g : k → ℂ) : (∑ i, ∑ j, f i * g j) = (∑ i, f i) * ∑ j, g j := by
    simp only [Finset.sum_mul_sum]
  have he (i j : k) :
      (a i * b j - a j * b i) * (c i * d j - c j * d i) =
        (a i * c i) * (b j * d j) - (a i * d i) * (b j * c j) -
          (b i * c i) * (a j * d j) + (b i * d i) * (a j * c j) := by ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, hp]
  ring

/-- Cauchy--Binet for second compounds, retaining all ordered coordinates. -/
theorem zeroReserveCompound_mul {m n k : Type*} [Fintype n]
    (X : Matrix m n ℂ) (Y : Matrix n k ℂ) :
    zeroReserveCompound (X * Y) = zeroReserveCompound X * zeroReserveCompound Y := by
  ext r c
  have h := sum_minor_product (X r.1) (X r.2) (fun i => Y i c.1) (fun i => Y i c.2)
  have he : (∑ i, ∑ j, ((X r.1 i * X r.2 j - X r.1 j * X r.2 i) / 2) *
      ((Y i c.1 * Y j c.2 - Y i c.2 * Y j c.1) / 2)) =
      (∑ i, ∑ j, (X r.1 i * X r.2 j - X r.1 j * X r.2 i) *
        (Y i c.1 * Y j c.2 - Y j c.1 * Y i c.2)) / 4 := by
    simp only [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [zeroReserveCompound, Matrix.mul_apply, Fintype.sum_prod_type]
  rw [he, h]
  ring

/-- The two reduced Gram matrices have equal squared Frobenius norms. -/
theorem zeroReserve_frobSq_gram {m n : Type*} [Fintype m] [Fintype n]
    (X : Matrix m n ℂ) : frobSq (Xᴴ * X) = frobSq (X * Xᴴ) := by
  apply Complex.ofReal_injective
  rw [ofReal_frobSq_eq_trace, ofReal_frobSq_eq_trace]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm Xᴴ (X * (Xᴴ * X))]
  simp only [Matrix.mul_assoc]

private theorem zeroReserve_frobSq_transpose {m n : Type*} [Fintype m] [Fintype n]
    (X : Matrix m n ℂ) : frobSq Xᵀ = frobSq X := by
  simp only [frobSq, Matrix.transpose_apply]
  exact Finset.sum_comm

/-- The exact second-compound norm formula, with no singular-value assumptions. -/
theorem zeroReserveCompound_frobSq {m n : Type*} [Fintype m] [Fintype n]
    (X : Matrix m n ℂ) :
    2 * frobSq (zeroReserveCompound X) = frobSq X ^ 2 - frobSq (Xᴴ * X) := by
  let u : m × n → ℂ := fun p => X p.1 p.2
  have hu : vecNormSq u = frobSq X := by
    simp only [vecNormSq, u, frobSq, Fintype.sum_prod_type]
  have hb : braket u u = (frobSq X : ℂ) := by
    rw [← hu]
    exact (ofReal_vecNormSq u).symm
  have hl : ptraceL (ketBra u u) = (Xᴴ * X)ᵀ := by
    ext i j
    simp only [ptraceL, ketBra, u, Matrix.transpose_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Complex.star_def]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hr : ptraceR (ketBra u u) = X * Xᴴ := by
    ext i j
    simp only [ptraceR, ketBra, u, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.star_def]
  have ha (p : (m × n) × (m × n)) :
      biAnti u u p = 4 * zeroReserveCompound X (p.1.1, p.2.1) (p.1.2, p.2.2) := by
    simp only [biAnti, u, zeroReserveCompound]
    ring
  have hs : (∑ p : (m × n) × (m × n), Complex.normSq (biAnti u u p)) =
      16 * frobSq (zeroReserveCompound X) := by
    simp_rw [ha, Complex.normSq_mul]
    norm_num only [Complex.normSq_ofNat]
    rw [← Finset.mul_sum]
    congr 1
    change (∑ p : (m × n) × (m × n), Complex.normSq
      (zeroReserveCompound X (p.1.1, p.2.1) (p.1.2, p.2.2))) = _
    calc
      _ = ∑ p : (m × m) × (n × n), Complex.normSq
          (zeroReserveCompound X p.1 p.2) :=
        Fintype.sum_equiv (Equiv.prodProdProdComm m n m n) _ _ (fun _ => rfl)
      _ = _ := by simp only [Fintype.sum_prod_type, frobSq]
  have h := four_mul_biDefect u u
  rw [hs, biDefect, hu, hb, Complex.normSq_ofReal, ptraceNormSq, hl, hr,
    zeroReserve_frobSq_transpose, ← zeroReserve_frobSq_gram] at h
  nlinarith

/-- In particular the Gram purity defect is always nonnegative. -/
theorem zeroReserve_gram_defect_nonneg {m n : Type*} [Fintype m] [Fintype n]
    (X : Matrix m n ℂ) : 0 ≤ frobSq X ^ 2 - frobSq (Xᴴ * X) := by
  rw [← zeroReserveCompound_frobSq]
  exact mul_nonneg (by norm_num) (frobSq_nonneg _)

/-- At unit Frobenius norm this is exactly half the reduced-state linear entropy. -/
theorem zeroReserveCompound_frobSq_unit {m n : Type*} [Fintype m] [Fintype n]
    (X : Matrix m n ℂ) (hX : frobSq X = 1) :
    frobSq (zeroReserveCompound X) = (1 - frobSq (Xᴴ * X)) / 2 := by
  have h := zeroReserveCompound_frobSq X
  rw [hX] at h
  linarith

end ThreeCopyQutritWerner
