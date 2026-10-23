module

public import CGLMPBounds.Companion.FourierBlocks

@[expose] public section


/-!
# Entry and trace expansion of the block Fourier operator

These finite identities connect the matrix construction with the weighted scalar
Fourier kernels. They retain the complex trace before real parts and normalization
are taken. In particular, the cross term is `Tr(B_j B_k†)`, whose cyclic trace is
the conjugate of the source correlation `Tr(B_j† B_k)`.
-/

open Matrix
open scoped Kronecker
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

namespace CGLMPBounds.Companion
noncomputable section

variable {d : ℕ} [NeZero d]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A computational outcome projector with arbitrary finite multiplicity space. -/
def outcomeProjector (a : ZMod d) : Matrix (ZMod d × ι) (ZMod d × ι) ℂ :=
  Matrix.diagonal fun p => if p.1 = a then 1 else 0

/-- The block in row outcome `a`, column outcome `b`. -/
def outcomeBlock (X : Matrix (ZMod d × ι) (ZMod d × ι) ℂ) (a b : ZMod d) : Matrix ι ι ℂ :=
  fun u v => X (a, u) (b, v)

lemma outcomeProjector_sandwich_apply
    (X : Matrix (ZMod d × ι) (ZMod d × ι) ℂ) (a b : ZMod d)
    (p q : ZMod d × ι) :
    (outcomeProjector a * X * outcomeProjector b :
      Matrix (ZMod d × ι) (ZMod d × ι) ℂ) p q =
      if p.1 = a ∧ q.1 = b then X p q else 0 := by
  simp only [outcomeProjector, Matrix.mul_diagonal, Matrix.diagonal_mul]
  split_ifs <;> simp_all

/-- The computational two-projector trace is the squared Hilbert–Schmidt norm of one block. -/
lemma trace_outcomeProjector_pair
    (X : Matrix (ZMod d × ι) (ZMod d × ι) ℂ) (a b : ZMod d) :
    Matrix.trace (outcomeProjector a * X * outcomeProjector b * Xᴴ) =
      Matrix.trace (outcomeBlock X a b * (outcomeBlock X a b)ᴴ) := by
  change (∑ p : ZMod d × ι, ∑ q : ZMod d × ι,
      (outcomeProjector a * X * outcomeProjector b : Matrix (ZMod d × ι) _ ℂ) p q *
        star (X p q)) =
    ∑ u : ι, ∑ v : ι, X (a, u) (b, v) * star (X (a, u) (b, v))
  simp only [outcomeProjector_sandwich_apply, Fintype.sum_prod_type]
  simp [ite_mul, ite_and, Finset.sum_ite_irrel]

def blockFourierOperator (B : Fin d → Matrix ι ι ℂ) :
    Matrix (ZMod d × ι) (ZMod d × ι) ℂ :=
  liftedFourier (d := d) (ι := ι) * frequencyDiagonal B *
    (liftedFourier (d := d) (ι := ι))ᴴ

/-- The two Fourier entries multiplying the frequency block in an outcome block. -/
def entryCoefficient (a b : ZMod d) (j : Fin d) : ℂ :=
  outcomeFourier a j * star (outcomeFourier b j)

lemma star_stdAddChar (a : ZMod d) :
    star (ZMod.stdAddChar a) = ZMod.stdAddChar (-a) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, AddChar.map_neg_eq_inv,
    Circle.coe_inv_eq_conj]
  rfl

lemma entryCoefficient_char (a b : ZMod d) (j : Fin d) :
    entryCoefficient a b j = (1 / (d : ℂ)) *
      ZMod.stdAddChar ((a - b) * (j.val : ZMod d)) := by
  have hscale : (((Real.sqrt d)⁻¹ : ℝ) : ℂ) * (((Real.sqrt d)⁻¹ : ℝ) : ℂ) =
      1 / (d : ℂ) := by
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg d)]
    push_cast <;> simp only [one_div]
  simp only [entryCoefficient, outcomeFourier, star_mul', star_stdAddChar,
    Complex.star_def, Complex.conj_ofReal]
  calc
    _ = ((((Real.sqrt d)⁻¹ : ℝ) : ℂ) * (((Real.sqrt d)⁻¹ : ℝ) : ℂ)) *
        (ZMod.stdAddChar (a * (j.val : ZMod d)) *
          ZMod.stdAddChar (-(b * (j.val : ZMod d)))) := by ring
    _ = (1 / (d : ℂ)) *
        ZMod.stdAddChar (a * (j.val : ZMod d) + -(b * (j.val : ZMod d))) := by
      rw [hscale, ← AddChar.map_add_eq_mul]
    _ = _ := by rw [sub_mul, sub_eq_add_neg]

lemma entryCoefficient_pair_char (a b : ZMod d) (j k : Fin d) :
    entryCoefficient a b j * star (entryCoefficient a b k) =
      (1 / (d : ℂ) ^ 2) *
        ZMod.stdAddChar ((a - b) * ((j.val : ZMod d) - (k.val : ZMod d))) := by
  simp only [entryCoefficient_char, star_mul', star_stdAddChar, star_div₀,
    star_one, star_inv₀, star_natCast]
  calc
    _ = (1 / (d : ℂ) ^ 2) *
        (ZMod.stdAddChar ((a - b) * (j.val : ZMod d)) *
          ZMod.stdAddChar (-((a - b) * (k.val : ZMod d)))) := by ring
    _ = _ := by
      rw [← AddChar.map_add_eq_mul]
      rw [show (a - b) * (j.val : ZMod d) + -((a - b) * (k.val : ZMod d)) =
        (a - b) * ((j.val : ZMod d) - (k.val : ZMod d)) by ring]

lemma entryCoefficient_pair_residual (a b : ZMod d) (j k : Fin d) :
    entryCoefficient a b j * star (entryCoefficient a b k) =
      (1 / (d : ℂ) ^ 2) *
        (outcomeRoot j * star (outcomeRoot k)) ^ (a - b).val := by
  rw [entryCoefficient_pair_char]
  have harg : (a - b) * ((j.val : ZMod d) - (k.val : ZMod d)) =
      (a - b).val • ((j.val : ZMod d) - (k.val : ZMod d)) := by
    rw [nsmul_eq_mul, ZMod.natCast_zmod_val]
  rw [harg, AddChar.map_nsmul_eq_pow]
  congr 2
  rw [sub_eq_add_neg, AddChar.map_add_eq_mul, ← star_stdAddChar]
  rfl

lemma trace_cross_star (A B : Matrix ι ι ℂ) :
    Matrix.trace (A * Bᴴ) = star (Matrix.trace (Aᴴ * B)) := by
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.trace_mul_comm]

lemma blockFourierOperator_apply (B : Fin d → Matrix ι ι ℂ)
    (a b : ZMod d) (u v : ι) :
    blockFourierOperator B (a, u) (b, v) =
      ∑ j, entryCoefficient a b j * B j u v := by
  simp only [blockFourierOperator, Matrix.mul_apply, Fintype.sum_prod_type,
    liftedFourier, Matrix.kronecker_apply, frequencyDiagonal_apply,
    Matrix.conjTranspose_apply, Matrix.one_apply]
  simp only [star_mul', apply_ite star, star_one, star_zero, mul_ite, ite_mul,
    Finset.sum_mul, Finset.mul_sum]
  simp [Finset.sum_ite_irrel, entryCoefficient, mul_assoc, mul_left_comm, mul_comm]

lemma outcomeBlock_blockFourierOperator (B : Fin d → Matrix ι ι ℂ) (a b : ZMod d) :
    outcomeBlock (blockFourierOperator B) a b = ∑ j, entryCoefficient a b j • B j := by
  ext u v
  simp only [outcomeBlock, blockFourierOperator_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]

lemma trace_weighted_blocks_mul_star (B : Fin d → Matrix ι ι ℂ) (c : Fin d → ℂ) :
    Matrix.trace ((∑ j, c j • B j) * (∑ k, c k • B k)ᴴ) =
      ∑ j, ∑ k, (c j * star (c k)) * Matrix.trace (B j * (B k)ᴴ) := by
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Matrix.sum_mul,
    Matrix.mul_sum, smul_mul_smul_comm, Matrix.trace_sum, Matrix.trace_smul,
    smul_eq_mul]
  exact Finset.sum_comm

/-- The exact complex trace expansion to be combined with the oriented scalar pairing. -/
theorem trace_blockFourierOperator_pair (B : Fin d → Matrix ι ι ℂ) (a b : ZMod d) :
    Matrix.trace (outcomeProjector a * blockFourierOperator B * outcomeProjector b *
        (blockFourierOperator B)ᴴ) =
      ∑ j, ∑ k, (entryCoefficient a b j * star (entryCoefficient a b k)) *
        Matrix.trace (B j * (B k)ᴴ) := by
  rw [trace_outcomeProjector_pair, outcomeBlock_blockFourierOperator,
    trace_weighted_blocks_mul_star]

theorem trace_blockFourierOperator_residual (B : Fin d → Matrix ι ι ℂ) (a b : ZMod d) :
    Matrix.trace (outcomeProjector a * blockFourierOperator B * outcomeProjector b *
        (blockFourierOperator B)ᴴ) =
      (1 / (d : ℂ) ^ 2) * ∑ j, ∑ k,
        (outcomeRoot j * star (outcomeRoot k)) ^ (a - b).val *
          Matrix.trace (B j * (B k)ᴴ) := by
  rw [trace_blockFourierOperator_pair]
  simp only [entryCoefficient_pair_residual, mul_assoc, ← Finset.mul_sum]

lemma sum_outcome_residual (f : ZMod d → ℂ) :
    (∑ a : ZMod d, ∑ b : ZMod d, f (a - b)) = (d : ℂ) * ∑ r, f r := by
  have hshift : ∀ b : ZMod d, (∑ a, f (a - b)) = ∑ r, f r := by
    intro b
    exact Fintype.sum_equiv (Equiv.subRight b) _ _ (fun _ => rfl)
  rw [Finset.sum_comm]
  simp only [hshift, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]

/-- The unnormalized residual-weighted trace sum, with the outcome multiplicity factor `d`. -/
theorem sum_weighted_trace_blockFourierOperator (B : Fin d → Matrix ι ι ℂ) :
    (∑ a : ZMod d, ∑ b : ZMod d, ((a - b).val : ℂ) *
        Matrix.trace (outcomeProjector a * blockFourierOperator B * outcomeProjector b *
          (blockFourierOperator B)ᴴ)) =
      (d : ℂ) * ((1 / (d : ℂ) ^ 2) * ∑ r : ZMod d, (r.val : ℂ) *
        ∑ j, ∑ k, (outcomeRoot j * star (outcomeRoot k)) ^ r.val *
          Matrix.trace (B j * (B k)ᴴ)) := by
  simp only [trace_blockFourierOperator_residual]
  rw [sum_outcome_residual (fun r : ZMod d => (r.val : ℂ) *
    (1 / (d : ℂ) ^ 2 * ∑ j, ∑ k,
      (outcomeRoot j * star (outcomeRoot k)) ^ r.val *
        Matrix.trace (B j * (B k)ᴴ)))]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- Normalize on the physical space of dimension `d * card ι`; no extra factor `d` remains. -/
theorem normalized_weighted_trace_blockFourierOperator (B : Fin d → Matrix ι ι ℂ) :
    ((∑ a : ZMod d, ∑ b : ZMod d, ((a - b).val : ℂ) *
        Matrix.trace (outcomeProjector a * blockFourierOperator B * outcomeProjector b *
          (blockFourierOperator B)ᴴ)) / ((d : ℂ) * (Fintype.card ι : ℂ))) =
      (∑ r : ZMod d, (r.val : ℂ) *
        ∑ j, ∑ k, (outcomeRoot j * star (outcomeRoot k)) ^ r.val *
          Matrix.trace (B j * (B k)ᴴ)) /
        ((d : ℂ) ^ 2 * (Fintype.card ι : ℂ)) := by
  rw [sum_weighted_trace_blockFourierOperator]
  rw [mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr (NeZero.ne d))]
  rw [one_div, mul_comm (((d : ℂ) ^ 2)⁻¹), ← div_eq_mul_inv, div_div]

end
end CGLMPBounds.Companion
