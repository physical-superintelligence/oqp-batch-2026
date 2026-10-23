module

public import CGLMPBounds.Companion.Fourier

@[expose] public section


/-!
# Frequency blocks of a unitary fourth root of the shift

After Fourier conjugation, an operator whose fourth power is `J ⊗ I` commutes
with a scalar diagonal matrix having distinct outcome eigenvalues. Its blocks
between different frequencies therefore vanish. This supplies the finite
spectral-block step in Lemma C.1 without assuming the companion tuple exists.
-/

open Matrix
open scoped Kronecker
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
attribute [default_instance 110] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

namespace CGLMPBounds.Companion
noncomputable section

variable {d : ℕ} [NeZero d]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The source Fourier transformation, acting trivially on the multiplicity space. -/
def liftedFourier : Matrix (ZMod d × ι) (Fin d × ι) ℂ :=
  outcomeFourier ⊗ₖ (1 : Matrix ι ι ℂ)

lemma liftedFourier_mul_star :
    liftedFourier (d := d) (ι := ι) * (liftedFourier (d := d) (ι := ι))ᴴ = 1 := by
  simp only [liftedFourier, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, outcomeFourier_mul_star, Matrix.one_mul,
    Matrix.one_kronecker_one]

lemma liftedFourier_star_mul :
    (liftedFourier (d := d) (ι := ι))ᴴ * liftedFourier (d := d) (ι := ι) = 1 := by
  simp only [liftedFourier, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, outcomeFourier_star_mul, Matrix.one_mul,
    Matrix.one_kronecker_one]

def frequencyConjugate (X : Matrix (ZMod d × ι) (ZMod d × ι) ℂ) :
    Matrix (Fin d × ι) (Fin d × ι) ℂ :=
  (liftedFourier (d := d) (ι := ι))ᴴ * X * liftedFourier (d := d) (ι := ι)

lemma frequencyConjugate_one : frequencyConjugate (1 : Matrix (ZMod d × ι) _ ℂ) = 1 := by
  rw [frequencyConjugate, Matrix.mul_one, liftedFourier_star_mul]

lemma frequencyConjugate_mul (X Y : Matrix (ZMod d × ι) (ZMod d × ι) ℂ) :
    frequencyConjugate X * frequencyConjugate Y = frequencyConjugate (X * Y) := by
  unfold frequencyConjugate
  calc
    ((liftedFourier (d := d) (ι := ι))ᴴ * X * liftedFourier (d := d) (ι := ι)) *
        ((liftedFourier (d := d) (ι := ι))ᴴ * Y * liftedFourier (d := d) (ι := ι)) =
      (liftedFourier (d := d) (ι := ι))ᴴ *
        (X * (liftedFourier (d := d) (ι := ι) *
          (liftedFourier (d := d) (ι := ι))ᴴ) * Y) *
        liftedFourier (d := d) (ι := ι) := by simp only [Matrix.mul_assoc]
    _ = (liftedFourier (d := d) (ι := ι))ᴴ * (X * Y) * liftedFourier (d := d) (ι := ι) := by
      rw [liftedFourier_mul_star, Matrix.mul_one]

lemma frequencyConjugate_star (X : Matrix (ZMod d × ι) (ZMod d × ι) ℂ) :
    frequencyConjugate Xᴴ = (frequencyConjugate X)ᴴ := by
  simp only [frequencyConjugate, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

lemma frequencyConjugate_pow (X : Matrix (ZMod d × ι) (ZMod d × ι) ℂ) (k : ℕ) :
    frequencyConjugate (X ^ k) = frequencyConjugate X ^ k := by
  induction k with
  | zero => simp only [pow_zero, frequencyConjugate_one]
  | succ k ih => rw [pow_succ, ← frequencyConjugate_mul, ih, pow_succ]

lemma frequencyConjugate_reconstruct (X : Matrix (ZMod d × ι) (ZMod d × ι) ℂ) :
    liftedFourier (d := d) (ι := ι) * frequencyConjugate X *
      (liftedFourier (d := d) (ι := ι))ᴴ = X := by
  unfold frequencyConjugate
  calc
    liftedFourier (d := d) (ι := ι) *
        ((liftedFourier (d := d) (ι := ι))ᴴ * X * liftedFourier (d := d) (ι := ι)) *
        (liftedFourier (d := d) (ι := ι))ᴴ =
        (liftedFourier (d := d) (ι := ι) * (liftedFourier (d := d) (ι := ι))ᴴ) * X *
          (liftedFourier (d := d) (ι := ι) * (liftedFourier (d := d) (ι := ι))ᴴ) := by simp only [Matrix.mul_assoc]
    _ = X := by rw [liftedFourier_mul_star, Matrix.one_mul, Matrix.mul_one]

lemma frequencyConjugate_shift :
    frequencyConjugate (outcomeShift (d := d) ⊗ₖ (1 : Matrix ι ι ℂ)) =
      Matrix.diagonal (fun p : Fin d × ι => outcomeRoot p.1) := by
  simp only [frequencyConjugate, liftedFourier, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    Matrix.mul_one, outcomeFourier_diagonalizes_shift]
  rw [show (1 : Matrix ι ι ℂ) = Matrix.diagonal (fun _ => 1) from rfl,
    Matrix.diagonal_kronecker_diagonal]
  simp only [mul_one]

/-- Assemble frequency-indexed square blocks into the ordinary product-index matrix. -/
def frequencyDiagonal : (Fin d → Matrix ι ι ℂ) →+* Matrix (Fin d × ι) (Fin d × ι) ℂ :=
  (Matrix.compRingEquiv (Fin d) ι ℂ).toRingHom.comp
    (Matrix.diagonalRingHom (Fin d) (Matrix ι ι ℂ))

lemma frequencyDiagonal_apply (B : Fin d → Matrix ι ι ℂ) (j k : Fin d) (u v : ι) :
    frequencyDiagonal B (j, u) (k, v) = if j = k then B j u v else 0 := by
  change (Matrix.diagonal B j k) u v = _
  by_cases h : j = k <;> simp [Matrix.diagonal_apply, h]

lemma frequencyDiagonal_injective : Function.Injective (frequencyDiagonal (d := d) (ι := ι)) :=
  (Matrix.compRingEquiv (Fin d) ι ℂ).injective.comp Matrix.diagonal_injective

lemma frequencyDiagonal_star (B : Fin d → Matrix ι ι ℂ) :
    frequencyDiagonal (fun j => (B j)ᴴ) = (frequencyDiagonal B)ᴴ := by
  ext p q
  rcases p with ⟨j, u⟩
  rcases q with ⟨k, v⟩
  by_cases h : j = k
  · subst k
    simp [frequencyDiagonal_apply, Matrix.conjTranspose_apply]
  · simp [frequencyDiagonal_apply, Matrix.conjTranspose_apply, h, Ne.symm h]

lemma frequencyDiagonal_roots :
    frequencyDiagonal (fun j : Fin d => outcomeRoot j • (1 : Matrix ι ι ℂ)) =
      Matrix.diagonal (fun p : Fin d × ι => outcomeRoot p.1) := by
  ext p q
  rcases p with ⟨j, u⟩
  rcases q with ⟨k, v⟩
  simp [frequencyDiagonal_apply, Matrix.diagonal_apply, Matrix.one_apply,
    Matrix.smul_apply, smul_eq_mul, Prod.mk.injEq, ite_and]

/-- Read the square block on one frequency subspace. -/
def frequencyBlock (W : Matrix (Fin d × ι) (Fin d × ι) ℂ) (j : Fin d) : Matrix ι ι ℂ :=
  fun u v => W (j, u) (j, v)

lemma frequency_off_diagonal (W : Matrix (Fin d × ι) (Fin d × ι) ℂ)
    (hfour : W ^ 4 = Matrix.diagonal (fun p : Fin d × ι => outcomeRoot p.1))
    {j k : Fin d} (hjk : j ≠ k) (u v : ι) : W (j, u) (k, v) = 0 := by
  have hc : W * Matrix.diagonal (fun p : Fin d × ι => outcomeRoot p.1) =
      Matrix.diagonal (fun p : Fin d × ι => outcomeRoot p.1) * W := by
    rw [← hfour]
    exact (pow_succ' W 4).symm.trans (pow_succ W 4)
  have he := congrArg (fun M : Matrix (Fin d × ι) (Fin d × ι) ℂ =>
    M (j, u) (k, v)) hc
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at he
  have hz : (outcomeRoot k - outcomeRoot j) * W (j, u) (k, v) = 0 := by
    calc
      _ = W (j, u) (k, v) * outcomeRoot k - outcomeRoot j * W (j, u) (k, v) := by ring
      _ = 0 := sub_eq_zero.mpr he
  exact (mul_eq_zero.mp hz).resolve_left
    (sub_ne_zero.mpr (fun h => hjk (outcomeRoot_injective h).symm))

/-- Distinct shift frequencies force the transformed fourth root to be block diagonal. -/
theorem frequency_eq_diagonal (W : Matrix (Fin d × ι) (Fin d × ι) ℂ)
    (hfour : W ^ 4 = Matrix.diagonal (fun p : Fin d × ι => outcomeRoot p.1)) :
    W = frequencyDiagonal (frequencyBlock W) := by
  ext p q
  rcases p with ⟨j, u⟩
  rcases q with ⟨k, v⟩
  by_cases h : j = k
  · subst k
    simp [frequencyDiagonal_apply, frequencyBlock]
  · rw [frequencyDiagonal_apply, if_neg h, frequency_off_diagonal W hfour h]

end
end CGLMPBounds.Companion
