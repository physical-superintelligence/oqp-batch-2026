module

public import CGLMPBounds.CGLMP.FourierCommutant
public import CGLMPBounds.Fourier.Basis
public import CGLMPBounds.Defs.FourierCommutant

@[expose] public section


/-!
# The actual Fourier-phase PVMs have scalar commutant

Supplement Appendix E.1, p. 17. The gauge is the first Fourier-phase basis.
The entries of the next basis in this gauge are the actual overlaps from
`Defs.Fourier`, and their nonvanishing follows from the already established
exact residual law (F.1). No nonzero-entry or irreducibility hypothesis is
assumed for the standard family.
-/

open Matrix
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

namespace CGLMPBounds
noncomputable section

variable (d : ℕ) [NeZero d]

/-- Strict positivity of the exact residual law at every valid separation. -/
theorem fourierResidualLaw_pos_of_lt (r : ℕ) (hr : r < d) :
    0 < fourierResidualLaw d r := by
  have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
  have hr' : (r : ℝ) + 1 ≤ d := by exact_mod_cast hr
  have hangle : 0 < Real.pi * ((r : ℝ) + 1 / 4) / d :=
    div_pos (mul_pos Real.pi_pos (by positivity)) hd
  have hangle' : Real.pi * ((r : ℝ) + 1 / 4) / d < Real.pi := by
    rw [div_lt_iff₀ hd]
    exact mul_lt_mul_of_pos_left (by linarith : (r : ℝ) + 1 / 4 < d) Real.pi_pos
  have hsin := Real.sin_pos_of_pos_of_lt_pi hangle hangle'
  unfold fourierResidualLaw
  exact one_div_pos.mpr (mul_pos (mul_pos (by norm_num) (pow_pos hd 2)) (pow_pos hsin 2))

/-- Every overlap between the first and second actual standard bases is nonzero. -/
theorem inner_fourierVector_zero_one_ne_zero (a b : ZMod d) :
    star (fourierVector d 0 a) ⬝ᵥ fourierVector d 1 b ≠ 0 := by
  intro hzero
  have htable := fourierTable_zero_zero d a b
  have hzeroTable : fourierTable d 0 0 a b = 0 := by
    change (Matrix.trace (Matrix.vecMulVec (fourierVector d 0 a) (star (fourierVector d 0 a)) *
      Matrix.vecMulVec (fourierVector d 1 b) (star (fourierVector d 1 b)))).re / d = 0
    rw [re_trace_vecMulVec_star_mul, hzero, Complex.normSq_zero, zero_div]
  have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
  have hp : 0 < fourierResidualLaw d (residual d 0 0 a b) / d := by
    apply div_pos _ hd
    apply fourierResidualLaw_pos_of_lt
    rw [residual_zero_zero]
    exact ZMod.val_lt _
  rw [hzeroTable] at htable
  exact (ne_of_gt hp) htable.symm

theorem fourierBasisMatrix_star_mul (t : ℕ) :
    (fourierBasisMatrix d t)ᴴ * fourierBasisMatrix d t = 1 := by
  ext a b
  rw [Matrix.mul_apply, Matrix.one_apply, ← inner_fourierVector_same d t a b]
  rfl

theorem fourierBasisMatrix_mul_star (t : ℕ) :
    fourierBasisMatrix d t * (fourierBasisMatrix d t)ᴴ = 1 :=
  (Matrix.mul_eq_one_comm_of_card_eq (ZMod d) (Fin d) ℂ (by simp [ZMod.card])).mp
    (fourierBasisMatrix_star_mul d t)

/-- Passing to a basis's own coordinates gives the computational projectors. -/
theorem fourierBasisMatrix_conjugate_projector (t : ℕ) (a : ZMod d) :
    (fourierBasisMatrix d t)ᴴ * fourierProjector d t a * fourierBasisMatrix d t =
      Matrix.single a a 1 := by
  have hv : (fourierBasisMatrix d t)ᴴ *ᵥ fourierVector d t a = Pi.single a 1 := by
    funext b
    change star (fourierVector d t b) ⬝ᵥ fourierVector d t a = _
    rw [inner_fourierVector_same]
    simp [Pi.single_apply, eq_comm]
  rw [fourierProjector, basis_conjugate_rankOne, hv]
  ext i j
  by_cases hai : a = i <;> by_cases haj : a = j <;>
    simp [Matrix.vecMulVec_apply, Matrix.single_apply, Pi.star_apply,
      Pi.single_apply, hai, haj, eq_comm]

theorem fourierTransition_apply (a b : ZMod d) :
    fourierTransition d a b =
      star (fourierVector d 0 a) ⬝ᵥ fourierVector d 1 b := rfl

theorem fourierTransition_entry_ne_zero (a b : ZMod d) :
    fourierTransition d a b ≠ 0 :=
  inner_fourierVector_zero_one_ne_zero d a b

theorem fourierTransition_star_mul :
    (fourierTransition d)ᴴ * fourierTransition d = 1 := by
  rw [fourierTransition, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (fourierBasisMatrix d 0) (fourierBasisMatrix d 0)ᴴ,
    fourierBasisMatrix_mul_star, Matrix.one_mul, fourierBasisMatrix_star_mul]

/-- The actual second PVM, in first-basis coordinates, consists of the
rank-one column projectors of `fourierTransition`. -/
theorem fourierBasisMatrix_conjugate_second (b : ZMod d) :
    (fourierBasisMatrix d 0)ᴴ * fourierProjector d 1 b * fourierBasisMatrix d 0 =
      Matrix.vecMulVec (fun a => fourierTransition d a b)
        (star (fun a => fourierTransition d a b)) := by
  rw [fourierProjector, basis_conjugate_rankOne]
  rfl

/-- Appendix E.1: every operator commuting with the first two standard PVMs
is scalar. No Hermiticity assumption on the operator is necessary. -/
theorem eq_scalar_of_commute_fourierProjector_zero_one
    (X : Matrix (Fin d) (Fin d) ℂ)
    (hzero : ∀ a, X * fourierProjector d 0 a = fourierProjector d 0 a * X)
    (hone : ∀ a, X * fourierProjector d 1 a = fourierProjector d 1 a * X) :
    ∃ c : ℂ, X = c • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  let U := fourierBasisMatrix d 0
  have hU : U * Uᴴ = 1 := fourierBasisMatrix_mul_star d 0
  have hcoord (a : ZMod d) :
      (Uᴴ * X * U) * Matrix.single a a 1 = Matrix.single a a 1 * (Uᴴ * X * U) := by
    have h := basis_conjugate_commute U hU X (fourierProjector d 0 a) (hzero a)
    simpa only [U, fourierBasisMatrix_conjugate_projector] using h
  have hsecond (b : ZMod d) :
      (Uᴴ * X * U) * Matrix.vecMulVec (fun a => fourierTransition d a b)
          (star (fun a => fourierTransition d a b)) =
        Matrix.vecMulVec (fun a => fourierTransition d a b)
          (star (fun a => fourierTransition d a b)) * (Uᴴ * X * U) := by
    have h := basis_conjugate_commute U hU X (fourierProjector d 1 b) (hone b)
    simpa only [U, fourierBasisMatrix_conjugate_second] using h
  obtain ⟨c, hc⟩ := eq_scalar_of_commute_coordinate_and_columns
    (Uᴴ * X * U) (fourierTransition d) hcoord (fourierTransition_entry_ne_zero d) hsecond
  exact ⟨c, eq_scalar_of_basis_conjugate_eq U hU X c hc⟩

/-- The four standard PVMs have scalar commutant; the first two already suffice. -/
theorem eq_scalar_of_commute_fourierProjector
    (X : Matrix (Fin d) (Fin d) ℂ)
    (hX : ∀ (t : Fin 4) (a : ZMod d),
      X * fourierProjector d t.val a = fourierProjector d t.val a * X) :
    ∃ c : ℂ, X = c • (1 : Matrix (Fin d) (Fin d) ℂ) :=
  eq_scalar_of_commute_fourierProjector_zero_one d X (hX 0) (hX 1)

end
end CGLMPBounds
