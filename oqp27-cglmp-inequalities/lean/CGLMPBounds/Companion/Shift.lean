module

public import CGLMPBounds.Companion.Covariance

@[expose] public section


/-! # Outcome shift and its commutation with the covariance unitaries -/

open Matrix
namespace CGLMPBounds.Companion
noncomputable section

variable {d n : ℕ} [NeZero d]

/-- The block permutation for `J |a⟩ = |a−1⟩`; its nonzero entry in row `a` is column `a+1`. -/
def shiftBlocks : Blocks d n :=
  (Equiv.addRight (1 : ZMod d)).permMatrix (Base n)

/-- The source's `J ⊗ I_n`. -/
def shift : OutcomeMat d n := flatten (shiftBlocks (d := d) (n := n))

lemma shiftBlocks_star_mul :
    (shiftBlocks (d := d) (n := n))ᴴ * shiftBlocks = 1 := by
  simp only [shiftBlocks, Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul,
    mul_inv_cancel, Matrix.permMatrix_one]

lemma shiftBlocks_mul_star :
    shiftBlocks (d := d) (n := n) * (shiftBlocks)ᴴ = 1 := by
  simp only [shiftBlocks, Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul,
    inv_mul_cancel, Matrix.permMatrix_one]

lemma shift_star_mul : (shift (d := d) (n := n))ᴴ * shift = 1 := by
  simpa only [map_mul, map_one, flatten_star, shift] using
    congrArg (flatten (d := d) (n := n)) (shiftBlocks_star_mul (d := d) (n := n))

lemma shift_mul_star : shift (d := d) (n := n) * (shift)ᴴ = 1 := by
  simpa only [map_mul, map_one, flatten_star, shift] using
    congrArg (flatten (d := d) (n := n)) (shiftBlocks_mul_star (d := d) (n := n))

lemma shiftBlocks_commutes (P : ZMod d → Base n) :
    Commute (shiftBlocks (d := d) (n := n)) (conjugatorBlocks P) := by
  change shiftBlocks * conjugatorBlocks P = conjugatorBlocks P * shiftBlocks
  unfold shiftBlocks Equiv.Perm.permMatrix
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  apply Matrix.ext
  intro a b
  simp only [Matrix.submatrix_apply, conjugatorBlocks, Equiv.coe_addRight,
    Equiv.addRight_symm, id_eq]
  congr 1
  abel

/-- The source's `Z_t` commutes with the outcome shift, even before imposing PVM axioms. -/
theorem shift_commutes (P : ZMod d → Base n) :
    Commute (shift (d := d) (n := n)) (conjugator P) := by
  change shift * conjugator P = conjugator P * shift
  simpa only [map_mul, shift, conjugator] using
    congrArg (flatten (d := d) (n := n)) (shiftBlocks_commutes P).eq

lemma shiftBlocks_computational (b : ZMod d) :
    shiftBlocks (d := d) (n := n) * computationalBlocks b * (shiftBlocks)ᴴ =
      computationalBlocks (b - 1) := by
  simp only [shiftBlocks, Matrix.conjTranspose_permMatrix]
  unfold Equiv.Perm.permMatrix
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  apply Matrix.ext
  intro k l
  simp only [Matrix.submatrix_apply, Equiv.Perm.inv_def, Equiv.symm_symm,
    Equiv.coe_addRight, id_eq, computationalBlocks, Matrix.diagonal_apply,
    add_left_inj, eq_sub_iff_add_eq]

/-- The closing twist sends the outcome projector at `b` to the one at `b−1`. -/
theorem shift_computational (b : ZMod d) :
    shift (d := d) (n := n) * computational b * (shift)ᴴ = computational (b - 1) := by
  simpa only [map_mul, flatten_star, shift, computational] using
    congrArg (flatten (d := d) (n := n)) (shiftBlocks_computational (n := n) b)

/-- Bundle the proved covariance matrix as a unitary. -/
def unitaryConjugator (P : ZMod d → Base n) (hP : IsPVM P) :
    Matrix.unitaryGroup (OutcomeSpace d n) ℂ :=
  ⟨conjugator P, conjugator_star_mul P hP, conjugator_mul_star P hP⟩

/-- Bundle the outcome shift as a unitary. -/
def unitaryShift : Matrix.unitaryGroup (OutcomeSpace d n) ℂ :=
  ⟨shift, shift_star_mul, shift_mul_star⟩

lemma unitaryShift_commutes (P : ZMod d → Base n) (hP : IsPVM P) :
    Commute (unitaryShift (d := d) (n := n)) (unitaryConjugator P hP) := by
  apply Subtype.ext
  exact (shift_commutes P).eq

end
end CGLMPBounds.Companion
