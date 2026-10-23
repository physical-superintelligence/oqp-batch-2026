module

public import ThreeCopyQutritWerner.SharpFixedPairAnnihilator
public import ThreeCopyQutritWerner.SharpCoordinatePlane

@[expose] public section


/-!
# Actual binary frames for thin qutrit column spaces

A thin rectangular matrix has a constructed unitary missing row, obtained
from its actual Gram matrix. The complement of that coordinate gives a
literal two-column isometry fixing the original matrix on the left.
-/

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace ThreeCopyQutritWerner

/-- A rectangular qutrit matrix of rank at most two has an actual unitary
missing row, including rank zero and one. -/
theorem qutrit_rank_le_two_exists_unitary_zero_row
    {n : Type*} [Fintype n] (A : Matrix (Fin 3) n ℂ) (hA : A.rank ≤ 2) :
    ∃ U : Matrix (Fin 3) (Fin 3) ℂ, ∃ a : Fin 3,
      Uᴴ * U = 1 ∧ ∀ j, (U * A) a j = 0 := by
  obtain ⟨U, a, hU, ha⟩ := sharpQutrit_rank_le_two_exists_unitary_zero_row (A * Aᴴ)
    (by rwa [Matrix.rank_self_mul_conjTranspose])
  refine ⟨U, a, hU, ?_⟩
  have hg : (U * A) * (U * A)ᴴ = (U * (A * Aᴴ)) * Uᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hz : ((U * A) * (U * A)ᴴ) a a = 0 := by
    rw [hg, Matrix.mul_apply]
    simp only [ha, zero_mul, Finset.sum_const_zero]
  have hr : (fun j => (U * A) a j) = 0 := by
    apply dotProduct_self_star_eq_zero.mp
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct, Pi.star_apply] using hz
  intro j
  exact congrFun hr j

/-- Literal inclusion of the two coordinates other than a. -/
def qutritPlaneInclusion (a : Fin 3) : Matrix (Fin 3) (Fin 2) ℂ :=
  fun i j => if i = a.succAbove j then 1 else 0

theorem qutritPlaneInclusion_isometry (a : Fin 3) :
    (qutritPlaneInclusion a)ᴴ * qutritPlaneInclusion a = 1 := by
  have hs : (2 : Fin 3).succAbove (1 : Fin 2) = 1 := by decide
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    norm_num [qutritPlaneInclusion, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Fin.sum_univ_three, hs]

theorem qutritPlaneInclusion_projection (a : Fin 3) :
    qutritPlaneInclusion a * (qutritPlaneInclusion a)ᴴ = sharpCoordinatePlaneProjection a := by
  have hs : (2 : Fin 3).succAbove (1 : Fin 2) = 1 := by decide
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    norm_num [qutritPlaneInclusion, sharpCoordinatePlaneProjection,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply, Fin.sum_univ_two, hs]

/-- Every actual thin qutrit column space is fixed by a constructed binary
isometry. No chosen support or orthonormal frame is assumed. -/
theorem qutrit_rank_le_two_exists_binary_frame
    {n : Type*} [Fintype n] (A : Matrix (Fin 3) n ℂ) (hA : A.rank ≤ 2) :
    ∃ J : Matrix (Fin 3) (Fin 2) ℂ, Jᴴ * J = 1 ∧ J * Jᴴ * A = A := by
  obtain ⟨U, a, hU, ha⟩ := qutrit_rank_le_two_exists_unitary_zero_row A hA
  have hUU : U * Uᴴ = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin 3))).mp hU
  refine ⟨Uᴴ * qutritPlaneInclusion a, ?_, ?_⟩
  · simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U Uᴴ, hUU, Matrix.one_mul, qutritPlaneInclusion_isometry]
  · calc
      _ = Uᴴ * ((qutritPlaneInclusion a * (qutritPlaneInclusion a)ᴴ) * (U * A)) := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.mul_assoc]
      _ = Uᴴ * (U * A) := by
        rw [qutritPlaneInclusion_projection, sharpCoordinatePlaneProjection_mul _ a ha]
      _ = A := by rw [← Matrix.mul_assoc, hU, Matrix.one_mul]

end ThreeCopyQutritWerner
