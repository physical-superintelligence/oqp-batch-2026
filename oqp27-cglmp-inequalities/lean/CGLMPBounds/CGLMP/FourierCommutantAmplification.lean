module

public import CGLMPBounds.CGLMP.FourierCommutantStandard

@[expose] public section


/-!
# The commutant of the standard amplification in product coordinates

Appendix E.1, p. 17: the joint commutant of `Π_a^t ⊗ I` is `I ⊗ M`.
Taking each pair of multiplicity coordinates gives an operator on the first
factor. The actual standard commutant theorem makes every such slice scalar.
-/

open Matrix
open scoped Kronecker
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

namespace CGLMPBounds
noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Fix the two multiplicity coordinates, leaving a matrix on the first factor. -/
def multiplicitySlice (X : Matrix (ι × κ) (ι × κ) ℂ) (k l : κ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => X (i, k) (j, l)

theorem multiplicitySlice_mul_kronecker_one
    (X : Matrix (ι × κ) (ι × κ) ℂ) (P : Matrix ι ι ℂ) (k l : κ) :
    multiplicitySlice (X * (P ⊗ₖ (1 : Matrix κ κ ℂ))) k l =
      multiplicitySlice X k l * P := by
  ext i j
  simp [multiplicitySlice, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.one_apply, mul_ite, ite_mul]

theorem multiplicitySlice_kronecker_one_mul
    (X : Matrix (ι × κ) (ι × κ) ℂ) (P : Matrix ι ι ℂ) (k l : κ) :
    multiplicitySlice ((P ⊗ₖ (1 : Matrix κ κ ℂ)) * X) k l =
      P * multiplicitySlice X k l := by
  ext i j
  simp [multiplicitySlice, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.one_apply, mul_ite, ite_mul]

theorem multiplicitySlice_commute_of_commute_kronecker_one
    (X : Matrix (ι × κ) (ι × κ) ℂ) (P : Matrix ι ι ℂ)
    (h : X * (P ⊗ₖ (1 : Matrix κ κ ℂ)) = (P ⊗ₖ (1 : Matrix κ κ ℂ)) * X)
    (k l : κ) : multiplicitySlice X k l * P = P * multiplicitySlice X k l := by
  have hs := congrArg (fun Y => multiplicitySlice Y k l) h
  simpa only [multiplicitySlice_mul_kronecker_one,
    multiplicitySlice_kronecker_one_mul] using hs

variable (d : ℕ) [NeZero d]

/-- Every operator commuting with the actual amplified standard PVMs acts only
on the multiplicity factor. The multiplicity type may be empty. -/
theorem eq_one_kronecker_of_commute_fourierProjector
    (X : Matrix (Fin d × κ) (Fin d × κ) ℂ)
    (hX : ∀ (t : Fin 4) (a : ZMod d),
      X * (fourierProjector d t.val a ⊗ₖ (1 : Matrix κ κ ℂ)) =
        (fourierProjector d t.val a ⊗ₖ (1 : Matrix κ κ ℂ)) * X) :
    ∃ Y : Matrix κ κ ℂ, X = (1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ Y := by
  refine ⟨Matrix.of (fun k l => X (0, k) (0, l)), ?_⟩
  ext ⟨i, k⟩ ⟨j, l⟩
  obtain ⟨c, hc⟩ := eq_scalar_of_commute_fourierProjector d (multiplicitySlice X k l)
    (fun t a => multiplicitySlice_commute_of_commute_kronecker_one X _ (hX t a) k l)
  have hzero : X (0, k) (0, l) = c := by
    have h := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M 0 0) hc
    simpa [multiplicitySlice] using h
  have hij := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M i j) hc
  change X (i, k) (j, l) = (1 : Matrix (Fin d) (Fin d) ℂ) i j * X (0, k) (0, l)
  calc
    X (i, k) (j, l) = c * (1 : Matrix (Fin d) (Fin d) ℂ) i j := by
      simpa [multiplicitySlice] using hij
    _ = (1 : Matrix (Fin d) (Fin d) ℂ) i j * X (0, k) (0, l) := by
      rw [hzero, mul_comm]

/-- Exact joint-commutant characterization, including its elementary converse. -/
theorem commute_fourierProjector_kronecker_iff
    (X : Matrix (Fin d × κ) (Fin d × κ) ℂ) :
    (∀ (t : Fin 4) (a : ZMod d),
      X * (fourierProjector d t.val a ⊗ₖ (1 : Matrix κ κ ℂ)) =
        (fourierProjector d t.val a ⊗ₖ (1 : Matrix κ κ ℂ)) * X) ↔
      ∃ Y : Matrix κ κ ℂ, X = (1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ Y := by
  constructor
  · exact eq_one_kronecker_of_commute_fourierProjector d X
  · rintro ⟨Y, rfl⟩ t a
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp

end
end CGLMPBounds
