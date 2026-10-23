module

public import CGLMPBounds.CGLMP.FourierCommutantAmplification
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section


/-!
# Dimension divisibility for reducing subspaces of the standard amplification

Appendix E.1, p.17: a reducing projection is I_d ⊗ Q, so its rank is divisible
by d. The proof derives idempotence of the multiplicity operator and uses the
proved trace/rank identity for idempotents. No integrality of trace is assumed.
The final theorem applies this to an actual rectangular isometry.
-/

open Matrix
open scoped Kronecker ComplexOrder
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

namespace CGLMPBounds
noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Trace equals ordinary matrix rank for every complex idempotent, without
requiring self-adjointness. This is the finite-dimensional projection trace theorem. -/
theorem trace_eq_rank_of_idempotent (P : Matrix ι ι ℂ) (hP : P * P = P) :
    Matrix.trace P = (P.rank : ℂ) := by
  have he : IsIdempotentElem P.toLin' := by
    change P.toLin' * P.toLin' = P.toLin'
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hP]
  calc
    Matrix.trace P = LinearMap.trace ℂ (ι → ℂ) P.toLin' :=
      (Matrix.trace_toLin'_eq P).symm
    _ = (Module.finrank ℂ (LinearMap.range P.toLin') : ℂ) :=
      LinearMap.IsProj.trace
        ((LinearMap.isProj_range_iff_isIdempotentElem P.toLin').mpr he)
    _ = (P.rank : ℂ) := rfl

variable (d : ℕ) [NeZero d]

lemma one_kronecker_injective :
    Function.Injective (fun Y : Matrix κ κ ℂ => (1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ Y) := by
  intro Y Z h
  ext k l
  have he := congrArg (fun X : Matrix (Fin d × κ) (Fin d × κ) ℂ => X (0, k) (0, l)) h
  simpa only [Matrix.kroneckerMap_apply, Matrix.one_apply_eq, one_mul] using he

/-- Idempotence descends through the identity tensor factor. -/
theorem idempotent_of_one_kronecker (Y : Matrix κ κ ℂ)
    (hY : ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ Y) * (1 ⊗ₖ Y) = 1 ⊗ₖ Y) :
    Y * Y = Y := by
  apply one_kronecker_injective d
  simpa only [← Matrix.mul_kronecker_mul, Matrix.one_mul] using hY

/-- The multiplicity matrix of an actual reducing projection is itself a
projection, and its rank gives the exact multiple of d. -/
theorem reducing_projection_multiplicity
    (X : Matrix (Fin d × κ) (Fin d × κ) ℂ)
    (hX : X.IsHermitian) (hX2 : X * X = X)
    (hcomm : ∀ (t : Fin 4) (a : ZMod d),
      X * (fourierProjector d t.val a ⊗ₖ (1 : Matrix κ κ ℂ)) =
        (fourierProjector d t.val a ⊗ₖ (1 : Matrix κ κ ℂ)) * X) :
    ∃ Y : Matrix κ κ ℂ, Y.IsHermitian ∧ Y * Y = Y ∧
      X = (1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ Y ∧ X.rank = d * Y.rank := by
  obtain ⟨Y, hY⟩ := eq_one_kronecker_of_commute_fourierProjector d X hcomm
  have hY2 : Y * Y = Y := idempotent_of_one_kronecker d Y (hY ▸ hX2)
  have hYstar : Yᴴ = Y := by
    apply one_kronecker_injective d
    have hs := hX.eq
    rw [hY, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one] at hs
    exact hs
  refine ⟨Y, hYstar, hY2, hY, ?_⟩
  have htrace : (X.rank : ℂ) = (d : ℂ) * Y.rank := by
    rw [← trace_eq_rank_of_idempotent X hX2, hY, Matrix.trace_kronecker,
      trace_eq_rank_of_idempotent Y hY2, Matrix.trace_one]
    simp
  exact_mod_cast htrace

/-- Every reducing projection of the standard amplification has rank divisible by d. -/
theorem dvd_rank_of_reducing_fourierProjector
    (X : Matrix (Fin d × κ) (Fin d × κ) ℂ)
    (hX : X.IsHermitian) (hX2 : X * X = X)
    (hcomm : ∀ (t : Fin 4) (a : ZMod d),
      X * (fourierProjector d t.val a ⊗ₖ (1 : Matrix κ κ ℂ)) =
        (fourierProjector d t.val a ⊗ₖ (1 : Matrix κ κ ℂ)) * X) :
    d ∣ X.rank := by
  obtain ⟨Y, _, _, _, hr⟩ := reducing_projection_multiplicity d X hX hX2 hcomm
  exact ⟨Y.rank, hr⟩

/-- Rank divisibility in the original dimension follows from an actual reducing
isometry; its isometry and commutation conditions are explicit matrix equations. -/
theorem dvd_dimension_of_reducing_fourier_isometry {n : ℕ}
    (W : Matrix (Fin d × κ) (Fin n) ℂ) (hW : Wᴴ * W = 1)
    (hcomm : ∀ (t : Fin 4) (a : ZMod d),
      (W * Wᴴ) * (fourierProjector d t.val a ⊗ₖ (1 : Matrix κ κ ℂ)) =
        (fourierProjector d t.val a ⊗ₖ (1 : Matrix κ κ ℂ)) * (W * Wᴴ)) :
    d ∣ n := by
  have hW2 : (W * Wᴴ) * (W * Wᴴ) = W * Wᴴ := by
    calc
      (W * Wᴴ) * (W * Wᴴ) = W * (Wᴴ * W) * Wᴴ := by simp only [Matrix.mul_assoc]
      _ = W * Wᴴ := by rw [hW, Matrix.mul_one]
  have hdim : (W * Wᴴ).rank = n := by
    rw [Matrix.rank_self_mul_conjTranspose, ← Matrix.rank_conjTranspose_mul_self W, hW,
      Matrix.rank_one, Fintype.card_fin]
  simpa only [hdim] using dvd_rank_of_reducing_fourierProjector d (W * Wᴴ)
    (Matrix.isHermitian_mul_conjTranspose_self W) hW2 hcomm

end
end CGLMPBounds
