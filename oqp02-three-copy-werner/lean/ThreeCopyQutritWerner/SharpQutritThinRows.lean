module

public import ThreeCopyQutritWerner.SharpQutritSaturationNormal
public import ThreeCopyQutritWerner.SharpQutritSingleSupportColumns
public import ThreeCopyQutritWerner.SharpSingularRangeTransport

@[expose] public section


/-!
# Constructed physical thin support of sharp qutrit extremizers

The local unitaries, normal coefficients and missing coordinate are derived
from the original matrix. Sharp equality and singularity of its actual range
reshapes imply a common two-by-two support on both row and column registers.
No normal form, exterior rank, or spectral support is supplied as a premise.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- The actual nonzero sharp extremizer has a constructed physical local
coordinate system in which both row and column supports omit one coordinate. -/
theorem sharpDoubleAnti_saturation_exists_thin_normal
    (Y : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) (hY : Y.rank ≤ 2)
    (hs : frobSq (sharpDoubleAnti Y) = frobSq Y / 2) (hpos : 0 < frobSq Y)
    (hrange : ∀ v : Fin 3 × Fin 3 → ℂ, (sharpReshape (Y *ᵥ v)).det = 0) :
    ∃ U V : Matrix (Fin 3) (Fin 3) ℂ, ∃ a : Fin 3,
      Uᴴ * U = 1 ∧ Vᴴ * V = 1 ∧
      ∀ (i j : Fin 3) (p : Fin 3 × Fin 3), i = a ∨ j = a →
        ((U ⊗ₖ V) * Y * (U ⊗ₖ V)ᵀ) (i, j) p = 0 ∧
        ((U ⊗ₖ V) * Y * (U ⊗ₖ V)ᵀ) p (i, j) = 0 := by
  obtain ⟨U, V, d, hU, hV, hd, hnormal⟩ :=
    sharpDoubleAnti_exists_qutrit_diagonal_normal Y
  have hW := sharpLocalCongruence_unitary U V hU hV
  have hQ : sharpDoubleAnti ((U ⊗ₖ V) * Y * (U ⊗ₖ V)ᵀ) =
      sharpQutritAntiEncode (Matrix.diagonal (fun i => (d i : ℂ))) := by
    rw [sharpDoubleAnti_local_congruence]
    exact hnormal
  obtain ⟨a, ha⟩ := sharpQutritDiagonal_saturation_exists_support_coordinate d hd
    ((U ⊗ₖ V) * Y * (U ⊗ₖ V)ᵀ)
    (by rwa [unitaryCongruence_rank _ _ hW]) hQ
    ((sharpDoubleAnti_equality_local_congruence U V Y hU hV).mpr hs)
    (by rwa [unitaryCongruence_frobSq _ _ hW])
    (sharpSingularRange_local_congruence U V Y hrange)
  exact ⟨U, V, a, hU, hV, ha⟩

end ThreeCopyQutritWerner
