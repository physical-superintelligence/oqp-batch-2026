module

public import CGLMPBounds.Companion.CutStandardizationBasis
public import CGLMPBounds.Circulation.CutDiagonalization

@[expose] public section


/-!
# Zero forbidden mass standardizes the actual companion clock PVMs

The common cut diagonalization is derived from the original tuple, its unitary
and fourth-power identities, and the literal zero forbidden mass. It is not an
oracle hypothesis. The common standardizer is constructed in product coordinates.
-/

open Matrix
open scoped Kronecker
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

namespace CGLMPBounds.Companion
noncomputable section

variable {d r : ℕ} [NeZero d] [NeZero r]

/-- E.1 through standard amplification, before restricting to the original
reducing summand. Both the input tuple and output B.2 projectors are literal. -/
theorem exists_standardization_of_forbidden_zero
    (V : Fin d → Circulation.Mat r)
    (hunit : ∀ j, (V j)ᴴ * V j = 1) (hfour : ∀ j, V j ^ 4 = 1)
    (hzero : scalarForbiddenTotal V = 0) :
    ∃ U : Matrix (ZMod d × Fin r) (Fin d × Fin r) ℂ,
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      ∀ (t : Fin 4) (b : ZMod d),
        blockClockMeasurement (blockFourierOperator (fun j => sourcePhase j • V j)) t.val b =
          U * (fourierProjector d t.val b ⊗ₖ (1 : Circulation.Mat r)) * Uᴴ := by
  obtain ⟨Q, a, j₀, hQ, hQ', hV⟩ :=
    Circulation.exists_unitary_cut_diagonalization V hunit hfour hzero
  refine ⟨cutBasisStandardizer Q j₀, cutBasisStandardizer_star_mul Q hQ j₀,
    cutBasisStandardizer_mul_star Q hQ' j₀, ?_⟩
  intro t b
  exact blockMeasurement_standard_of_cut_diagonalization V Q hQ hQ' a j₀ hV t.val b

end
end CGLMPBounds.Companion
