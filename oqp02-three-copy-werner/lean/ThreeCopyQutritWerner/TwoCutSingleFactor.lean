module

public import ThreeCopyQutritWerner.TwoCutSingleOutputFactor
public import ThreeCopyQutritWerner.TwoCutLocalConjugation
public import ThreeCopyQutritWerner.BinaryPartitionEmbedding

@[expose] public section


/-!
# The original single-output-direction cut zero

The constructed direction is rotated to one coordinate, classified there,
then the exact unitary conjugation is undone on both ket-bra vectors. The
second-site rank-two projection is the same input and output projection.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- An actual single first-site output direction forces a literal ket-bra
tensor an orthogonal rank-two projection in the original coordinates. -/
theorem cutForm_zero_single_output_factor
    {d : Type*} [Fintype d] [DecidableEq d]
    (C : Matrix (Fin 3 × d) (Fin 3 × d) ℂ) (hC : C.rank ≤ 2)
    (hz : cutForm C = 0) (hne : C ≠ 0) (i₀ : Fin 3) (x : Fin 3 → ℂ)
    (hx : x i₀ = 1) (hfactor : ∀ i r q, C (i, r) q = x i * C (i₀, r) q) :
    ∃ (u v : Fin 3 → ℂ) (P : Matrix d d ℂ),
      vecNormSq u = 1 ∧ v ≠ 0 ∧ P.IsHermitian ∧ P * P = P ∧ P.rank = 2 ∧
        C = ketBra u v ⊗ₖ P := by
  obtain ⟨U, hU, hrow⟩ := twoCut_single_output_exists_unitary_coordinate C i₀ x hx hfactor
  let W := U ⊗ₖ (1 : Matrix d d ℂ)
  let D := W * C * Wᴴ
  have hI : (1 : Matrix d d ℂ)ᴴ * 1 = 1 := by simp
  have hW : Wᴴ * W = 1 := kron_isometry U 1 hU hI
  have hdata := twoCut_local_conj_data U (1 : Matrix d d ℂ) hU hI C
  have hDne : D ≠ 0 := by
    intro h
    apply hne
    have he := twoCut_unitary_conj_recover W C hW
    change Wᴴ * D * W = C at he
    simpa only [h, Matrix.mul_zero, Matrix.zero_mul] using he.symm
  obtain ⟨b, P, hb, hP, hPP, hPr, hDf⟩ :=
    cutForm_zero_single_output_coordinate_factor D (hdata.1.trans_le hC)
      (hdata.2.2.trans hz) hDne 0 hrow
  have hUU : U * Uᴴ = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin 3))).mp hU
  have hUH : (Uᴴ)ᴴ * Uᴴ = 1 := by
    simpa only [Matrix.conjTranspose_conjTranspose] using hUU
  let e : Fin 3 → ℂ := fun i => if i = 0 then 1 else 0
  have heN : vecNormSq e = 1 := by simp [vecNormSq, e]
  refine ⟨Uᴴ *ᵥ e, Uᴴ *ᵥ b, P, ?_, ?_, hP, hPP, hPr, ?_⟩
  · exact (binaryPartition_isometry_vecNormSq Uᴴ hUH e).trans heN
  · intro hv
    apply hb
    have he := congrArg (fun z => U *ᵥ z) hv
    simpa only [Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec, Matrix.mulVec_zero] using he
  · calc
      C = Wᴴ * D * W := (twoCut_unitary_conj_recover W C hW).symm
      _ = Wᴴ * (ketBra e b ⊗ₖ P) * W := by rw [hDf]
      _ = (Uᴴ * ketBra e b * U) ⊗ₖ P := by
        simp only [W, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
          ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
      _ = ketBra (Uᴴ *ᵥ e) (Uᴴ *ᵥ b) ⊗ₖ P := by
        have he := binaryPartition_conj_ketBra Uᴴ e b
        simpa only [Matrix.conjTranspose_conjTranspose] using
          congrArg (fun A => A ⊗ₖ P) he

end ThreeCopyQutritWerner
