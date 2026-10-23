module

public import ThreeCopyQutritWerner.BinaryPartitionCoordinates
public import ThreeCopyQutritWerner.TwoCutTransport

@[expose] public section


/-!
# The original spin transform in each partition placement

Permuting the three identical epsilon factors preserves the literal spin
matrix. The full-word partition equations therefore identify the spin
transform of the actually permuted original C, without an additional unitary
or a change of transpose convention.
-/

noncomputable section

open scoped Matrix Kronecker

namespace ThreeCopyQutritWerner

theorem binaryPartitionSiteTuple_spin (i : Fin 3) :
    epsJ₃.submatrix (binaryPartitionSiteTuple i) (binaryPartitionSiteTuple i) = epsJ₃ := by
  ext a b
  fin_cases i <;>
    simp [binaryPartitionSiteTuple, siteEquiv₂, siteEquiv₃,
      Matrix.submatrix_apply, epsJ₃, Matrix.kroneckerMap_apply] <;> ring

theorem binaryPartitionSiteTuple_spin_transpose (i : Fin 3) :
    epsJ₃ᵀ.submatrix (binaryPartitionSiteTuple i) (binaryPartitionSiteTuple i) = epsJ₃ᵀ := by
  have h := congrArg Matrix.transpose (binaryPartitionSiteTuple_spin i)
  simpa only [Matrix.transpose_submatrix] using h

theorem binaryPartitionSiteWord_spin_original
    (C : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ) (i : Fin 3) :
    (binaryThreeWordMatrix (C * epsJ₃ᵀ)).submatrix
        (binaryPartitionSiteWord i) (binaryPartitionSiteWord i) =
      C.submatrix (binaryPartitionSiteTuple i) (binaryPartitionSiteTuple i) * epsJ₃ᵀ := by
  have he : (binaryThreeWordMatrix (C * epsJ₃ᵀ)).submatrix
      (binaryPartitionSiteWord i) (binaryPartitionSiteWord i) =
        (C * epsJ₃ᵀ).submatrix (binaryPartitionSiteTuple i) (binaryPartitionSiteTuple i) := by
    ext a b
    simp [binaryThreeWordMatrix, binaryPartitionSiteWord]
  rw [he]
  calc
    (C * epsJ₃ᵀ).submatrix (binaryPartitionSiteTuple i) (binaryPartitionSiteTuple i) =
        C.submatrix (binaryPartitionSiteTuple i) (binaryPartitionSiteTuple i) *
          epsJ₃ᵀ.submatrix (binaryPartitionSiteTuple i) (binaryPartitionSiteTuple i) :=
      (Matrix.submatrix_mul_equiv C epsJ₃ᵀ (binaryPartitionSiteTuple i)
        (binaryPartitionSiteTuple i) (binaryPartitionSiteTuple i)).symm
    _ = _ := by rw [binaryPartitionSiteTuple_spin_transpose]

/-- The selected original placement keeps both exact rank and normalization. -/
theorem binaryPartitionSiteTuple_rank_frob
    (C : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ) (i : Fin 3) :
    (C.submatrix (binaryPartitionSiteTuple i) (binaryPartitionSiteTuple i)).rank = C.rank ∧
      frobSq (C.submatrix (binaryPartitionSiteTuple i) (binaryPartitionSiteTuple i)) =
        frobSq C :=
  ⟨Matrix.rank_submatrix C (binaryPartitionSiteTuple i) (binaryPartitionSiteTuple i),
    frobSq_submatrix_equiv (binaryPartitionSiteTuple i) C⟩

end ThreeCopyQutritWerner
