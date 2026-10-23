module

public import ThreeCopyQutritWerner.CertificateSparseDiagramAction

@[expose] public section


/-!
# Recovering the original pivot action from actual source invariance

Once source invariance is proved by the highest-kernel certificates, the
original identity rows recover its unique coefficient action. Thus the sparse
pivot formula determines the full physical action and its original compression.
This closes the action premise in the sparse checker without adding a table
correctness assumption.
-/

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

/-- An identity-row submatrix recovers the unique action on the source columns. -/
theorem certificateFrame_action_eq_pivot {n m R : Type*}
    [Fintype n] [Fintype m] [DecidableEq m] [Semiring R]
    (U : Matrix n m R) (pivot : m → n) (hp : U.submatrix pivot id = 1)
    (M : Matrix n n R) (A : Matrix m m R) (hact : M * U = U * A) :
    M * U = U * ((M * U).submatrix pivot id) := by
  have hA : (M * U).submatrix pivot id = A := by
    rw [hact]
    change U.submatrix pivot id * A = A
    rw [hp, Matrix.one_mul]
  rw [hA]
  exact hact

/-- Identity rows are unchanged under exact integer-to-complex scalar extension. -/
theorem certificateIntFrame_pivots_complex {n m : Type*}
    [DecidableEq m] (U : Matrix n m ℤ) (pivot : m → n)
    (hp : U.submatrix pivot id = 1) :
    (U.map (Int.cast : ℤ → ℂ)).submatrix pivot id = 1 := by
  ext i j
  have h : U (pivot i) j = (1 : Matrix m m ℤ) i j := congrFun (congrFun hp i) j
  simp only [Matrix.submatrix_apply, Matrix.map_apply, id_eq, h]
  simp [Matrix.one_apply]

/-- Equality of the complex physical actions reflects to the integer actions. -/
theorem certificateIntFrame_action_of_complex {n m : Type*} [Fintype n] [Fintype m]
    (M : Matrix n n ℤ) (U : Matrix n m ℤ) (A : Matrix m m ℤ)
    (h : M.map (Int.cast : ℤ → ℂ) * U.map (Int.cast : ℤ → ℂ) =
      U.map (Int.cast : ℤ → ℂ) * A.map (Int.cast : ℤ → ℂ)) :
    M * U = U * A := by
  ext i j
  have he : ((M * U) i j : ℂ) = ((U * A) i j : ℂ) := by
    simpa [Matrix.mul_apply] using congrFun (congrFun h i) j
  exact_mod_cast he

/-- Actual complex source invariance discharges the sparse integer action premise. -/
theorem certificateSparsePivotAction_source_action_of_complex {m : ℕ}
    (entries : List (CertificateLocalWord × Fin m × ℤ))
    (pivot : Fin m → CertificateLocalWord)
    (hp : (certificateMatrixFromSparseEntries entries).submatrix pivot id = 1)
    (S : Finset (Fin 6)) (σ : Equiv.Perm (Fin 6))
    (hsource : ∃ A : Matrix (Fin m) (Fin m) ℂ,
      certificateLocalDiagram (R := ℂ) S σ *
        (certificateMatrixFromSparseEntries entries).map (Int.cast : ℤ → ℂ) =
      (certificateMatrixFromSparseEntries entries).map (Int.cast : ℤ → ℂ) * A) :
    certificateLocalDiagram S σ * certificateMatrixFromSparseEntries entries =
      certificateMatrixFromSparseEntries entries * certificateSparsePivotAction entries pivot S σ := by
  obtain ⟨A, hA⟩ := hsource
  let U := certificateMatrixFromSparseEntries entries
  let M : Matrix CertificateLocalWord CertificateLocalWord ℤ := certificateLocalDiagram S σ
  have hmap : M.map (Int.cast : ℤ → ℂ) = certificateLocalDiagram S σ :=
    certificateLocalDiagram_map (Int.castRingHom ℂ) S σ
  have hpC := certificateIntFrame_pivots_complex U pivot hp
  have hact : M.map (Int.cast : ℤ → ℂ) * U.map (Int.cast : ℤ → ℂ) =
      U.map (Int.cast : ℤ → ℂ) * A := by
    rw [hmap]
    exact hA
  have hpivot := certificateFrame_action_eq_pivot (U.map (Int.cast : ℤ → ℂ))
    pivot hpC (M.map (Int.cast : ℤ → ℂ)) A hact
  have htable : (M.map (Int.cast : ℤ → ℂ) * U.map (Int.cast : ℤ → ℂ)).submatrix pivot id =
      (certificateSparsePivotAction entries pivot S σ).map (Int.cast : ℤ → ℂ) := by
    have h := congrArg (fun B : Matrix (Fin m) (Fin m) ℤ => B.map (Int.castRingHom ℂ))
      (certificateSparsePivotAction_eq entries pivot S σ)
    change ((M * U).map (Int.castRingHom ℂ)).submatrix pivot id = _ at h
    rw [Matrix.map_mul] at h
    exact h
  rw [htable] at hpivot
  exact certificateIntFrame_action_of_complex M U _ hpivot

end ThreeCopyQutritWerner
