module

public import ThreeCopyQutritWerner.CertificateHighestPivotAction

@[expose] public section


/-!
# Ordinary stabilizer actions on the original highest frames

The local carrier arrays use ordinary register permutations. Such a permutation
commutes with the signed local action when it preserves the fundamental/dual
register partition. Its coefficient action is read at the original identity
pivot rows, with the archive's inverse-permutation convention.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

/-- A register permutation moves each individual matrix-unit site. -/
theorem certificateRegisterPerm_site_action {k : ℕ} {n : Type*}
    [Fintype n] [DecidableEq n]
    (σ : Equiv.Perm (Fin k)) (s : Fin k) (i j : n) :
    (certificateRegisterPerm (n := n) σ).permMatrix ℤ * certificateSiteMatrixUnit s i j =
      certificateSiteMatrixUnit (σ s) i j * (certificateRegisterPerm σ).permMatrix ℤ := by
  apply Matrix.mulVec_injective
  funext v
  ext r
  simp only [← Matrix.mulVec_mulVec, Matrix.permMatrix_mulVec,
    Function.comp_apply, certificateSiteMatrixUnit_mulVec]
  change (if r (σ s) = i then v (Function.update (r ∘ σ) s j) else 0) =
    if r (σ s) = i then v (Function.update r (σ s) j ∘ σ) else 0
  rw [Function.update_comp_equiv]
  simp

/-- Every partition-preserving register permutation commutes with the signed action. -/
theorem certificateRegisterPerm_commutes_signed {k : ℕ} {n : Type*}
    [Fintype n] [DecidableEq n]
    (ket : Finset (Fin k)) (σ : Equiv.Perm (Fin k))
    (hσ : ∀ s, σ s ∈ ket ↔ s ∈ ket) (i j : n) :
    (certificateRegisterPerm (n := n) σ).permMatrix ℤ * certificateSignedGenerator ket i j =
      certificateSignedGenerator ket i j * (certificateRegisterPerm σ).permMatrix ℤ := by
  rw [certificateSignedGenerator, Matrix.mul_sum, Matrix.sum_mul]
  apply Fintype.sum_equiv σ _ _
  intro s
  by_cases hs : s ∈ ket
  · simp only [if_pos hs, if_pos ((hσ s).mpr hs)]
    exact certificateRegisterPerm_site_action σ s i j
  · simp only [if_neg hs, if_neg (fun h => hs ((hσ s).mp h)),
      Matrix.mul_neg, Matrix.neg_mul]
    rw [certificateRegisterPerm_site_action]

/-- Empty register transpose is the literal ordinary inverse permutation matrix. -/
theorem certificateLocalDiagram_empty {k : ℕ} {n R : Type*}
    [Fintype n] [DecidableEq n] [Zero R] [One R]
    (σ : Equiv.Perm (Fin k)) :
    certificateLocalDiagram (n := n) (R := R) ∅ σ =
      ((certificateRegisterPerm (n := n) σ)⁻¹).permMatrix R := by
  have hswap (r c : Fin k → n) : certificateWordSwap (∅ : Finset (Fin k)) r c = r := by
    funext i
    simp [certificateWordSwap]
  ext r c
  show ((certificateRegisterPerm (n := n) σ)⁻¹).permMatrix R
      (certificateWordSwap (∅ : Finset (Fin k)) r c)
      (certificateWordSwap (∅ : Finset (Fin k)) c r) = _
  rw [hswap r c, hswap c r]

/-- The archive's ordinary permutation acts on the signed physical generator. -/
theorem certificateOrdinaryRegister_commutes_generator
    (ket : Finset (Fin 6)) (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ket ↔ s ∈ ket) (i j : Fin 3) :
    certificateLocalDiagram (R := ℤ) ∅ σ * certificateLocalGenerator ket i j =
      certificateLocalGenerator ket i j * certificateLocalDiagram ∅ σ := by
  rw [certificateLocalDiagram_empty, certificateRegisterPerm_inv,
    certificateLocalGenerator_eq_signed]
  apply certificateRegisterPerm_commutes_signed
  intro s
  simpa using (hσ (σ⁻¹ s)).symm

/-- Exact scalar extension supplies the highest-space preservation premise. -/
theorem certificateOrdinaryRegister_commutes_generator_complex
    (ket : Finset (Fin 6)) (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ket ↔ s ∈ ket) (i j : Fin 3) :
    certificateLocalDiagram (R := ℂ) ∅ σ *
        (certificateLocalGenerator ket i j).map (Int.cast : ℤ → ℂ) =
      (certificateLocalGenerator ket i j).map (Int.cast : ℤ → ℂ) *
        certificateLocalDiagram ∅ σ := by
  have h := congrArg (fun M : Matrix CertificateLocalWord CertificateLocalWord ℤ =>
      M.map (Int.castRingHom ℂ))
    (certificateOrdinaryRegister_commutes_generator ket σ hσ i j)
  simp only [Matrix.map_mul (f := Int.castRingHom ℂ), certificateLocalDiagram_map] at h
  exact h

/-- Ordinary permutation multiplication has exactly one source value per entry. -/
theorem certificateOrdinaryRegister_mul_frame {m : Type*}
    (U : Matrix CertificateLocalWord m ℤ) (σ : Equiv.Perm (Fin 6))
    (r : CertificateLocalWord) (c : m) :
    (certificateLocalDiagram (n := Fin 3) (R := ℤ) ∅ σ * U : Matrix CertificateLocalWord m ℤ) r c =
      U (r ∘ ⇑(σ.symm)) c := by
  rw [certificateLocalDiagram_empty, certificateRegisterPerm_inv,
    Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul]
  rfl

/-- The sparse pivot formula reduces to literal original-frame lookup. -/
theorem certificateOrdinaryRegister_pivot_action {m : ℕ}
    (entries : List (CertificateLocalWord × Fin m × ℤ))
    (pivot : Fin m → CertificateLocalWord) (σ : Equiv.Perm (Fin 6)) :
    certificateSparsePivotAction entries pivot ∅ σ =
      (certificateMatrixFromSparseEntries entries).submatrix
        (fun r => pivot r ∘ ⇑(σ.symm)) id := by
  rw [← certificateSparsePivotAction_eq]
  ext r c
  exact certificateOrdinaryRegister_mul_frame _ σ (pivot r) c

end ThreeCopyQutritWerner
