module

public import ThreeCopyQutritWerner.CertificateDiagramOperators

@[expose] public section


/-!
# Physical weight spaces and preservation of highest vectors

The Cartan generators are the literal signed diagonal weights on all 729 words.
Their joint eigenspace is exactly support on the selected weight. The final
restriction lemma transports the physical raising equations to any finite list
of tested output rows, provided the input list covers the entire weight space.
No highest-weight dimension or irreducibility theorem is assumed.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

/-- A diagonal site matrix unit tests the local digit. -/
theorem certificateSiteMatrixUnit_self {k : ℕ} {n : Type*} [Fintype n]
    [DecidableEq n] (s : Fin k) (i : n) :
    certificateSiteMatrixUnit s i i =
      Matrix.diagonal (fun w : Fin k → n => if w s = i then (1 : ℤ) else 0) := by
  ext r c
  by_cases hrc : r = c
  · subst r
    simp [certificateSiteMatrixUnit, Matrix.diagonal_apply,
      Function.update_eq_self_iff, eq_comm]
  · by_cases hc : c s = i
    · have hu : Function.update c s i = c := by rw [← hc, Function.update_eq_self]
      simp [certificateSiteMatrixUnit, Matrix.diagonal_apply, hrc, hc, hu, Ne.symm hrc]
    · simp [certificateSiteMatrixUnit, Matrix.diagonal_apply, hrc, hc]

/-- Every physical Cartan matrix is exactly the signed weight diagonal. -/
theorem certificateLocalGenerator_cartan (ket : Finset (Fin 6)) (i : Fin 3) :
    certificateLocalGenerator ket i i =
      Matrix.diagonal (fun w => certificateLocalWeight ket w i) := by
  rw [certificateLocalGenerator_eq_signed, certificateSignedGenerator]
  ext r c
  by_cases hrc : r = c
  · subst c
    simp only [Matrix.sum_apply, certificateSiteMatrixUnit_self, Matrix.ite_apply,
      Matrix.neg_apply, Matrix.diagonal_apply_eq, certificateLocalWeight]
    apply Finset.sum_congr rfl
    intro s _
    by_cases hs : s ∈ ket <;> by_cases hi : r s = i <;> simp [hs, hi]
  · rw [Matrix.diagonal_apply_ne _ hrc]
    simp only [Matrix.sum_apply, certificateSiteMatrixUnit_self]
    apply Finset.sum_eq_zero
    intro s _
    by_cases hs : s ∈ ket <;>
      simp [hs, Matrix.diagonal_apply, hrc]

theorem certificateLocalGenerator_cartan_complex (ket : Finset (Fin 6)) (i : Fin 3) :
    (certificateLocalGenerator ket i i).map (Int.cast : ℤ → ℂ) =
      Matrix.diagonal (fun w => (certificateLocalWeight ket w i : ℂ)) := by
  rw [certificateLocalGenerator_cartan]
  ext r c
  simp [Matrix.map_apply, Matrix.diagonal_apply]

/-- Literal support in the physical signed-weight subspace. -/
def certificateHasWeight (ket : Finset (Fin 6)) (lam : Fin 3 → ℤ)
    (v : CertificateLocalWord → ℂ) : Prop :=
  ∀ w, certificateLocalWeight ket w ≠ lam → v w = 0

/-- Joint Cartan eigenvectors are exactly vectors supported on the declared weight. -/
theorem certificateHasWeight_iff_cartan (ket : Finset (Fin 6)) (lam : Fin 3 → ℤ)
    (v : CertificateLocalWord → ℂ) :
    certificateHasWeight ket lam v ↔ ∀ i : Fin 3,
      (certificateLocalGenerator ket i i).map (Int.cast : ℤ → ℂ) *ᵥ v = (lam i : ℂ) • v := by
  simp only [certificateLocalGenerator_cartan_complex]
  constructor
  · intro hv i
    ext w
    by_cases hw : certificateLocalWeight ket w = lam
    · simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, hw, Pi.smul_apply, smul_eq_mul]
    · simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, hv w hw,
        Pi.smul_apply, smul_eq_mul]
  · intro hv w hw
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
    have he := congrFun (hv i) w
    have he' : (certificateLocalWeight ket w i : ℂ) * v w = (lam i : ℂ) * v w := by
      simpa [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, Pi.smul_apply, smul_eq_mul] using he
    by_contra hn
    have hc : (certificateLocalWeight ket w i : ℂ) = (lam i : ℂ) := mul_right_cancel₀ hn he'
    exact hi (by exact_mod_cast hc)

/-- Commutation with all Cartan matrices preserves the exact physical weight support. -/
theorem certificateHasWeight_mulVec (ket : Finset (Fin 6)) (lam : Fin 3 → ℤ)
    (M : Matrix CertificateLocalWord CertificateLocalWord ℂ)
    (hcomm : ∀ i : Fin 3,
      M * (certificateLocalGenerator ket i i).map (Int.cast : ℤ → ℂ) =
        (certificateLocalGenerator ket i i).map (Int.cast : ℤ → ℂ) * M)
    (v : CertificateLocalWord → ℂ) (hv : certificateHasWeight ket lam v) :
    certificateHasWeight ket lam (M *ᵥ v) := by
  apply (certificateHasWeight_iff_cartan ket lam _).mpr
  intro i
  have he := (certificateHasWeight_iff_cartan ket lam v).mp hv i
  rw [Matrix.mulVec_mulVec, ← hcomm i, ← Matrix.mulVec_mulVec, he, Matrix.mulVec_smul]

/-- The exact highest-vector condition, with both actual simple raising operators. -/
def certificateIsHighest (ket : Finset (Fin 6)) (lam : Fin 3 → ℤ)
    (v : CertificateLocalWord → ℂ) : Prop :=
  certificateHasWeight ket lam v ∧
    (certificateLocalGenerator ket 0 1).map (Int.cast : ℤ → ℂ) *ᵥ v = 0 ∧
    (certificateLocalGenerator ket 1 2).map (Int.cast : ℤ → ℂ) *ᵥ v = 0

/-- An operator in the literal generator commutant preserves every highest-vector space. -/
theorem certificateIsHighest_mulVec (ket : Finset (Fin 6)) (lam : Fin 3 → ℤ)
    (M : Matrix CertificateLocalWord CertificateLocalWord ℂ)
    (hcomm : ∀ i j : Fin 3,
      M * (certificateLocalGenerator ket i j).map (Int.cast : ℤ → ℂ) =
        (certificateLocalGenerator ket i j).map (Int.cast : ℤ → ℂ) * M)
    (v : CertificateLocalWord → ℂ) (hv : certificateIsHighest ket lam v) :
    certificateIsHighest ket lam (M *ᵥ v) := by
  refine ⟨certificateHasWeight_mulVec ket lam M (fun i => hcomm i i) v hv.1, ?_, ?_⟩
  · rw [Matrix.mulVec_mulVec, ← hcomm 0 1, ← Matrix.mulVec_mulVec, hv.2.1,
      Matrix.mulVec_zero]
  · rw [Matrix.mulVec_mulVec, ← hcomm 1 2, ← Matrix.mulVec_mulVec, hv.2.2,
      Matrix.mulVec_zero]

/-- All diagram coefficients preserve the highest spaces for the PT complement. -/
theorem certificateDiagramCombination_highest (S : Finset (Fin 6))
    (weight : Equiv.Perm (Fin 6) → ℂ) (lam : Fin 3 → ℤ)
    (v : CertificateLocalWord → ℂ) (hv : certificateIsHighest Sᶜ lam v) :
    certificateIsHighest Sᶜ lam (certificateLocalDiagramCombination S weight *ᵥ v) := by
  apply certificateIsHighest_mulVec _ _ _ _ _ hv
  intro i j
  apply certificateDiagramCombination_commutes_of_each
  intro σ
  exact certificateLocalDiagram_generator_complex S σ i j

/-- The same conclusion in the complementary sector-0 source convention. -/
theorem certificateDiagramCombination_complement_highest (S : Finset (Fin 6))
    (weight : Equiv.Perm (Fin 6) → ℂ) (lam : Fin 3 → ℤ)
    (v : CertificateLocalWord → ℂ) (hv : certificateIsHighest S lam v) :
    certificateIsHighest S lam (certificateLocalDiagramCombination S weight *ᵥ v) := by
  apply certificateIsHighest_mulVec _ _ _ _ _ hv
  intro i j
  apply certificateDiagramCombination_commutes_of_each
  intro σ
  exact certificateLocalDiagram_complement_generator_complex S σ i j

/-- Restricting a supported vector's input sum to an injective covering list is exact. -/
theorem certificateRestrictedAction {n a b : Type*} [Fintype n] [Fintype b]
    (row : b → n) (hrow : Function.Injective row)
    (M : Matrix a n ℂ) (v : n → ℂ) (hv : ∀ w ∉ Set.range row, v w = 0) :
    (M.submatrix id row) *ᵥ (v ∘ row) = M *ᵥ v := by
  ext r
  simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id_eq, Function.comp_apply]
  apply Fintype.sum_of_injective row hrow _ _
  · intro w hw
    rw [hv w hw, mul_zero]
  · intro b
    rfl

/-- Covering the physical weight is enough to cover the support of a highest vector. -/
theorem certificateHasWeight_support_rows {b : Type*} (ket : Finset (Fin 6))
    (lam : Fin 3 → ℤ) (row : b → CertificateLocalWord)
    (hcover : ∀ w, certificateLocalWeight ket w = lam → w ∈ Set.range row)
    (v : CertificateLocalWord → ℂ) (hv : certificateHasWeight ket lam v) :
    ∀ w ∉ Set.range row, v w = 0 := by
  intro w hw
  apply hv w
  intro he
  exact hw (hcover w he)

/-- Selected physical rows of the two actual raising operators. -/
def certificateRestrictedRaising {a b : Type*} (ket : Finset (Fin 6))
    (row : b → CertificateLocalWord) (test : a → Fin 2 × CertificateLocalWord) :
    Matrix a b ℤ :=
  fun t c => if (test t).1 = 0 then certificateLocalGenerator ket 0 1 (test t).2 (row c)
    else certificateLocalGenerator ket 1 2 (test t).2 (row c)

/-- Every physical highest vector is killed by the exact restricted test matrix. -/
theorem certificateRestrictedRaising_kills {a b : Type*} [Fintype b]
    (ket : Finset (Fin 6)) (lam : Fin 3 → ℤ)
    (row : b → CertificateLocalWord) (hrow : Function.Injective row)
    (hcover : ∀ w, certificateLocalWeight ket w = lam → w ∈ Set.range row)
    (test : a → Fin 2 × CertificateLocalWord)
    (v : CertificateLocalWord → ℂ) (hv : certificateIsHighest ket lam v) :
    (certificateRestrictedRaising ket row test).map (Int.cast : ℤ → ℂ) *ᵥ (v ∘ row) = 0 := by
  have hs := certificateHasWeight_support_rows ket lam row hcover v hv.1
  have h01 := certificateRestrictedAction row hrow
    ((certificateLocalGenerator ket 0 1).map (Int.cast : ℤ → ℂ)) v hs
  have h12 := certificateRestrictedAction row hrow
    ((certificateLocalGenerator ket 1 2).map (Int.cast : ℤ → ℂ)) v hs
  rw [hv.2.1] at h01
  rw [hv.2.2] at h12
  ext t
  by_cases ht : (test t).1 = 0
  · simpa [certificateRestrictedRaising, Matrix.mulVec, dotProduct, ht,
      Matrix.submatrix_apply] using congrFun h01 (test t).2
  · simpa [certificateRestrictedRaising, Matrix.mulVec, dotProduct, ht,
      Matrix.submatrix_apply] using congrFun h12 (test t).2

end ThreeCopyQutritWerner
