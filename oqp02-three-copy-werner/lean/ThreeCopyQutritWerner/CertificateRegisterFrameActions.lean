module

public import ThreeCopyQutritWerner.CertificateRegisterActions

@[expose] public section


/-! Exact ordinary stabilizer actions in all 22 original highest frames. -/

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

/-- The original carrier action is literal source lookup at permuted identity rows. -/
theorem certificateLocalFrame0_0_ordinary_action (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({5} : Finset (Fin 6)) ↔ s ∈ ({5} : Finset (Fin 6))) :
    certificateLocalDiagram ∅ σ * certificateLocalFrame0_0 = certificateLocalFrame0_0 * (certificateLocalFrame0_0.submatrix (fun r => certificateLocalPivots0_0 r ∘ ⇑(σ.symm)) id) := by
  have h : certificateLocalDiagram ∅ σ * certificateLocalFrame0_0 =
      certificateLocalFrame0_0 * certificateSparsePivotAction certificateLocalFrameEntries0_0 certificateLocalPivots0_0 ∅ σ := by
    apply certificateSparsePivotAction_source_action_of_complex certificateLocalFrameEntries0_0 certificateLocalPivots0_0
      certificateLocalFrame0_0_pivots ∅ σ
    refine ⟨_, certificateHighestKernel0_0source_action (certificateLocalDiagram ∅ σ) ?_⟩
    intro i j
    exact certificateOrdinaryRegister_commutes_generator_complex {5} σ hσ i j
  rw [certificateOrdinaryRegister_pivot_action] at h
  exact h

/-- The exact physical ordinary compression retains the original Gram metric. -/
theorem certificateLocalFrame0_0_ordinary_compression (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({5} : Finset (Fin 6)) ↔ s ∈ ({5} : Finset (Fin 6))) :
    certificateLocalFrame0_0ᵀ * certificateLocalDiagram ∅ σ * certificateLocalFrame0_0 = certificateLocalGram0_0 * (certificateLocalFrame0_0.submatrix (fun r => certificateLocalPivots0_0 r ∘ ⇑(σ.symm)) id) := by
  rw [Matrix.mul_assoc, certificateLocalFrame0_0_ordinary_action σ hσ,
    ← Matrix.mul_assoc, certificateLocalGram0_0_correct]

/-- The original carrier action is literal source lookup at permuted identity rows. -/
theorem certificateLocalFrame0_1_ordinary_action (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({5} : Finset (Fin 6)) ↔ s ∈ ({5} : Finset (Fin 6))) :
    certificateLocalDiagram ∅ σ * certificateLocalFrame0_1 = certificateLocalFrame0_1 * (certificateLocalFrame0_1.submatrix (fun r => certificateLocalPivots0_1 r ∘ ⇑(σ.symm)) id) := by
  have h : certificateLocalDiagram ∅ σ * certificateLocalFrame0_1 =
      certificateLocalFrame0_1 * certificateSparsePivotAction certificateLocalFrameEntries0_1 certificateLocalPivots0_1 ∅ σ := by
    apply certificateSparsePivotAction_source_action_of_complex certificateLocalFrameEntries0_1 certificateLocalPivots0_1
      certificateLocalFrame0_1_pivots ∅ σ
    refine ⟨_, certificateHighestKernel0_1source_action (certificateLocalDiagram ∅ σ) ?_⟩
    intro i j
    exact certificateOrdinaryRegister_commutes_generator_complex {5} σ hσ i j
  rw [certificateOrdinaryRegister_pivot_action] at h
  exact h

/-- The exact physical ordinary compression retains the original Gram metric. -/
theorem certificateLocalFrame0_1_ordinary_compression (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({5} : Finset (Fin 6)) ↔ s ∈ ({5} : Finset (Fin 6))) :
    certificateLocalFrame0_1ᵀ * certificateLocalDiagram ∅ σ * certificateLocalFrame0_1 = certificateLocalGram0_1 * (certificateLocalFrame0_1.submatrix (fun r => certificateLocalPivots0_1 r ∘ ⇑(σ.symm)) id) := by
  rw [Matrix.mul_assoc, certificateLocalFrame0_1_ordinary_action σ hσ,
    ← Matrix.mul_assoc, certificateLocalGram0_1_correct]

/-- The original carrier action is literal source lookup at permuted identity rows. -/
theorem certificateLocalFrame0_2_ordinary_action (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({5} : Finset (Fin 6)) ↔ s ∈ ({5} : Finset (Fin 6))) :
    certificateLocalDiagram ∅ σ * certificateLocalFrame0_2 = certificateLocalFrame0_2 * (certificateLocalFrame0_2.submatrix (fun r => certificateLocalPivots0_2 r ∘ ⇑(σ.symm)) id) := by
  have h : certificateLocalDiagram ∅ σ * certificateLocalFrame0_2 =
      certificateLocalFrame0_2 * certificateSparsePivotAction certificateLocalFrameEntries0_2 certificateLocalPivots0_2 ∅ σ := by
    apply certificateSparsePivotAction_source_action_of_complex certificateLocalFrameEntries0_2 certificateLocalPivots0_2
      certificateLocalFrame0_2_pivots ∅ σ
    refine ⟨_, certificateHighestKernel0_2source_action (certificateLocalDiagram ∅ σ) ?_⟩
    intro i j
    exact certificateOrdinaryRegister_commutes_generator_complex {5} σ hσ i j
  rw [certificateOrdinaryRegister_pivot_action] at h
  exact h

/-- The exact physical ordinary compression retains the original Gram metric. -/
theorem certificateLocalFrame0_2_ordinary_compression (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({5} : Finset (Fin 6)) ↔ s ∈ ({5} : Finset (Fin 6))) :
    certificateLocalFrame0_2ᵀ * certificateLocalDiagram ∅ σ * certificateLocalFrame0_2 = certificateLocalGram0_2 * (certificateLocalFrame0_2.submatrix (fun r => certificateLocalPivots0_2 r ∘ ⇑(σ.symm)) id) := by
  rw [Matrix.mul_assoc, certificateLocalFrame0_2_ordinary_action σ hσ,
    ← Matrix.mul_assoc, certificateLocalGram0_2_correct]

/-- The original carrier action is literal source lookup at permuted identity rows. -/
theorem certificateLocalFrame0_3_ordinary_action (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({5} : Finset (Fin 6)) ↔ s ∈ ({5} : Finset (Fin 6))) :
    certificateLocalDiagram ∅ σ * certificateLocalFrame0_3 = certificateLocalFrame0_3 * (certificateLocalFrame0_3.submatrix (fun r => certificateLocalPivots0_3 r ∘ ⇑(σ.symm)) id) := by
  have h : certificateLocalDiagram ∅ σ * certificateLocalFrame0_3 =
      certificateLocalFrame0_3 * certificateSparsePivotAction certificateLocalFrameEntries0_3 certificateLocalPivots0_3 ∅ σ := by
    apply certificateSparsePivotAction_source_action_of_complex certificateLocalFrameEntries0_3 certificateLocalPivots0_3
      certificateLocalFrame0_3_pivots ∅ σ
    refine ⟨_, certificateHighestKernel0_3source_action (certificateLocalDiagram ∅ σ) ?_⟩
    intro i j
    exact certificateOrdinaryRegister_commutes_generator_complex {5} σ hσ i j
  rw [certificateOrdinaryRegister_pivot_action] at h
  exact h

/-- The exact physical ordinary compression retains the original Gram metric. -/
theorem certificateLocalFrame0_3_ordinary_compression (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({5} : Finset (Fin 6)) ↔ s ∈ ({5} : Finset (Fin 6))) :
    certificateLocalFrame0_3ᵀ * certificateLocalDiagram ∅ σ * certificateLocalFrame0_3 = certificateLocalGram0_3 * (certificateLocalFrame0_3.submatrix (fun r => certificateLocalPivots0_3 r ∘ ⇑(σ.symm)) id) := by
  rw [Matrix.mul_assoc, certificateLocalFrame0_3_ordinary_action σ hσ,
    ← Matrix.mul_assoc, certificateLocalGram0_3_correct]

/-- The original carrier action is literal source lookup at permuted identity rows. -/
theorem certificateLocalFrame0_4_ordinary_action (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({5} : Finset (Fin 6)) ↔ s ∈ ({5} : Finset (Fin 6))) :
    certificateLocalDiagram ∅ σ * certificateLocalFrame0_4 = certificateLocalFrame0_4 * (certificateLocalFrame0_4.submatrix (fun r => certificateLocalPivots0_4 r ∘ ⇑(σ.symm)) id) := by
  have h : certificateLocalDiagram ∅ σ * certificateLocalFrame0_4 =
      certificateLocalFrame0_4 * certificateSparsePivotAction certificateLocalFrameEntries0_4 certificateLocalPivots0_4 ∅ σ := by
    apply certificateSparsePivotAction_source_action_of_complex certificateLocalFrameEntries0_4 certificateLocalPivots0_4
      certificateLocalFrame0_4_pivots ∅ σ
    refine ⟨_, certificateHighestKernel0_4source_action (certificateLocalDiagram ∅ σ) ?_⟩
    intro i j
    exact certificateOrdinaryRegister_commutes_generator_complex {5} σ hσ i j
  rw [certificateOrdinaryRegister_pivot_action] at h
  exact h

/-- The exact physical ordinary compression retains the original Gram metric. -/
theorem certificateLocalFrame0_4_ordinary_compression (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({5} : Finset (Fin 6)) ↔ s ∈ ({5} : Finset (Fin 6))) :
    certificateLocalFrame0_4ᵀ * certificateLocalDiagram ∅ σ * certificateLocalFrame0_4 = certificateLocalGram0_4 * (certificateLocalFrame0_4.submatrix (fun r => certificateLocalPivots0_4 r ∘ ⇑(σ.symm)) id) := by
  rw [Matrix.mul_assoc, certificateLocalFrame0_4_ordinary_action σ hσ,
    ← Matrix.mul_assoc, certificateLocalGram0_4_correct]

/-- The original carrier action is literal source lookup at permuted identity rows. -/
theorem certificateLocalFrame0_5_ordinary_action (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({5} : Finset (Fin 6)) ↔ s ∈ ({5} : Finset (Fin 6))) :
    certificateLocalDiagram ∅ σ * certificateLocalFrame0_5 = certificateLocalFrame0_5 * (certificateLocalFrame0_5.submatrix (fun r => certificateLocalPivots0_5 r ∘ ⇑(σ.symm)) id) := by
  have h : certificateLocalDiagram ∅ σ * certificateLocalFrame0_5 =
      certificateLocalFrame0_5 * certificateSparsePivotAction certificateLocalFrameEntries0_5 certificateLocalPivots0_5 ∅ σ := by
    apply certificateSparsePivotAction_source_action_of_complex certificateLocalFrameEntries0_5 certificateLocalPivots0_5
      certificateLocalFrame0_5_pivots ∅ σ
    refine ⟨_, certificateHighestKernel0_5source_action (certificateLocalDiagram ∅ σ) ?_⟩
    intro i j
    exact certificateOrdinaryRegister_commutes_generator_complex {5} σ hσ i j
  rw [certificateOrdinaryRegister_pivot_action] at h
  exact h

/-- The exact physical ordinary compression retains the original Gram metric. -/
theorem certificateLocalFrame0_5_ordinary_compression (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({5} : Finset (Fin 6)) ↔ s ∈ ({5} : Finset (Fin 6))) :
    certificateLocalFrame0_5ᵀ * certificateLocalDiagram ∅ σ * certificateLocalFrame0_5 = certificateLocalGram0_5 * (certificateLocalFrame0_5.submatrix (fun r => certificateLocalPivots0_5 r ∘ ⇑(σ.symm)) id) := by
  rw [Matrix.mul_assoc, certificateLocalFrame0_5_ordinary_action σ hσ,
    ← Matrix.mul_assoc, certificateLocalGram0_5_correct]

/-- The original carrier action is literal source lookup at permuted identity rows. -/
theorem certificateLocalFrame0_6_ordinary_action (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({5} : Finset (Fin 6)) ↔ s ∈ ({5} : Finset (Fin 6))) :
    certificateLocalDiagram ∅ σ * certificateLocalFrame0_6 = certificateLocalFrame0_6 * (certificateLocalFrame0_6.submatrix (fun r => certificateLocalPivots0_6 r ∘ ⇑(σ.symm)) id) := by
  have h : certificateLocalDiagram ∅ σ * certificateLocalFrame0_6 =
      certificateLocalFrame0_6 * certificateSparsePivotAction certificateLocalFrameEntries0_6 certificateLocalPivots0_6 ∅ σ := by
    apply certificateSparsePivotAction_source_action_of_complex certificateLocalFrameEntries0_6 certificateLocalPivots0_6
      certificateLocalFrame0_6_pivots ∅ σ
    refine ⟨_, certificateHighestKernel0_6source_action (certificateLocalDiagram ∅ σ) ?_⟩
    intro i j
    exact certificateOrdinaryRegister_commutes_generator_complex {5} σ hσ i j
  rw [certificateOrdinaryRegister_pivot_action] at h
  exact h

/-- The exact physical ordinary compression retains the original Gram metric. -/
theorem certificateLocalFrame0_6_ordinary_compression (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({5} : Finset (Fin 6)) ↔ s ∈ ({5} : Finset (Fin 6))) :
    certificateLocalFrame0_6ᵀ * certificateLocalDiagram ∅ σ * certificateLocalFrame0_6 = certificateLocalGram0_6 * (certificateLocalFrame0_6.submatrix (fun r => certificateLocalPivots0_6 r ∘ ⇑(σ.symm)) id) := by
  rw [Matrix.mul_assoc, certificateLocalFrame0_6_ordinary_action σ hσ,
    ← Matrix.mul_assoc, certificateLocalGram0_6_correct]

/-- The original carrier action is literal source lookup at permuted identity rows. -/
theorem certificateLocalFrame1_0_ordinary_action (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({0, 1, 2} : Finset (Fin 6)) ↔ s ∈ ({0, 1, 2} : Finset (Fin 6))) :
    certificateLocalDiagram ∅ σ * certificateLocalFrame1_0 = certificateLocalFrame1_0 * (certificateLocalFrame1_0.submatrix (fun r => certificateLocalPivots1_0 r ∘ ⇑(σ.symm)) id) := by
  have h : certificateLocalDiagram ∅ σ * certificateLocalFrame1_0 =
      certificateLocalFrame1_0 * certificateSparsePivotAction certificateLocalFrameEntries1_0 certificateLocalPivots1_0 ∅ σ := by
    apply certificateSparsePivotAction_source_action_of_complex certificateLocalFrameEntries1_0 certificateLocalPivots1_0
      certificateLocalFrame1_0_pivots ∅ σ
    refine ⟨_, certificateHighestKernel1_0source_action (certificateLocalDiagram ∅ σ) ?_⟩
    intro i j
    exact certificateOrdinaryRegister_commutes_generator_complex {0, 1, 2} σ hσ i j
  rw [certificateOrdinaryRegister_pivot_action] at h
  exact h

/-- The exact physical ordinary compression retains the original Gram metric. -/
theorem certificateLocalFrame1_0_ordinary_compression (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({0, 1, 2} : Finset (Fin 6)) ↔ s ∈ ({0, 1, 2} : Finset (Fin 6))) :
    certificateLocalFrame1_0ᵀ * certificateLocalDiagram ∅ σ * certificateLocalFrame1_0 = certificateLocalGram1_0 * (certificateLocalFrame1_0.submatrix (fun r => certificateLocalPivots1_0 r ∘ ⇑(σ.symm)) id) := by
  rw [Matrix.mul_assoc, certificateLocalFrame1_0_ordinary_action σ hσ,
    ← Matrix.mul_assoc, certificateLocalGram1_0_correct]

/-- The original carrier action is literal source lookup at permuted identity rows. -/
theorem certificateLocalFrame1_1_ordinary_action (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({0, 1, 2} : Finset (Fin 6)) ↔ s ∈ ({0, 1, 2} : Finset (Fin 6))) :
    certificateLocalDiagram ∅ σ * certificateLocalFrame1_1 = certificateLocalFrame1_1 * (certificateLocalFrame1_1.submatrix (fun r => certificateLocalPivots1_1 r ∘ ⇑(σ.symm)) id) := by
  have h : certificateLocalDiagram ∅ σ * certificateLocalFrame1_1 =
      certificateLocalFrame1_1 * certificateSparsePivotAction certificateLocalFrameEntries1_1 certificateLocalPivots1_1 ∅ σ := by
    apply certificateSparsePivotAction_source_action_of_complex certificateLocalFrameEntries1_1 certificateLocalPivots1_1
      certificateLocalFrame1_1_pivots ∅ σ
    refine ⟨_, certificateHighestKernel1_1source_action (certificateLocalDiagram ∅ σ) ?_⟩
    intro i j
    exact certificateOrdinaryRegister_commutes_generator_complex {0, 1, 2} σ hσ i j
  rw [certificateOrdinaryRegister_pivot_action] at h
  exact h

/-- The exact physical ordinary compression retains the original Gram metric. -/
theorem certificateLocalFrame1_1_ordinary_compression (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({0, 1, 2} : Finset (Fin 6)) ↔ s ∈ ({0, 1, 2} : Finset (Fin 6))) :
    certificateLocalFrame1_1ᵀ * certificateLocalDiagram ∅ σ * certificateLocalFrame1_1 = certificateLocalGram1_1 * (certificateLocalFrame1_1.submatrix (fun r => certificateLocalPivots1_1 r ∘ ⇑(σ.symm)) id) := by
  rw [Matrix.mul_assoc, certificateLocalFrame1_1_ordinary_action σ hσ,
    ← Matrix.mul_assoc, certificateLocalGram1_1_correct]

/-- The original carrier action is literal source lookup at permuted identity rows. -/
theorem certificateLocalFrame1_2_ordinary_action (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({0, 1, 2} : Finset (Fin 6)) ↔ s ∈ ({0, 1, 2} : Finset (Fin 6))) :
    certificateLocalDiagram ∅ σ * certificateLocalFrame1_2 = certificateLocalFrame1_2 * (certificateLocalFrame1_2.submatrix (fun r => certificateLocalPivots1_2 r ∘ ⇑(σ.symm)) id) := by
  have h : certificateLocalDiagram ∅ σ * certificateLocalFrame1_2 =
      certificateLocalFrame1_2 * certificateSparsePivotAction certificateLocalFrameEntries1_2 certificateLocalPivots1_2 ∅ σ := by
    apply certificateSparsePivotAction_source_action_of_complex certificateLocalFrameEntries1_2 certificateLocalPivots1_2
      certificateLocalFrame1_2_pivots ∅ σ
    refine ⟨_, certificateHighestKernel1_2source_action (certificateLocalDiagram ∅ σ) ?_⟩
    intro i j
    exact certificateOrdinaryRegister_commutes_generator_complex {0, 1, 2} σ hσ i j
  rw [certificateOrdinaryRegister_pivot_action] at h
  exact h

/-- The exact physical ordinary compression retains the original Gram metric. -/
theorem certificateLocalFrame1_2_ordinary_compression (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({0, 1, 2} : Finset (Fin 6)) ↔ s ∈ ({0, 1, 2} : Finset (Fin 6))) :
    certificateLocalFrame1_2ᵀ * certificateLocalDiagram ∅ σ * certificateLocalFrame1_2 = certificateLocalGram1_2 * (certificateLocalFrame1_2.submatrix (fun r => certificateLocalPivots1_2 r ∘ ⇑(σ.symm)) id) := by
  rw [Matrix.mul_assoc, certificateLocalFrame1_2_ordinary_action σ hσ,
    ← Matrix.mul_assoc, certificateLocalGram1_2_correct]

/-- The original carrier action is literal source lookup at permuted identity rows. -/
theorem certificateLocalFrame1_3_ordinary_action (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({0, 1, 2} : Finset (Fin 6)) ↔ s ∈ ({0, 1, 2} : Finset (Fin 6))) :
    certificateLocalDiagram ∅ σ * certificateLocalFrame1_3 = certificateLocalFrame1_3 * (certificateLocalFrame1_3.submatrix (fun r => certificateLocalPivots1_3 r ∘ ⇑(σ.symm)) id) := by
  have h : certificateLocalDiagram ∅ σ * certificateLocalFrame1_3 =
      certificateLocalFrame1_3 * certificateSparsePivotAction certificateLocalFrameEntries1_3 certificateLocalPivots1_3 ∅ σ := by
    apply certificateSparsePivotAction_source_action_of_complex certificateLocalFrameEntries1_3 certificateLocalPivots1_3
      certificateLocalFrame1_3_pivots ∅ σ
    refine ⟨_, certificateHighestKernel1_3source_action (certificateLocalDiagram ∅ σ) ?_⟩
    intro i j
    exact certificateOrdinaryRegister_commutes_generator_complex {0, 1, 2} σ hσ i j
  rw [certificateOrdinaryRegister_pivot_action] at h
  exact h

/-- The exact physical ordinary compression retains the original Gram metric. -/
theorem certificateLocalFrame1_3_ordinary_compression (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({0, 1, 2} : Finset (Fin 6)) ↔ s ∈ ({0, 1, 2} : Finset (Fin 6))) :
    certificateLocalFrame1_3ᵀ * certificateLocalDiagram ∅ σ * certificateLocalFrame1_3 = certificateLocalGram1_3 * (certificateLocalFrame1_3.submatrix (fun r => certificateLocalPivots1_3 r ∘ ⇑(σ.symm)) id) := by
  rw [Matrix.mul_assoc, certificateLocalFrame1_3_ordinary_action σ hσ,
    ← Matrix.mul_assoc, certificateLocalGram1_3_correct]

/-- The original carrier action is literal source lookup at permuted identity rows. -/
theorem certificateLocalFrame1_4_ordinary_action (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({0, 1, 2} : Finset (Fin 6)) ↔ s ∈ ({0, 1, 2} : Finset (Fin 6))) :
    certificateLocalDiagram ∅ σ * certificateLocalFrame1_4 = certificateLocalFrame1_4 * (certificateLocalFrame1_4.submatrix (fun r => certificateLocalPivots1_4 r ∘ ⇑(σ.symm)) id) := by
  have h : certificateLocalDiagram ∅ σ * certificateLocalFrame1_4 =
      certificateLocalFrame1_4 * certificateSparsePivotAction certificateLocalFrameEntries1_4 certificateLocalPivots1_4 ∅ σ := by
    apply certificateSparsePivotAction_source_action_of_complex certificateLocalFrameEntries1_4 certificateLocalPivots1_4
      certificateLocalFrame1_4_pivots ∅ σ
    refine ⟨_, certificateHighestKernel1_4source_action (certificateLocalDiagram ∅ σ) ?_⟩
    intro i j
    exact certificateOrdinaryRegister_commutes_generator_complex {0, 1, 2} σ hσ i j
  rw [certificateOrdinaryRegister_pivot_action] at h
  exact h

/-- The exact physical ordinary compression retains the original Gram metric. -/
theorem certificateLocalFrame1_4_ordinary_compression (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({0, 1, 2} : Finset (Fin 6)) ↔ s ∈ ({0, 1, 2} : Finset (Fin 6))) :
    certificateLocalFrame1_4ᵀ * certificateLocalDiagram ∅ σ * certificateLocalFrame1_4 = certificateLocalGram1_4 * (certificateLocalFrame1_4.submatrix (fun r => certificateLocalPivots1_4 r ∘ ⇑(σ.symm)) id) := by
  rw [Matrix.mul_assoc, certificateLocalFrame1_4_ordinary_action σ hσ,
    ← Matrix.mul_assoc, certificateLocalGram1_4_correct]

/-- The original carrier action is literal source lookup at permuted identity rows. -/
theorem certificateLocalFrame1_5_ordinary_action (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({0, 1, 2} : Finset (Fin 6)) ↔ s ∈ ({0, 1, 2} : Finset (Fin 6))) :
    certificateLocalDiagram ∅ σ * certificateLocalFrame1_5 = certificateLocalFrame1_5 * (certificateLocalFrame1_5.submatrix (fun r => certificateLocalPivots1_5 r ∘ ⇑(σ.symm)) id) := by
  have h : certificateLocalDiagram ∅ σ * certificateLocalFrame1_5 =
      certificateLocalFrame1_5 * certificateSparsePivotAction certificateLocalFrameEntries1_5 certificateLocalPivots1_5 ∅ σ := by
    apply certificateSparsePivotAction_source_action_of_complex certificateLocalFrameEntries1_5 certificateLocalPivots1_5
      certificateLocalFrame1_5_pivots ∅ σ
    refine ⟨_, certificateHighestKernel1_5source_action (certificateLocalDiagram ∅ σ) ?_⟩
    intro i j
    exact certificateOrdinaryRegister_commutes_generator_complex {0, 1, 2} σ hσ i j
  rw [certificateOrdinaryRegister_pivot_action] at h
  exact h

/-- The exact physical ordinary compression retains the original Gram metric. -/
theorem certificateLocalFrame1_5_ordinary_compression (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({0, 1, 2} : Finset (Fin 6)) ↔ s ∈ ({0, 1, 2} : Finset (Fin 6))) :
    certificateLocalFrame1_5ᵀ * certificateLocalDiagram ∅ σ * certificateLocalFrame1_5 = certificateLocalGram1_5 * (certificateLocalFrame1_5.submatrix (fun r => certificateLocalPivots1_5 r ∘ ⇑(σ.symm)) id) := by
  rw [Matrix.mul_assoc, certificateLocalFrame1_5_ordinary_action σ hσ,
    ← Matrix.mul_assoc, certificateLocalGram1_5_correct]

/-- The original carrier action is literal source lookup at permuted identity rows. -/
theorem certificateLocalFrame1_6_ordinary_action (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({0, 1, 2} : Finset (Fin 6)) ↔ s ∈ ({0, 1, 2} : Finset (Fin 6))) :
    certificateLocalDiagram ∅ σ * certificateLocalFrame1_6 = certificateLocalFrame1_6 * (certificateLocalFrame1_6.submatrix (fun r => certificateLocalPivots1_6 r ∘ ⇑(σ.symm)) id) := by
  have h : certificateLocalDiagram ∅ σ * certificateLocalFrame1_6 =
      certificateLocalFrame1_6 * certificateSparsePivotAction certificateLocalFrameEntries1_6 certificateLocalPivots1_6 ∅ σ := by
    apply certificateSparsePivotAction_source_action_of_complex certificateLocalFrameEntries1_6 certificateLocalPivots1_6
      certificateLocalFrame1_6_pivots ∅ σ
    refine ⟨_, certificateHighestKernel1_6source_action (certificateLocalDiagram ∅ σ) ?_⟩
    intro i j
    exact certificateOrdinaryRegister_commutes_generator_complex {0, 1, 2} σ hσ i j
  rw [certificateOrdinaryRegister_pivot_action] at h
  exact h

/-- The exact physical ordinary compression retains the original Gram metric. -/
theorem certificateLocalFrame1_6_ordinary_compression (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({0, 1, 2} : Finset (Fin 6)) ↔ s ∈ ({0, 1, 2} : Finset (Fin 6))) :
    certificateLocalFrame1_6ᵀ * certificateLocalDiagram ∅ σ * certificateLocalFrame1_6 = certificateLocalGram1_6 * (certificateLocalFrame1_6.submatrix (fun r => certificateLocalPivots1_6 r ∘ ⇑(σ.symm)) id) := by
  rw [Matrix.mul_assoc, certificateLocalFrame1_6_ordinary_action σ hσ,
    ← Matrix.mul_assoc, certificateLocalGram1_6_correct]

/-- The original carrier action is literal source lookup at permuted identity rows. -/
theorem certificateLocalFrame1_7_ordinary_action (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({0, 1, 2} : Finset (Fin 6)) ↔ s ∈ ({0, 1, 2} : Finset (Fin 6))) :
    certificateLocalDiagram ∅ σ * certificateLocalFrame1_7 = certificateLocalFrame1_7 * (certificateLocalFrame1_7.submatrix (fun r => certificateLocalPivots1_7 r ∘ ⇑(σ.symm)) id) := by
  have h : certificateLocalDiagram ∅ σ * certificateLocalFrame1_7 =
      certificateLocalFrame1_7 * certificateSparsePivotAction certificateLocalFrameEntries1_7 certificateLocalPivots1_7 ∅ σ := by
    apply certificateSparsePivotAction_source_action_of_complex certificateLocalFrameEntries1_7 certificateLocalPivots1_7
      certificateLocalFrame1_7_pivots ∅ σ
    refine ⟨_, certificateHighestKernel1_7source_action (certificateLocalDiagram ∅ σ) ?_⟩
    intro i j
    exact certificateOrdinaryRegister_commutes_generator_complex {0, 1, 2} σ hσ i j
  rw [certificateOrdinaryRegister_pivot_action] at h
  exact h

/-- The exact physical ordinary compression retains the original Gram metric. -/
theorem certificateLocalFrame1_7_ordinary_compression (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({0, 1, 2} : Finset (Fin 6)) ↔ s ∈ ({0, 1, 2} : Finset (Fin 6))) :
    certificateLocalFrame1_7ᵀ * certificateLocalDiagram ∅ σ * certificateLocalFrame1_7 = certificateLocalGram1_7 * (certificateLocalFrame1_7.submatrix (fun r => certificateLocalPivots1_7 r ∘ ⇑(σ.symm)) id) := by
  rw [Matrix.mul_assoc, certificateLocalFrame1_7_ordinary_action σ hσ,
    ← Matrix.mul_assoc, certificateLocalGram1_7_correct]

/-- The original carrier action is literal source lookup at permuted identity rows. -/
theorem certificateLocalFrame2_0_ordinary_action (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({0} : Finset (Fin 6)) ↔ s ∈ ({0} : Finset (Fin 6))) :
    certificateLocalDiagram ∅ σ * certificateLocalFrame2_0 = certificateLocalFrame2_0 * (certificateLocalFrame2_0.submatrix (fun r => certificateLocalPivots2_0 r ∘ ⇑(σ.symm)) id) := by
  have h : certificateLocalDiagram ∅ σ * certificateLocalFrame2_0 =
      certificateLocalFrame2_0 * certificateSparsePivotAction certificateLocalFrameEntries2_0 certificateLocalPivots2_0 ∅ σ := by
    apply certificateSparsePivotAction_source_action_of_complex certificateLocalFrameEntries2_0 certificateLocalPivots2_0
      certificateLocalFrame2_0_pivots ∅ σ
    refine ⟨_, certificateHighestKernel2_0source_action (certificateLocalDiagram ∅ σ) ?_⟩
    intro i j
    exact certificateOrdinaryRegister_commutes_generator_complex {0} σ hσ i j
  rw [certificateOrdinaryRegister_pivot_action] at h
  exact h

/-- The exact physical ordinary compression retains the original Gram metric. -/
theorem certificateLocalFrame2_0_ordinary_compression (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({0} : Finset (Fin 6)) ↔ s ∈ ({0} : Finset (Fin 6))) :
    certificateLocalFrame2_0ᵀ * certificateLocalDiagram ∅ σ * certificateLocalFrame2_0 = certificateLocalGram2_0 * (certificateLocalFrame2_0.submatrix (fun r => certificateLocalPivots2_0 r ∘ ⇑(σ.symm)) id) := by
  rw [Matrix.mul_assoc, certificateLocalFrame2_0_ordinary_action σ hσ,
    ← Matrix.mul_assoc, certificateLocalGram2_0_correct]

/-- The original carrier action is literal source lookup at permuted identity rows. -/
theorem certificateLocalFrame2_1_ordinary_action (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({0} : Finset (Fin 6)) ↔ s ∈ ({0} : Finset (Fin 6))) :
    certificateLocalDiagram ∅ σ * certificateLocalFrame2_1 = certificateLocalFrame2_1 * (certificateLocalFrame2_1.submatrix (fun r => certificateLocalPivots2_1 r ∘ ⇑(σ.symm)) id) := by
  have h : certificateLocalDiagram ∅ σ * certificateLocalFrame2_1 =
      certificateLocalFrame2_1 * certificateSparsePivotAction certificateLocalFrameEntries2_1 certificateLocalPivots2_1 ∅ σ := by
    apply certificateSparsePivotAction_source_action_of_complex certificateLocalFrameEntries2_1 certificateLocalPivots2_1
      certificateLocalFrame2_1_pivots ∅ σ
    refine ⟨_, certificateHighestKernel2_1source_action (certificateLocalDiagram ∅ σ) ?_⟩
    intro i j
    exact certificateOrdinaryRegister_commutes_generator_complex {0} σ hσ i j
  rw [certificateOrdinaryRegister_pivot_action] at h
  exact h

/-- The exact physical ordinary compression retains the original Gram metric. -/
theorem certificateLocalFrame2_1_ordinary_compression (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({0} : Finset (Fin 6)) ↔ s ∈ ({0} : Finset (Fin 6))) :
    certificateLocalFrame2_1ᵀ * certificateLocalDiagram ∅ σ * certificateLocalFrame2_1 = certificateLocalGram2_1 * (certificateLocalFrame2_1.submatrix (fun r => certificateLocalPivots2_1 r ∘ ⇑(σ.symm)) id) := by
  rw [Matrix.mul_assoc, certificateLocalFrame2_1_ordinary_action σ hσ,
    ← Matrix.mul_assoc, certificateLocalGram2_1_correct]

/-- The original carrier action is literal source lookup at permuted identity rows. -/
theorem certificateLocalFrame2_2_ordinary_action (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({0} : Finset (Fin 6)) ↔ s ∈ ({0} : Finset (Fin 6))) :
    certificateLocalDiagram ∅ σ * certificateLocalFrame2_2 = certificateLocalFrame2_2 * (certificateLocalFrame2_2.submatrix (fun r => certificateLocalPivots2_2 r ∘ ⇑(σ.symm)) id) := by
  have h : certificateLocalDiagram ∅ σ * certificateLocalFrame2_2 =
      certificateLocalFrame2_2 * certificateSparsePivotAction certificateLocalFrameEntries2_2 certificateLocalPivots2_2 ∅ σ := by
    apply certificateSparsePivotAction_source_action_of_complex certificateLocalFrameEntries2_2 certificateLocalPivots2_2
      certificateLocalFrame2_2_pivots ∅ σ
    refine ⟨_, certificateHighestKernel2_2source_action (certificateLocalDiagram ∅ σ) ?_⟩
    intro i j
    exact certificateOrdinaryRegister_commutes_generator_complex {0} σ hσ i j
  rw [certificateOrdinaryRegister_pivot_action] at h
  exact h

/-- The exact physical ordinary compression retains the original Gram metric. -/
theorem certificateLocalFrame2_2_ordinary_compression (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({0} : Finset (Fin 6)) ↔ s ∈ ({0} : Finset (Fin 6))) :
    certificateLocalFrame2_2ᵀ * certificateLocalDiagram ∅ σ * certificateLocalFrame2_2 = certificateLocalGram2_2 * (certificateLocalFrame2_2.submatrix (fun r => certificateLocalPivots2_2 r ∘ ⇑(σ.symm)) id) := by
  rw [Matrix.mul_assoc, certificateLocalFrame2_2_ordinary_action σ hσ,
    ← Matrix.mul_assoc, certificateLocalGram2_2_correct]

/-- The original carrier action is literal source lookup at permuted identity rows. -/
theorem certificateLocalFrame2_3_ordinary_action (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({0} : Finset (Fin 6)) ↔ s ∈ ({0} : Finset (Fin 6))) :
    certificateLocalDiagram ∅ σ * certificateLocalFrame2_3 = certificateLocalFrame2_3 * (certificateLocalFrame2_3.submatrix (fun r => certificateLocalPivots2_3 r ∘ ⇑(σ.symm)) id) := by
  have h : certificateLocalDiagram ∅ σ * certificateLocalFrame2_3 =
      certificateLocalFrame2_3 * certificateSparsePivotAction certificateLocalFrameEntries2_3 certificateLocalPivots2_3 ∅ σ := by
    apply certificateSparsePivotAction_source_action_of_complex certificateLocalFrameEntries2_3 certificateLocalPivots2_3
      certificateLocalFrame2_3_pivots ∅ σ
    refine ⟨_, certificateHighestKernel2_3source_action (certificateLocalDiagram ∅ σ) ?_⟩
    intro i j
    exact certificateOrdinaryRegister_commutes_generator_complex {0} σ hσ i j
  rw [certificateOrdinaryRegister_pivot_action] at h
  exact h

/-- The exact physical ordinary compression retains the original Gram metric. -/
theorem certificateLocalFrame2_3_ordinary_compression (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({0} : Finset (Fin 6)) ↔ s ∈ ({0} : Finset (Fin 6))) :
    certificateLocalFrame2_3ᵀ * certificateLocalDiagram ∅ σ * certificateLocalFrame2_3 = certificateLocalGram2_3 * (certificateLocalFrame2_3.submatrix (fun r => certificateLocalPivots2_3 r ∘ ⇑(σ.symm)) id) := by
  rw [Matrix.mul_assoc, certificateLocalFrame2_3_ordinary_action σ hσ,
    ← Matrix.mul_assoc, certificateLocalGram2_3_correct]

/-- The original carrier action is literal source lookup at permuted identity rows. -/
theorem certificateLocalFrame2_4_ordinary_action (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({0} : Finset (Fin 6)) ↔ s ∈ ({0} : Finset (Fin 6))) :
    certificateLocalDiagram ∅ σ * certificateLocalFrame2_4 = certificateLocalFrame2_4 * (certificateLocalFrame2_4.submatrix (fun r => certificateLocalPivots2_4 r ∘ ⇑(σ.symm)) id) := by
  have h : certificateLocalDiagram ∅ σ * certificateLocalFrame2_4 =
      certificateLocalFrame2_4 * certificateSparsePivotAction certificateLocalFrameEntries2_4 certificateLocalPivots2_4 ∅ σ := by
    apply certificateSparsePivotAction_source_action_of_complex certificateLocalFrameEntries2_4 certificateLocalPivots2_4
      certificateLocalFrame2_4_pivots ∅ σ
    refine ⟨_, certificateHighestKernel2_4source_action (certificateLocalDiagram ∅ σ) ?_⟩
    intro i j
    exact certificateOrdinaryRegister_commutes_generator_complex {0} σ hσ i j
  rw [certificateOrdinaryRegister_pivot_action] at h
  exact h

/-- The exact physical ordinary compression retains the original Gram metric. -/
theorem certificateLocalFrame2_4_ordinary_compression (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({0} : Finset (Fin 6)) ↔ s ∈ ({0} : Finset (Fin 6))) :
    certificateLocalFrame2_4ᵀ * certificateLocalDiagram ∅ σ * certificateLocalFrame2_4 = certificateLocalGram2_4 * (certificateLocalFrame2_4.submatrix (fun r => certificateLocalPivots2_4 r ∘ ⇑(σ.symm)) id) := by
  rw [Matrix.mul_assoc, certificateLocalFrame2_4_ordinary_action σ hσ,
    ← Matrix.mul_assoc, certificateLocalGram2_4_correct]

/-- The original carrier action is literal source lookup at permuted identity rows. -/
theorem certificateLocalFrame2_5_ordinary_action (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({0} : Finset (Fin 6)) ↔ s ∈ ({0} : Finset (Fin 6))) :
    certificateLocalDiagram ∅ σ * certificateLocalFrame2_5 = certificateLocalFrame2_5 * (certificateLocalFrame2_5.submatrix (fun r => certificateLocalPivots2_5 r ∘ ⇑(σ.symm)) id) := by
  have h : certificateLocalDiagram ∅ σ * certificateLocalFrame2_5 =
      certificateLocalFrame2_5 * certificateSparsePivotAction certificateLocalFrameEntries2_5 certificateLocalPivots2_5 ∅ σ := by
    apply certificateSparsePivotAction_source_action_of_complex certificateLocalFrameEntries2_5 certificateLocalPivots2_5
      certificateLocalFrame2_5_pivots ∅ σ
    refine ⟨_, certificateHighestKernel2_5source_action (certificateLocalDiagram ∅ σ) ?_⟩
    intro i j
    exact certificateOrdinaryRegister_commutes_generator_complex {0} σ hσ i j
  rw [certificateOrdinaryRegister_pivot_action] at h
  exact h

/-- The exact physical ordinary compression retains the original Gram metric. -/
theorem certificateLocalFrame2_5_ordinary_compression (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({0} : Finset (Fin 6)) ↔ s ∈ ({0} : Finset (Fin 6))) :
    certificateLocalFrame2_5ᵀ * certificateLocalDiagram ∅ σ * certificateLocalFrame2_5 = certificateLocalGram2_5 * (certificateLocalFrame2_5.submatrix (fun r => certificateLocalPivots2_5 r ∘ ⇑(σ.symm)) id) := by
  rw [Matrix.mul_assoc, certificateLocalFrame2_5_ordinary_action σ hσ,
    ← Matrix.mul_assoc, certificateLocalGram2_5_correct]

/-- The original carrier action is literal source lookup at permuted identity rows. -/
theorem certificateLocalFrame2_6_ordinary_action (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({0} : Finset (Fin 6)) ↔ s ∈ ({0} : Finset (Fin 6))) :
    certificateLocalDiagram ∅ σ * certificateLocalFrame2_6 = certificateLocalFrame2_6 * (certificateLocalFrame2_6.submatrix (fun r => certificateLocalPivots2_6 r ∘ ⇑(σ.symm)) id) := by
  have h : certificateLocalDiagram ∅ σ * certificateLocalFrame2_6 =
      certificateLocalFrame2_6 * certificateSparsePivotAction certificateLocalFrameEntries2_6 certificateLocalPivots2_6 ∅ σ := by
    apply certificateSparsePivotAction_source_action_of_complex certificateLocalFrameEntries2_6 certificateLocalPivots2_6
      certificateLocalFrame2_6_pivots ∅ σ
    refine ⟨_, certificateHighestKernel2_6source_action (certificateLocalDiagram ∅ σ) ?_⟩
    intro i j
    exact certificateOrdinaryRegister_commutes_generator_complex {0} σ hσ i j
  rw [certificateOrdinaryRegister_pivot_action] at h
  exact h

/-- The exact physical ordinary compression retains the original Gram metric. -/
theorem certificateLocalFrame2_6_ordinary_compression (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ({0} : Finset (Fin 6)) ↔ s ∈ ({0} : Finset (Fin 6))) :
    certificateLocalFrame2_6ᵀ * certificateLocalDiagram ∅ σ * certificateLocalFrame2_6 = certificateLocalGram2_6 * (certificateLocalFrame2_6.submatrix (fun r => certificateLocalPivots2_6 r ∘ ⇑(σ.symm)) id) := by
  rw [Matrix.mul_assoc, certificateLocalFrame2_6_ordinary_action σ hσ,
    ← Matrix.mul_assoc, certificateLocalGram2_6_correct]

end ThreeCopyQutritWerner
