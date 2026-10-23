module

public import ThreeCopyQutritWerner.CertificateSiteRegroup
public import ThreeCopyQutritWerner.CertificateSparseDiagramAction
public import ThreeCopyQutritWerner.WernerPT

@[expose] public section


/-!
# The literal endpoint operator in the original diagram coordinates (core)

The distinguished local registers are row = 0 and col = 5; registers 1 through 4 carry the
identity. Their swap, partially transposed at register 5, is the unnormalized maximally
entangled projector `Ω₀₅`. Regrouped by sites, the six-register endpoint operator is the tensor
cube of the two-term local diagram combination `I - Ω₀₅ / 2`
(`certificateSixRegisterOperator_diagram`).

This is the frame-free part of `CertificateEndpointDiagram`, with robust proofs (the earlier
proofs failed on reordered conjunctions, a `rw` under a `Decidable` instance, and an unreduced
`Equiv.symm`). It imports no frame data.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- Embed a row/column pair operator at local registers 0 and 5. -/
def certificateLocalPairLift (M : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) :
    Matrix CertificateLocalWord CertificateLocalWord ℂ := fun r c =>
  M (r 0, r 5) (c 0, c 5) *
    (if r 1 = c 1 then 1 else 0) * (if r 2 = c 2 then 1 else 0) *
    (if r 3 = c 3 then 1 else 0) * (if r 4 = c 4 then 1 else 0)

theorem certificate_indicator_and (p q : Prop) [Decidable p] [Decidable q] :
    (if p ∧ q then (1 : ℂ) else 0) =
      (if p then 1 else 0) * (if q then 1 else 0) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-- Swapping a register set in both words keeps them equal exactly when they are equal. -/
theorem certificateWordSwap_eq_comm_iff {k : ℕ} {n : Type*} (S : Finset (Fin k))
    (r c : Fin k → n) :
    certificateWordSwap S r c = certificateWordSwap S c r ↔ r = c := by
  constructor
  · intro h
    funext i
    have hi := congrFun h i
    by_cases hS : i ∈ S
    · simp only [certificateWordSwap, if_pos hS] at hi
      exact hi.symm
    · simp only [certificateWordSwap, if_neg hS] at hi
      exact hi
  · rintro rfl
    rfl

/-- Equality of two local words, coordinate by coordinate (row/col first). -/
theorem certificateLocalWord_eq_iff (r c : CertificateLocalWord) :
    r = c ↔ (r 0 = c 0 ∧ r 5 = c 5) ∧ r 1 = c 1 ∧ r 2 = c 2 ∧ r 3 = c 3 ∧ r 4 = c 4 := by
  constructor
  · rintro rfl
    exact ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl⟩
  · rintro ⟨⟨h0, h5⟩, h1, h2, h3, h4⟩
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5

/-- Entries of the lifted identity. -/
theorem certificateLocalPairLift_one_apply (r c : CertificateLocalWord) :
    certificateLocalPairLift 1 r c =
      if (r 0 = c 0 ∧ r 5 = c 5) ∧ r 1 = c 1 ∧ r 2 = c 2 ∧ r 3 = c 3 ∧ r 4 = c 4 then 1 else 0 := by
  simp only [certificateLocalPairLift, Matrix.one_apply, Prod.mk.injEq]
  by_cases h0 : r 0 = c 0 <;> by_cases h5 : r 5 = c 5 <;> by_cases h1 : r 1 = c 1 <;>
    by_cases h2 : r 2 = c 2 <;> by_cases h3 : r 3 = c 3 <;> by_cases h4 : r 4 = c 4 <;>
    simp [h0, h5, h1, h2, h3, h4]

/-- Entries of the lifted `Ω`. -/
theorem certificateLocalPairLift_omega_apply (r c : CertificateLocalWord) :
    certificateLocalPairLift (omegaOp (Fin 3)) r c =
      if (r 0 = r 5 ∧ c 0 = c 5) ∧ r 1 = c 1 ∧ r 2 = c 2 ∧ r 3 = c 3 ∧ r 4 = c 4 then 1 else 0 := by
  simp only [certificateLocalPairLift, omegaOp]
  by_cases h0 : r 0 = r 5 <;> by_cases h5 : c 0 = c 5 <;> by_cases h1 : r 1 = c 1 <;>
    by_cases h2 : r 2 = c 2 <;> by_cases h3 : r 3 = c 3 <;> by_cases h4 : r 4 = c 4 <;>
    simp [h0, h5, h1, h2, h3, h4]

/-- The diagram condition of the identity permutation. -/
theorem certificateEndpointDiagram_identity_cond (r c : CertificateLocalWord) :
    certificateWordSwap {5} r c = certificateWordSwap {5} c r ∘ ⇑(1 : Equiv.Perm (Fin 6)) ↔
      (r 0 = c 0 ∧ r 5 = c 5) ∧ r 1 = c 1 ∧ r 2 = c 2 ∧ r 3 = c 3 ∧ r 4 = c 4 := by
  rw [Equiv.Perm.coe_one, Function.comp_id, certificateWordSwap_eq_comm_iff,
    certificateLocalWord_eq_iff]

/-- The diagram condition of the transposition `(0 5)` with register 5 transposed. -/
theorem certificateEndpointDiagram_omega_cond (r c : CertificateLocalWord) :
    certificateWordSwap {5} r c = certificateWordSwap {5} c r ∘ ⇑(Equiv.swap (0 : Fin 6) 5) ↔
      (r 0 = r 5 ∧ c 0 = c 5) ∧ r 1 = c 1 ∧ r 2 = c 2 ∧ r 3 = c 3 ∧ r 4 = c 4 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    have h3 := congrFun h 3
    have h4 := congrFun h 4
    have h5 := congrFun h 5
    simp [certificateWordSwap, Equiv.swap_apply_def] at h0 h1 h2 h3 h4 h5
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;> first | assumption | (apply Eq.symm; assumption)
  · rintro ⟨⟨h05, hc⟩, h1, h2, h3, h4⟩
    funext i
    fin_cases i <;> simp [certificateWordSwap, Equiv.swap_apply_def, h05, hc, h1, h2, h3, h4]

/-- The identity diagram retains the identity on all six original local registers. -/
theorem certificateEndpointDiagram_identity :
    certificateLocalDiagram (n := Fin 3) (R := ℂ) {5} 1 =
      certificateLocalPairLift 1 := by
  ext r c
  rw [certificateLocalDiagram_entry, certificateLocalPairLift_one_apply]
  by_cases h : (r 0 = c 0 ∧ r 5 = c 5) ∧ r 1 = c 1 ∧ r 2 = c 2 ∧ r 3 = c 3 ∧ r 4 = c 4
  · rw [if_pos ((certificateEndpointDiagram_identity_cond r c).mpr h), if_pos h]
  · rw [if_neg (fun h' => h ((certificateEndpointDiagram_identity_cond r c).mp h')), if_neg h]

/-- The transposed 0/5 swap is exactly Ω on that pair and identity on all minor registers. -/
theorem certificateEndpointDiagram_omega :
    certificateLocalDiagram (n := Fin 3) (R := ℂ) {5} (Equiv.swap 0 5) =
      certificateLocalPairLift (omegaOp (Fin 3)) := by
  ext r c
  rw [certificateLocalDiagram_entry, certificateLocalPairLift_omega_apply]
  by_cases h : (r 0 = r 5 ∧ c 0 = c 5) ∧ r 1 = c 1 ∧ r 2 = c 2 ∧ r 3 = c 3 ∧ r 4 = c 4
  · rw [if_pos ((certificateEndpointDiagram_omega_cond r c).mpr h), if_pos h]
  · rw [if_neg (fun h' => h ((certificateEndpointDiagram_omega_cond r c).mp h')), if_neg h]

/-- Exactly two nonzero local diagram coefficients, before taking three tensor copies. -/
def certificateEndpointDiagramWeight (σ : Equiv.Perm (Fin 6)) : ℂ :=
  (if σ = 1 then 1 else 0) - (1 / 2) * (if σ = Equiv.swap 0 5 then 1 else 0)

theorem certificateEndpointDiagram_combination :
    certificateLocalDiagramCombination {5} certificateEndpointDiagramWeight =
      certificateLocalPairLift (1 - (1 / 2 : ℂ) • omegaOp (Fin 3)) := by
  have hs : certificateLocalDiagramCombination {5} certificateEndpointDiagramWeight =
      certificateLocalDiagram {5} 1 -
        (1 / 2 : ℂ) • certificateLocalDiagram {5} (Equiv.swap 0 5) := by
    unfold certificateLocalDiagramCombination certificateEndpointDiagramWeight
    simp only [sub_smul, mul_smul, Finset.sum_sub_distrib]
    rw [← Finset.smul_sum]
    simp [ite_smul]
  rw [hs, certificateEndpointDiagram_identity, certificateEndpointDiagram_omega]
  ext r c
  simp only [certificateLocalPairLift, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- The inverse site regrouping, written out (definitional). -/
theorem certificateSiteRegroupEquiv_symm_apply
    (w : CertificateLocalWord × CertificateLocalWord × CertificateLocalWord) :
    certificateSiteRegroupEquiv.symm w =
      ((((w.1 0, w.2.1 0, w.2.2 0), (w.1 5, w.2.1 5, w.2.2 5)),
        ((w.1 1, w.2.1 1, w.2.2 1), (w.1 2, w.2.1 2, w.2.2 2))),
        ((w.1 3, w.2.1 3, w.2.2 3), (w.1 4, w.2.1 4, w.2.2 4))) := rfl

/-- `liftRowCol` with its two identity factors written as indicators. -/
theorem certificate_liftRowCol_apply {r b c : Type*} [DecidableEq b] [DecidableEq c]
    (T : Matrix r r ℂ) (x y : (r × b) × c) :
    liftRowCol T x y =
      T x.1.1 y.1.1 * (if x.1.2 = y.1.2 then 1 else 0) * (if x.2 = y.2 then 1 else 0) := by
  simp only [liftRowCol, Matrix.one_apply]

/-- The indicator of a pair equality factors (for any decidability instance of the pair
equality, so that rewriting does not depend on how the instance was produced). -/
theorem certificate_ind_pair {α β : Type*} [DecidableEq α] [DecidableEq β]
    (a c : α) (b d : β) {_ : Decidable ((a, b) = (c, d))} :
    (if (a, b) = (c, d) then (1 : ℂ) else 0) =
      (if a = c then 1 else 0) * (if b = d then 1 else 0) := by
  by_cases h1 : a = c <;> by_cases h2 : b = d <;> simp [h1, h2]

/-- Regrouping three pair operators retains every identity factor on the four minor registers. -/
theorem certificateRegroupMatrix_lift_tripleCopy
    (M : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) :
    certificateRegroupMatrix (liftRowCol (tripleCopy M)) =
      certificateLocalPairLift M ⊗ₖ
        (certificateLocalPairLift M ⊗ₖ certificateLocalPairLift M) := by
  ext ⟨r₁, r₂, r₃⟩ ⟨c₁, c₂, c₃⟩
  simp only [certificateRegroupMatrix, Matrix.submatrix_apply]
  rw [certificateSiteRegroupEquiv_symm_apply, certificateSiteRegroupEquiv_symm_apply]
  simp only [certificate_liftRowCol_apply, Matrix.kroneckerMap_apply, certificateLocalPairLift,
    tripleCopy, certificate_ind_pair]
  ring

/-- `(M ⊗ M ⊗ M)^Γ = M^Γ ⊗ M^Γ ⊗ M^Γ`. -/
theorem certificate_partialTranspose_tripleCopy_core {m n : Type*}
    (ρ : Matrix (m × n) (m × n) ℂ) :
    partialTranspose (tripleCopy ρ) = tripleCopy (partialTranspose ρ) := by
  ext x y
  rfl

/-- Three copies of a scalar multiple. -/
theorem certificate_tripleCopy_smul_core {m n : Type*} (z : ℂ) (M : Matrix (m × n) (m × n) ℂ) :
    tripleCopy (z • M) = z ^ 3 • tripleCopy M := by
  ext x y
  simp only [tripleCopy, Matrix.smul_apply, smul_eq_mul]
  ring

/-- The exact `(15/2)^3` Werner normalization gives three copies of `I - Ω/2`. -/
theorem certificateEndpointOperator_tripleCopy :
    endpointOperator = tripleCopy
      ((1 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) -
        (1 / 2 : ℂ) • omegaOp (Fin 3)) := by
  have hw : partialTranspose (werner 3 (1 / 2)) = (2 / 15 : ℂ) •
      ((1 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) -
        (1 / 2 : ℂ) • omegaOp (Fin 3)) := by
    rw [partialTranspose_werner]
    norm_num
  rw [endpointOperator, certificate_partialTranspose_tripleCopy_core, hw,
    certificate_tripleCopy_smul_core, smul_smul]
  norm_num

/-- The actual six-register endpoint is the tensor cube of the exact two-coefficient diagram. -/
theorem certificateSixRegisterOperator_diagram :
    certificateRegroupMatrix sixRegisterOperator =
      certificateLocalDiagramCombination {5} certificateEndpointDiagramWeight ⊗ₖ
        (certificateLocalDiagramCombination {5} certificateEndpointDiagramWeight ⊗ₖ
          certificateLocalDiagramCombination {5} certificateEndpointDiagramWeight) := by
  rw [sixRegisterOperator, certificateEndpointOperator_tripleCopy,
    certificateRegroupMatrix_lift_tripleCopy, certificateEndpointDiagram_combination]

end ThreeCopyQutritWerner
