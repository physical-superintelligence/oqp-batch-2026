module

public import ThreeCopyQutritWerner.CertificateExactAssembly
public import ThreeCopyQutritWerner.CertificateFrameRealization
public import ThreeCopyQutritWerner.CertificateSiteRegroup
public import ThreeCopyQutritWerner.CertificateX2BridgeActions

@[expose] public section


/-!
# Operator-level assembly on a complete h frame basis

Let `S` be a complete frame basis of the three-site space (columns grouped by frames `f`, each
of a type `type f`, with a positive definite metric per type and the scalar overlap structure
of `certificate_exists_positive_frame_realization`). Suppose the regrouped carrier `Π`, the
regrouped endpoint operator `T`, and the regrouped transfers `Γ₃₄ Gm`, `Γ₁₂₃₄ Ga` act on `S` by
type blocks `π`, `Tt`, `Am`, `Aa`. Then the regrouped residual `Π (T - Γ₃₄ Gm - Γ₁₂₃₄ Ga) Π`
acts by `π (Tt - Am - Aa) π`; if every `G t * π t (Tt t - Am t - Aa t) π t` (its Q-form) is
positive semidefinite, the residual is positive semidefinite, and with `Gm`, `Ga` positive
semidefinite the endpoint inequality follows.

For the certificate, `S` is `certificateThreeSiteFrameSystem0.basis`, `π` is
`certificateCarrierJointAction0` (`certificateCarrierJointAction0_physical`), and `Tt` comes from
`certificateSixRegisterOperator_source_action`; the transfers act through
`certificateGlobalDiagramActions0` once `Gm`, `Ga` are global diagram combinations.
-/

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace ThreeCopyQutritWerner

/-- Regrouping commutes with subtraction. -/
theorem x2Regroup_sub (M N : Matrix SixRegisters SixRegisters ℂ) :
    certificateRegroupMatrix (M - N) = certificateRegroupMatrix M - certificateRegroupMatrix N := by
  ext i j
  simp only [certificateRegroupMatrix, Matrix.submatrix_apply, Matrix.sub_apply]

/-- Positivity returns from the regrouped matrix. -/
theorem x2_posSemidef_of_regroup (M : Matrix SixRegisters SixRegisters ℂ)
    (h : (certificateRegroupMatrix M).PosSemidef) : M.PosSemidef := by
  have h2 := h.submatrix certificateSiteRegroupEquiv
  have he : (certificateRegroupMatrix M).submatrix certificateSiteRegroupEquiv
      certificateSiteRegroupEquiv = M := by
    ext i j
    simp only [certificateRegroupMatrix, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rwa [he] at h2

/-- THE ASSEMBLY: the exact residual is positive semidefinite when its type-block Q-forms are. -/
theorem x2_exactResidual_posSemidef_of_actions
    {F T : Type*} [Fintype F] [DecidableEq F] [Fintype T] [DecidableEq T]
    (size : T → ℕ) (type : F → T) (pivot : (t : T) → Fin (size t))
    (S : Matrix (CertificateLocalWord × CertificateLocalWord × CertificateLocalWord)
      (Σ f, Fin (size (type f))) ℂ)
    (G : (t : T) → Matrix (Fin (size t)) (Fin (size t)) ℂ) (K : Matrix F F ℂ)
    (hS : Function.Bijective S.mulVec) (hG : ∀ t, (G t).PosDef)
    (hGram : Sᴴ * S = certificateRepeatedFrameMetric size type G K)
    (hzero : ∀ f f', type f ≠ type f' → K f f' = 0)
    (Gm Ga : Matrix SixRegisters SixRegisters ℂ)
    (π Tt Am Aa : (t : T) → Matrix (Fin (size t)) (Fin (size t)) ℂ)
    (hπ : X2Acts S (certificateRegroupMatrix certificateQutritCarrier) (fun f => π (type f)))
    (hT : X2Acts S (certificateRegroupMatrix sixRegisterOperator) (fun f => Tt (type f)))
    (hAm : X2Acts S (certificateRegroupMatrix (partialTranspose Gm)) (fun f => Am (type f)))
    (hAa : X2Acts S (certificateRegroupMatrix (minorTranspose Ga)) (fun f => Aa (type f)))
    (hpsd : ∀ t, (G t * (π t * (Tt t - Am t - Aa t) * π t)).PosSemidef) :
    (certificateExactResidual Gm Ga).PosSemidef := by
  apply x2_posSemidef_of_regroup
  have h := (((hπ.mul hT).mul hπ).sub ((hπ.mul hAm).mul hπ)).sub ((hπ.mul hAa).mul hπ)
  have hR : X2Acts S (certificateRegroupMatrix (certificateExactResidual Gm Ga))
      (fun f => π (type f) * (Tt (type f) - Am (type f) - Aa (type f)) * π (type f)) := by
    unfold certificateExactResidual
    simp only [x2Regroup_sub, certificateRegroupMatrix_mul, Matrix.mul_sub, Matrix.sub_mul]
    exact h
  obtain ⟨M, hM, hMS⟩ := certificate_exists_positive_frame_realization size type pivot S G
    (fun t => π t * (Tt t - Am t - Aa t) * π t) K hS hG hGram hzero hpsd
  exact hR.posSemidef_of_realize hS.2 ⟨M, hM, hMS⟩

/-- The endpoint inequality from positive transfers whose residual Q-forms are positive. -/
theorem x2_qutritEndpointInequality_of_actions
    {F T : Type*} [Fintype F] [DecidableEq F] [Fintype T] [DecidableEq T]
    (size : T → ℕ) (type : F → T) (pivot : (t : T) → Fin (size t))
    (S : Matrix (CertificateLocalWord × CertificateLocalWord × CertificateLocalWord)
      (Σ f, Fin (size (type f))) ℂ)
    (G : (t : T) → Matrix (Fin (size t)) (Fin (size t)) ℂ) (K : Matrix F F ℂ)
    (hS : Function.Bijective S.mulVec) (hG : ∀ t, (G t).PosDef)
    (hGram : Sᴴ * S = certificateRepeatedFrameMetric size type G K)
    (hzero : ∀ f f', type f ≠ type f' → K f f' = 0)
    (Gm Ga : Matrix SixRegisters SixRegisters ℂ) (hm : Gm.PosSemidef) (ha : Ga.PosSemidef)
    (π Tt Am Aa : (t : T) → Matrix (Fin (size t)) (Fin (size t)) ℂ)
    (hπ : X2Acts S (certificateRegroupMatrix certificateQutritCarrier) (fun f => π (type f)))
    (hT : X2Acts S (certificateRegroupMatrix sixRegisterOperator) (fun f => Tt (type f)))
    (hAm : X2Acts S (certificateRegroupMatrix (partialTranspose Gm)) (fun f => Am (type f)))
    (hAa : X2Acts S (certificateRegroupMatrix (minorTranspose Ga)) (fun f => Aa (type f)))
    (hpsd : ∀ t, (G t * (π t * (Tt t - Am t - Aa t) * π t)).PosSemidef) :
    QutritEndpointInequality :=
  qutritEndpointInequality_of_exact_residual Gm Ga hm ha
    (x2_exactResidual_posSemidef_of_actions size type pivot S G K hS hG hGram hzero Gm Ga
      π Tt Am Aa hπ hT hAm hAa hpsd)

end ThreeCopyQutritWerner

end
