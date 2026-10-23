module

public import ThreeCopyQutritWerner.CertificateProjectorCore

@[expose] public section


/-!
# A concrete Hermitian carrier for the endpoint reduction

The carrier below uses exactly the Appendix B `[32]` rational character
sum and the two minor antisymmetrizers. It is written as `A E A`, where
`A=A₁₂A₃₄`, to expose Hermiticity without requiring an additional
representation-theoretic idempotence proof. The theorem needed by
`qutritEndpointInequality_of_certificate` is that it fixes every actual
holomorphic feature.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker ComplexOrder

set_option maxRecDepth 100000

namespace ThreeCopyQutritWerner

/-- Restore the manuscript register order from the statement base's nested product.
The column register is kept separate from the five permuted source registers. -/
def certificateSixRegistersEquiv : SixRegisters ≃
    ((Fin 5 → Fin 3 × Fin 3 × Fin 3) × (Fin 3 × Fin 3 × Fin 3)) where
  toFun x := (![x.1.1.1, x.1.2.1, x.1.2.2, x.2.1, x.2.2], x.1.1.2)
  invFun x := (((x.1 0, x.2), (x.1 1, x.1 2)), (x.1 3, x.1 4))
  left_inv x := rfl
  right_inv x := by
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · rfl

/-- A concrete carrier on the exact six-register space of the endpoint reduction. -/
def certificateQutritCarrier : Matrix SixRegisters SixRegisters ℂ :=
  (certificateHolomorphicCarrier (n := Fin 3 × Fin 3 × Fin 3) ⊗ₖ
    (1 : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ)).submatrix
    certificateSixRegistersEquiv certificateSixRegistersEquiv

theorem certificateQutritCarrier_hermitian :
    certificateQutritCarrierᴴ = certificateQutritCarrier := by
  exact certificateHolomorphicCarrier_reindex_hermitian certificateSixRegistersEquiv

/-- The explicit carrier fixes every actual feature, for arbitrary complex `X,B`. -/
theorem certificateQutritCarrier_fixes
    (X : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 2) ℂ)
    (B : Matrix (Fin 2) (Fin 3 × Fin 3 × Fin 3) ℂ) :
    certificateQutritCarrier *ᵥ featureH (X * B) (bivecMat X) =
      featureH (X * B) (bivecMat X) := by
  exact certificateHolomorphicCarrier_reindex_fixes certificateSixRegistersEquiv X B

/-- The endpoint inequality with no abstract carrier premise: three PSD matrices
satisfying the full Gram identity for the explicit carrier suffice. -/
theorem qutritEndpointInequality_of_explicit_carrier_certificate
    (Gh Gm Ga : Matrix SixRegisters SixRegisters ℂ)
    (hgram : certificateQutritCarrier * sixRegisterOperator * certificateQutritCarrier =
      Gh + certificateQutritCarrier * partialTranspose Gm * certificateQutritCarrier +
        certificateQutritCarrier * minorTranspose Ga * certificateQutritCarrier)
    (hpsd : Gh.PosSemidef ∧ Gm.PosSemidef ∧ Ga.PosSemidef) :
    QutritEndpointInequality :=
  qutritEndpointInequality_of_certificate certificateQutritCarrier Gh Gm Ga
    certificateQutritCarrier_hermitian certificateQutritCarrier_fixes hgram hpsd

end ThreeCopyQutritWerner
