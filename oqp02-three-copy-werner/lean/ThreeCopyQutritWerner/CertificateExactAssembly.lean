module

public import ThreeCopyQutritWerner.CertificateProjector
public import Mathlib.Tactic.Abel

@[expose] public section


/-!
# Final assembly of the T2.1a certificate in exact supported form

`qutritEndpointInequality_of_explicit_carrier_certificate` (CertificateProjector) needs three
positive semidefinite matrices `Gh, Gm, Ga` on `SixRegisters` and the full Gram identity
eq. (14) for the concrete carrier `Π = certificateQutritCarrier`.

Here `Gh` is *defined* as the residual `Π T Π - Π Γ₃₄(Gm) Π - Π Γ₁₂₃₄(Ga) Π`, so eq. (14) holds
by algebra and the whole certificate content is three positivity statements
(`qutritEndpointInequality_of_exact_residual`). Writing `Gm = G⁰m + Um`, `Ga = G⁰a + Ua`, that
residual is `G⁰h + δ` with `δ = E - Π Γ₃₄(Um) Π - Π Γ₁₂₃₄(Ua) Π` and `E` the complete trial
defect of the manuscript (eq. (residual)); see `certificateExactResidual_repair`. This is
Lemma 4.1's identity part with no range, rank or singular-value premise: those only serve to
produce a correction `U` whose `δ` lies on the holomorphic face. An exact rational correction
witnesses that directly.

`certificate_posSemidef_of_face_margin` is the positivity step on a face: a margin
`G⁰ - γP ⪰ 0`, a perturbation supported on the face projector `P`, and `γI + δ ⪰ 0`.

Nothing here constructs the trial tuple, the correction or the faces; these remain the data
obligations (positivity of the 327 faces, the exact defect, the exact correction) and the
symmetry-reduction bridge that identifies block data with matrices on `SixRegisters`.
-/

noncomputable section

open scoped Matrix ComplexOrder

namespace ThreeCopyQutritWerner

/-- The holomorphic residual left by mixed and antiholomorphic Grams, for the concrete carrier. -/
def certificateExactResidual (Gm Ga : Matrix SixRegisters SixRegisters ℂ) :
    Matrix SixRegisters SixRegisters ℂ :=
  certificateQutritCarrier * sixRegisterOperator * certificateQutritCarrier -
    certificateQutritCarrier * partialTranspose Gm * certificateQutritCarrier -
    certificateQutritCarrier * minorTranspose Ga * certificateQutritCarrier

/-- Eq. (14) holds for the residual by definition. -/
theorem certificateExactResidual_gram (Gm Ga : Matrix SixRegisters SixRegisters ℂ) :
    certificateQutritCarrier * sixRegisterOperator * certificateQutritCarrier =
      certificateExactResidual Gm Ga +
        certificateQutritCarrier * partialTranspose Gm * certificateQutritCarrier +
        certificateQutritCarrier * minorTranspose Ga * certificateQutritCarrier := by
  unfold certificateExactResidual
  abel

/-- FINAL ASSEMBLY: the endpoint inequality follows from two positive semidefinite matrices
whose carrier-compressed holomorphic residual is positive semidefinite. -/
theorem qutritEndpointInequality_of_exact_residual (Gm Ga : Matrix SixRegisters SixRegisters ℂ)
    (hm : Gm.PosSemidef) (ha : Ga.PosSemidef)
    (hh : (certificateExactResidual Gm Ga).PosSemidef) : QutritEndpointInequality :=
  qutritEndpointInequality_of_explicit_carrier_certificate (certificateExactResidual Gm Ga) Gm Ga
    (certificateExactResidual_gram Gm Ga) ⟨hh, hm, ha⟩

/-- Whole-register partial transpose is additive. -/
theorem certificate_partialTranspose_add {m n : Type*} (A B : Matrix (m × n) (m × n) ℂ) :
    partialTranspose (A + B) = partialTranspose A + partialTranspose B := by
  ext x y
  simp only [partialTranspose, Matrix.add_apply]

/-- The simultaneous transpose of both minor pairs is additive. -/
theorem certificate_minorTranspose_add {r b c : Type*}
    (A B : Matrix ((r × b) × c) ((r × b) × c) ℂ) :
    minorTranspose (A + B) = minorTranspose A + minorTranspose B := by
  ext x y
  simp only [minorTranspose, Matrix.add_apply]

/-- The complete trial defect `E = Π T Π - G⁰h - Π Γ₃₄(G⁰m) Π - Π Γ₁₂₃₄(G⁰a) Π`
(manuscript eq. (residual)); no block is dropped. -/
def certificateExactTrialDefect (G0h G0m G0a : Matrix SixRegisters SixRegisters ℂ) :
    Matrix SixRegisters SixRegisters ℂ :=
  certificateQutritCarrier * sixRegisterOperator * certificateQutritCarrier - G0h -
    certificateQutritCarrier * partialTranspose G0m * certificateQutritCarrier -
    certificateQutritCarrier * minorTranspose G0a * certificateQutritCarrier

/-- The holomorphic correction `δ = E - Π Γ₃₄(Um) Π - Π Γ₁₂₃₄(Ua) Π` of Lemma 4.1. -/
def certificateExactHolomorphicCorrection (G0h G0m G0a Um Ua : Matrix SixRegisters SixRegisters ℂ) :
    Matrix SixRegisters SixRegisters ℂ :=
  certificateExactTrialDefect G0h G0m G0a -
    certificateQutritCarrier * partialTranspose Um * certificateQutritCarrier -
    certificateQutritCarrier * minorTranspose Ua * certificateQutritCarrier

/-- Lemma 4.1, identity part: the residual of the corrected tuple is `G⁰h + δ`. -/
theorem certificateExactResidual_repair (G0h G0m G0a Um Ua : Matrix SixRegisters SixRegisters ℂ) :
    certificateExactResidual (G0m + Um) (G0a + Ua) =
      G0h + certificateExactHolomorphicCorrection G0h G0m G0a Um Ua := by
  unfold certificateExactResidual certificateExactHolomorphicCorrection certificateExactTrialDefect
  rw [certificate_partialTranspose_add, certificate_minorTranspose_add]
  simp only [Matrix.mul_add, Matrix.add_mul]
  abel

/-- Exact supported repair: positivity of the corrected mixed and antiholomorphic Grams and of
`G⁰h + δ` proves T2.1a. -/
theorem qutritEndpointInequality_of_supported_repair
    (G0h G0m G0a Um Ua : Matrix SixRegisters SixRegisters ℂ)
    (hm : (G0m + Um).PosSemidef) (ha : (G0a + Ua).PosSemidef)
    (hh : (G0h + certificateExactHolomorphicCorrection G0h G0m G0a Um Ua).PosSemidef) :
    QutritEndpointInequality := by
  apply qutritEndpointInequality_of_exact_residual (G0m + Um) (G0a + Ua) hm ha
  rw [certificateExactResidual_repair G0h G0m G0a Um Ua]
  exact hh

/-- Positivity on a face: a margin `G - γP ⪰ 0` on the face projector `P`, a perturbation
supported on that face (`P δ P = δ`), and `γI + δ ⪰ 0` give `G + δ ⪰ 0`. -/
theorem certificate_posSemidef_of_face_margin {n : Type*} [Fintype n] [DecidableEq n]
    (G δ P : Matrix n n ℂ) (γ : ℝ)
    (hG : (G - (γ : ℂ) • P).PosSemidef) (hP : Pᴴ = P) (hPP : P * P = P)
    (hsupp : P * δ * P = δ)
    (hsmall : ((γ : ℂ) • (1 : Matrix n n ℂ) + δ).PosSemidef) :
    (G + δ).PosSemidef := by
  have h1 : (Pᴴ * ((γ : ℂ) • (1 : Matrix n n ℂ) + δ) * P).PosSemidef :=
    hsmall.conjTranspose_mul_mul_same P
  have h2 : Pᴴ * ((γ : ℂ) • (1 : Matrix n n ℂ) + δ) * P = (γ : ℂ) • P + δ := by
    rw [hP, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      hPP, hsupp]
  have h3 : G + δ = (G - (γ : ℂ) • P) + ((γ : ℂ) • P + δ) := by abel
  rw [h3]
  rw [h2] at h1
  exact hG.add h1

end ThreeCopyQutritWerner

end
