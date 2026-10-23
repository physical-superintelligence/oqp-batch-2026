module

public import ThreeCopyQutritWerner.JointShadowBound
public import ThreeCopyQutritWerner.CoherentReserveEquality

@[expose] public section


/-!
# The exact coherent-shadow combination

The two lower bounds use the same balanced two-column factors. Their weighted
average retains the reserve square, logical marginal slack and original overlap
terms. Scalar compression cancellation is a separate next step.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace ThreeCopyQutritWerner

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] [DecidableEq c]

/-- The actual coherent endpoint bound B_P. -/
def coherentShadowP (X Y : Matrix (a × b × c) (Fin 2) ℂ) : ℝ :=
  (2 * invN (X * Yᴴ) - invT (X * Yᴴ)) / 8 -
    coherentReserveMixed (X * Xᴴ) (Y * Yᴴ) -
    Real.sqrt (zeroReserve (X * Xᴴ) * zeroReserve (Y * Yᴴ))

/-- The exact original-coordinate right side of the QR7 combination. -/
def coherentShadowFloor (X Y : Matrix (a × b × c) (Fin 2) ℂ) : ℝ :=
  (2 * invN (X * Yᴴ) - frobSq X ^ 2) / 6 +
    (Real.sqrt (zeroReserve (X * Xᴴ)) - Real.sqrt (zeroReserve (Y * Yᴴ))) ^ 2 / 6 -
    (hsInner (X * Xᴴ) (Y * Yᴴ)).re / 12 + invT (X * Yᴴ) / 24 +
    (2 * jointShadowMarginalDefect X Y - invB (X * Xᴴ - Y * Yᴴ)) / 24

/-- QR7 with the actual reserves, marginal defect and reduced-overlap terms. -/
theorem coherentShadow_weighted_identity (X Y : Matrix (a × b × c) (Fin 2) ℂ)
    (hn : 2 ≤ Fintype.card (a × b × c)) (hG : Xᴴ * X = Yᴴ * Y) :
    (coherentShadowP X Y + 2 * jointShadowLowerBound X Y) / 3 = coherentShadowFloor X Y := by
  have hx : 0 ≤ zeroReserve (X * Xᴴ) := by
    simpa [coherentPositiveSource] using coherentPositiveSource_reserve_nonneg X 0 0 hn
  have hy : 0 ≤ zeroReserve (Y * Yᴴ) := by
    simpa [coherentPositiveSource] using coherentPositiveSource_reserve_nonneg Y 0 0 hn
  have hsx := Real.sq_sqrt hx
  have hsy := Real.sq_sqrt hy
  obtain ⟨hX, hY, hw⟩ := jointShadow_balanced_norms X Y hG
  have hNX : invN (X * Xᴴ) = invN (X * Yᴴ) := hX
  have hNY : invN (Y * Yᴴ) = invN (X * Yᴴ) := hY
  have hTX : invT (X * Xᴴ) = frobSq X ^ 2 := by
    rw [invT, jointShadow_trace_source, Complex.normSq_ofReal, pow_two]
  have hTY : invT (Y * Yᴴ) = frobSq Y ^ 2 := by
    rw [invT, jointShadow_trace_source, Complex.normSq_ofReal, pow_two]
  unfold coherentShadowP jointShadowLowerBound coherentShadowFloor
  rw [Real.sqrt_mul hx, jointShadowS3_sub, jointShadow_invB_sub]
  simp only [endpointEnergy, energy, zeroReserve, coherentReserveMixed,
    jointShadowCrossA, jointShadowCrossB] at hsx hsy ⊢
  simp only [hTX, hTY, hNX, hNY, hw] at hsx hsy ⊢
  nlinarith only [hsx, hsy]

/-- The exact combined floor holds for every balanced two-column source pair. -/
theorem coherentShadow_endpoint_lower_bound (X Y : Matrix (a × b × c) (Fin 2) ℂ)
    (hn : 2 ≤ Fintype.card (a × b × c)) (hG : Xᴴ * X = Yᴴ * Y) :
    coherentShadowFloor X Y ≤ endpointEnergy (X * Yᴴ) := by
  have hp : coherentShadowP X Y ≤ endpointEnergy (X * Yᴴ) :=
    coherentEndpoint_lower_bound X Y hn
  have hj := jointShadow_lower_bound X Y hG
  have h := coherentShadow_weighted_identity X Y hn hG
  linarith

end ThreeCopyQutritWerner
