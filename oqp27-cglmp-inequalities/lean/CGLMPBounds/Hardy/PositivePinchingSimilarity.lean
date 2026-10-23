module

public import CGLMPBounds.Hardy.PositivePinchingAlgebra

@[expose] public section


/-! The block-balancing similarity in C.4, constructed without choosing a basis.
The balancing matrix is a linear polynomial in the Hermitian involution B.
Its two scalar eigenvalues are sqrt(1-x) and sqrt(1+x). -/

namespace CGLMPBounds.Hardy
noncomputable section
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma involution_linear_factor_mul {B : Matrix ι ι ℂ} (hB2 : B ^ 2 = 1)
    (a b c d : ℂ) :
    (a • (1 : Matrix ι ι ℂ) + b • B) * (c • 1 + d • B) =
      (a * c + b * d) • (1 : Matrix ι ι ℂ) + (a * d + b * c) • B := by
  have hBB : B * B = 1 := by simpa only [pow_two] using hB2
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, smul_smul, hBB]
  module

lemma involution_linear_factor_commute {B : Matrix ι ι ℂ} (a b : ℂ) :
    (a • (1 : Matrix ι ι ℂ) + b • B) * B =
      B * (a • (1 : Matrix ι ι ℂ) + b • B) := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

lemma positivePinching_even_sandwich {B Y : Matrix ι ι ℂ}
    (hB2 : B ^ 2 = 1) (a b : ℂ) :
    (a • (1 : Matrix ι ι ℂ) + b • B) * positivePinchingPart B Y *
      (a • 1 + b • B) =
    (a ^ 2 + b ^ 2) • positivePinchingPart B Y +
      (2 * a * b) • (B * positivePinchingPart B Y) := by
  calc
    _ = a ^ 2 • positivePinchingPart B Y +
        (a * b) • (positivePinchingPart B Y * B) +
        (b * a) • (B * positivePinchingPart B Y) +
        b ^ 2 • (B * positivePinchingPart B Y * B) := by
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
        one_mul, mul_one, smul_smul]
      module
    _ = _ := by
      rw [positivePinching_part_conjugate hB2,
        ← positivePinching_part_commute hB2]
      module

lemma positivePinching_odd_sandwich {B Y : Matrix ι ι ℂ}
    (hB2 : B ^ 2 = 1) (a b : ℂ) :
    (a • (1 : Matrix ι ι ℂ) + b • B) * positivePinchingOffdiag B Y *
      (a • 1 + b • B) = (a ^ 2 - b ^ 2) • positivePinchingOffdiag B Y := by
  have hanti : positivePinchingOffdiag B Y * B =
      -(B * positivePinchingOffdiag B Y) := by
    have h := positivePinching_offdiag_anticommute (Y := Y) hB2
    rw [h, neg_neg]
  calc
    _ = a ^ 2 • positivePinchingOffdiag B Y +
        (a * b) • (positivePinchingOffdiag B Y * B) +
        (b * a) • (B * positivePinchingOffdiag B Y) +
        b ^ 2 • (B * positivePinchingOffdiag B Y * B) := by
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
        one_mul, mul_one, smul_smul]
      module
    _ = _ := by
      rw [positivePinching_offdiag_conjugate hB2, hanti]
      module

/-- The three actual scalar identities needed by the balancing similarity. -/
lemma positivePinching_balance_coefficients {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    let a := (Real.sqrt (1 - x) + Real.sqrt (1 + x)) / 2
    let b := (Real.sqrt (1 - x) - Real.sqrt (1 + x)) / 2
    a ^ 2 + b ^ 2 = 1 ∧ 2 * a * b = -x ∧
      a ^ 2 - b ^ 2 = Real.sqrt (1 - x ^ 2) := by
  have hu : 0 ≤ 1 - x := by linarith [hx.2]
  have hv : 0 ≤ 1 + x := by linarith [hx.1]
  have hu2 := Real.sq_sqrt hu
  have hv2 := Real.sq_sqrt hv
  have hm : Real.sqrt (1 - x) * Real.sqrt (1 + x) = Real.sqrt (1 - x ^ 2) := by
    rw [← Real.sqrt_mul hu]
    congr 1
    ring
  dsimp
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

lemma positivePinching_balanced_middle {B Y : Matrix ι ι ℂ}
    (hB2 : B ^ 2 = 1) (a b x y δ : ℂ)
    (hplus : a ^ 2 + b ^ 2 = 1) (hcross : 2 * a * b = -x)
    (hminus : a ^ 2 - b ^ 2 = δ) :
    B * ((a • (1 : Matrix ι ι ℂ) + b • B) * (Y - y • 1) *
      (a • 1 + b • B)) =
      (B - x • (1 : Matrix ι ι ℂ)) * (positivePinchingPart B Y - y • 1) +
        δ • (B * positivePinchingOffdiag B Y) := by
  have hBB : B * B = 1 := by simpa only [pow_two] using hB2
  have hdecomp : Y = positivePinchingPart B Y + positivePinchingOffdiag B Y :=
    (positivePinching_part_add_offdiag B Y).symm
  have hmid : (a • (1 : Matrix ι ι ℂ) + b • B) * (Y - y • 1) *
      (a • 1 + b • B) =
      positivePinchingPart B Y - x • (B * positivePinchingPart B Y) +
        δ • positivePinchingOffdiag B Y - y • (1 - x • B) := by
    calc
      _ = (a • (1 : Matrix ι ι ℂ) + b • B) * positivePinchingPart B Y *
          (a • 1 + b • B) +
        (a • (1 : Matrix ι ι ℂ) + b • B) * positivePinchingOffdiag B Y *
          (a • 1 + b • B) -
        y • ((a • (1 : Matrix ι ι ℂ) + b • B) * (a • 1 + b • B)) := by
          conv_lhs => rw [hdecomp]
          simp only [mul_sub, sub_mul, mul_add, add_mul, mul_smul_comm,
            smul_mul_assoc, mul_one]
          module
      _ = _ := by
        rw [positivePinching_even_sandwich hB2, positivePinching_odd_sandwich hB2,
          involution_linear_factor_mul hB2]
        have hprod : a * a + b * b = 1 := by linear_combination hplus
        have hsum : a * b + b * a = -x := by linear_combination hcross
        rw [hplus, hcross, hminus, hprod, hsum]
        module
  rw [hmid]
  simp only [mul_sub, mul_add, mul_smul_comm, sub_mul,
    smul_mul_assoc, one_mul, mul_one, ← mul_assoc, hBB, smul_smul]
  module

/-- Actual source pencil similarity. The matrix U is an invertible change of
basis constructed from B; the final perturbation has exactly sqrt(1-x²). -/
theorem positivePinching_exists_balancing_unit {B Y : Matrix ι ι ℂ}
    (hB2 : B ^ 2 = 1) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (y : ℝ) :
    ∃ U : (Matrix ι ι ℂ)ˣ,
      (↑U⁻¹ : Matrix ι ι ℂ) *
        ((B - (x : ℂ) • 1) * (Y - (y : ℂ) • 1)) * (U : Matrix ι ι ℂ) =
      (B - (x : ℂ) • 1) * (positivePinchingPart B Y - (y : ℂ) • 1) +
        (Real.sqrt (1 - x ^ 2) : ℂ) • (B * positivePinchingOffdiag B Y) := by
  let a : ℂ := ((Real.sqrt (1 - x) + Real.sqrt (1 + x)) / 2 : ℝ)
  let b : ℂ := ((Real.sqrt (1 - x) - Real.sqrt (1 + x)) / 2 : ℝ)
  let δ : ℂ := Real.sqrt (1 - x ^ 2)
  obtain ⟨hp, hc, hm⟩ := positivePinching_balance_coefficients hx
  have hp' : a ^ 2 + b ^ 2 = 1 := by
    dsimp [a, b]
    exact_mod_cast hp
  have hc' : 2 * a * b = -(x : ℂ) := by
    dsimp [a, b]
    exact_mod_cast hc
  have hm' : a ^ 2 - b ^ 2 = δ := by
    dsimp [a, b, δ]
    exact_mod_cast hm
  have hδ : δ ≠ 0 := by
    dsimp [δ]
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (positivePinching_strip_denominator_pos hx)))
  let S : Matrix ι ι ℂ := a • 1 + b • B
  let T : Matrix ι ι ℂ := δ⁻¹ • (a • 1 + (-b) • B)
  have hTS : T * S = 1 := by
    dsimp [T, S]
    rw [smul_mul_assoc, involution_linear_factor_mul hB2]
    have h1 : a * a + -b * b = δ := by linear_combination hm'
    have h0 : a * b + -b * a = 0 := by ring
    rw [h1, h0, zero_smul, add_zero, smul_smul, inv_mul_cancel₀ hδ, one_smul]
  have hST : S * T = 1 := (Matrix.mul_eq_one_comm_of_card_eq (ι) (ι) ℂ rfl).mp hTS
  let U : (Matrix ι ι ℂ)ˣ := ⟨S, T, hST, hTS⟩
  refine ⟨U, ?_⟩
  change T * ((B - (x : ℂ) • 1) * (Y - (y : ℂ) • 1)) * S = _
  have hS2 : S * S = 1 - (x : ℂ) • B := by
    dsimp [S]
    rw [involution_linear_factor_mul hB2]
    have h1 : a * a + b * b = 1 := by linear_combination hp'
    have h2 : a * b + b * a = -(x : ℂ) := by linear_combination hc'
    rw [h1, h2]
    module
  have hBB : B * B = 1 := by simpa only [pow_two] using hB2
  have hP : B - (x : ℂ) • (1 : Matrix ι ι ℂ) = B * (S * S) := by
    rw [hS2, mul_sub, mul_smul_comm, hBB, mul_one]
  have hTB : T * B = B * T := by
    dsimp [T]
    rw [smul_mul_assoc, mul_smul_comm, involution_linear_factor_commute]
  calc
    _ = B * (S * (Y - (y : ℂ) • 1) * S) := by
      rw [hP]
      calc
        _ = (T * B) * S * S * (Y - (y : ℂ) • 1) * S := by noncomm_ring
        _ = B * (T * S) * S * (Y - (y : ℂ) • 1) * S := by
          rw [hTB]
          noncomm_ring
        _ = _ := by rw [hTS, mul_one]; noncomm_ring
    _ = _ := positivePinching_balanced_middle hB2 a b (x : ℂ) (y : ℂ) δ hp' hc' hm'

end
end CGLMPBounds.Hardy
