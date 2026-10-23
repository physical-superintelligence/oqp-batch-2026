module

public import CGLMPBounds.Certificates.ScalarCosecant
public import Mathlib.Analysis.Calculus.SmoothSeries

@[expose] public section


/-!
# Differentiating the regularized scalar series

The source phi is y(1-y) times the regularized cosecant. Falling factorials
describe its polynomial summands at every derivative order, including orders
above the degree. Bounds below justify termwise differentiation on (0,1).
-/

namespace CGLMPBounds.Certificates
noncomputable section

def scalarPowerDerivative (n m : ℕ) (y : ℝ) : ℝ :=
  (n.descFactorial m : ℝ) * y ^ (n - m)

def scalarPhiTerm (i m : ℕ) (y : ℝ) : ℝ :=
  scalarCosecantCoefficient (i + 1) *
    (scalarPowerDerivative (2 * i + 2) m y - scalarPowerDerivative (2 * i + 3) m y)

def scalarPhiSeries (m : ℕ) (y : ℝ) : ℝ := ∑' i : ℕ, scalarPhiTerm i m y

def scalarPhiMajorant (m i : ℕ) : ℝ :=
  (8 / 3 : ℝ) * 3 ^ m * ((i : ℝ) + 1) ^ m * (1 / 4 : ℝ) ^ (i + 1)

theorem scalarPowerDerivative_hasDerivAt (n m : ℕ) (y : ℝ) :
    HasDerivAt (scalarPowerDerivative n m) (scalarPowerDerivative n (m + 1) y) y := by
  have h := (hasDerivAt_pow (n - m) y).const_mul (n.descFactorial m : ℝ)
  convert h using 1
  · rfl
  · unfold scalarPowerDerivative
    rw [Nat.descFactorial_succ, Nat.cast_mul,
      show n - (m + 1) = n - m - 1 by omega]
    ring

theorem scalarPhiTerm_hasDerivAt (i m : ℕ) (y : ℝ) :
    HasDerivAt (scalarPhiTerm i m) (scalarPhiTerm i (m + 1) y) y := by
  exact ((scalarPowerDerivative_hasDerivAt (2 * i + 2) m y).sub
    (scalarPowerDerivative_hasDerivAt (2 * i + 3) m y)).const_mul _

theorem scalarPowerDerivative_bound (n m : ℕ) {y : ℝ}
    (hy : y ∈ Set.Icc (0 : ℝ) 1) : |scalarPowerDerivative n m y| ≤ (n : ℝ) ^ m := by
  have hy0 : 0 ≤ y := hy.1
  have hpow : y ^ (n - m) ≤ 1 := pow_le_one₀ hy.1 hy.2
  rw [scalarPowerDerivative, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (n.descFactorial m : ℝ) * 1 := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ ≤ (n : ℝ) ^ m := by
      simpa only [mul_one] using (show (n.descFactorial m : ℝ) ≤ (n : ℝ) ^ m by
        exact_mod_cast Nat.descFactorial_le_pow n m)

theorem scalarPhiTerm_bound (i m : ℕ) {y : ℝ}
    (hy : y ∈ Set.Icc (0 : ℝ) 1) : ‖scalarPhiTerm i m y‖ ≤ scalarPhiMajorant m i := by
  have hc := scalarCosecantCoefficient_pos_lt (i + 1) (by omega)
  have h1 := scalarPowerDerivative_bound (2 * i + 2) m hy
  have h2 := scalarPowerDerivative_bound (2 * i + 3) m hy
  have hb1 : ((2 * i + 2 : ℕ) : ℝ) ^ m ≤ (3 * ((i : ℝ) + 1)) ^ m := by
    apply pow_le_pow_left₀ (by positivity)
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) i]
  have hb2 : ((2 * i + 3 : ℕ) : ℝ) ^ m ≤ (3 * ((i : ℝ) + 1)) ^ m := by
    apply pow_le_pow_left₀ (by positivity)
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) i]
  have ht : |scalarPowerDerivative (2 * i + 2) m y -
      scalarPowerDerivative (2 * i + 3) m y| ≤
      |scalarPowerDerivative (2 * i + 2) m y| +
        |scalarPowerDerivative (2 * i + 3) m y| := by
    simpa only [sub_zero, zero_sub, abs_neg] using
      abs_sub_le (scalarPowerDerivative (2 * i + 2) m y) 0
        (scalarPowerDerivative (2 * i + 3) m y)
  have hs : |scalarPowerDerivative (2 * i + 2) m y -
      scalarPowerDerivative (2 * i + 3) m y| ≤ 2 * (3 * ((i : ℝ) + 1)) ^ m := by
    linarith
  rw [scalarPhiTerm, Real.norm_eq_abs, abs_mul, abs_of_pos hc.1]
  calc
    _ ≤ ((4 / 3 : ℝ) * (1 / 4 : ℝ) ^ (i + 1)) *
        (2 * (3 * ((i : ℝ) + 1)) ^ m) :=
      mul_le_mul hc.2.le hs (abs_nonneg _) (by positivity)
    _ = scalarPhiMajorant m i := by rw [scalarPhiMajorant, mul_pow]; ring

theorem scalarPhiMajorant_summable (m : ℕ) : Summable (scalarPhiMajorant m) := by
  have h := summable_pow_mul_geometric_of_norm_lt_one m
    (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)
  have hs := (summable_nat_add_iff 1).2 h
  have hc := hs.mul_left ((8 / 3 : ℝ) * 3 ^ m)
  change Summable (fun i : ℕ =>
    (8 / 3 : ℝ) * 3 ^ m * ((i : ℝ) + 1) ^ m * (1 / 4 : ℝ) ^ (i + 1))
  simpa only [Nat.cast_add, Nat.cast_one, mul_assoc] using hc

theorem scalarPhiTerm_summable (m : ℕ) {y : ℝ}
    (hy : y ∈ Set.Icc (0 : ℝ) 1) : Summable (fun i => scalarPhiTerm i m y) :=
  Summable.of_norm_bounded (scalarPhiMajorant_summable m) (fun i => scalarPhiTerm_bound i m hy)

theorem scalarPhiSeries_hasDerivAt (m : ℕ) {y : ℝ}
    (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (scalarPhiSeries m) (scalarPhiSeries (m + 1) y) y := by
  apply hasDerivAt_tsum_of_isPreconnected (scalarPhiMajorant_summable (m + 1))
    isOpen_Ioo (convex_Ioo (0 : ℝ) 1).isPreconnected
    (fun i t _ => scalarPhiTerm_hasDerivAt i m t)
    (fun i t ht => scalarPhiTerm_bound i (m + 1) ⟨ht.1.le, ht.2.le⟩)
    (show (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 by norm_num)
    (scalarPhiTerm_summable m (by norm_num : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1)) hy

theorem scalarPhiSeries_zero_order {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    scalarPhiSeries 0 y = y * (1 - y) *
      (1 / Real.sin (Real.pi * y / 2) - 2 / (Real.pi * y)) := by
  have h := (scalar_cosecant_hasSum_zero_le
    (show y ∈ Set.Ico (0 : ℝ) 2 from ⟨hy.1, by linarith [hy.2]⟩)).mul_left (y * (1 - y))
  have he : (fun i : ℕ => scalarPhiTerm i 0 y) =
      (fun i : ℕ => y * (1 - y) * (scalarCosecantCoefficient (i + 1) * y ^ (2 * i + 1))) := by
    ext i
    simp only [scalarPhiTerm, scalarPowerDerivative, Nat.descFactorial_zero,
      Nat.cast_one, one_mul, Nat.sub_zero]
    rw [show 2 * i + 2 = (2 * i + 1) + 1 by omega,
      show 2 * i + 3 = (2 * i + 1) + 2 by omega, pow_add, pow_add]
    ring
  unfold scalarPhiSeries
  rw [he]
  exact h.tsum_eq

end
end CGLMPBounds.Certificates
