module

public import ThreeCopyQutritWerner.SharpRankOneFamily
public import ThreeCopyQutritWerner.SharpGammaFamilyAdjoint

@[expose] public section


/-!
# Opposite fixed-factor orientations cannot form three gamma-one rays

For u_i = a tensor y_i and v_i = x_i tensor b, orthogonality kills both
off-diagonal partial-trace pairings. Gamma is then minus the scalar trace
product. A three-cycle of gamma-one equations would make a nonpositive real
number equal one. Fixed local factors need not be supplied normalized.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

def sharpProductVector {L R : Type*} (a : L → ℂ) (b : R → ℂ) : L × R → ℂ :=
  fun p => a p.1 * b p.2

theorem sharpProductVector_braket {L R : Type*} [Fintype L] [Fintype R]
    (a c : L → ℂ) (b d : R → ℂ) :
    braket (sharpProductVector a b) (sharpProductVector c d) = braket a c * braket b d := by
  simp only [braket, sharpProductVector, Fintype.sum_prod_type, map_mul,
    Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem sharpProductVector_ptraceL {L R : Type*} [Fintype L] [Fintype R]
    (a c : L → ℂ) (b d : R → ℂ) :
    ptraceL (ketBra (sharpProductVector a b) (sharpProductVector c d)) =
      braket c a • ketBra b d := by
  ext i j
  simp only [ptraceL, ketBra, sharpProductVector, braket, Matrix.smul_apply,
    smul_eq_mul, map_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem sharpProductVector_ptraceR {L R : Type*} [Fintype L] [Fintype R]
    (a c : L → ℂ) (b d : R → ℂ) :
    ptraceR (ketBra (sharpProductVector a b) (sharpProductVector c d)) =
      braket d b • ketBra a c := by
  ext i j
  simp only [ptraceR, ketBra, sharpProductVector, braket, Matrix.smul_apply,
    smul_eq_mul, map_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- A nonzero vector has nonzero self pairing. -/
theorem sharp_braket_self_ne_zero {n : Type*} [Fintype n]
    (x : n → ℂ) (hx : ∃ i, x i ≠ 0) : braket x x ≠ 0 := by
  intro h
  have hn : vecNormSq x = 0 := by
    rw [braket_self] at h
    exact_mod_cast h
  obtain ⟨i, hi⟩ := hx
  exact hi (eq_zero_of_vecNormSq_eq_zero x hn i)

/-- Opposite fixed-factor product families have only the negative trace
product in their off-diagonal gamma entry. -/
theorem sharpProductVector_opposite_gamma
    {L R : Type*} [Fintype L] [Fintype R]
    (a : L → ℂ) (b : R → ℂ) (x x' : L → ℂ) (y y' : R → ℂ)
    (ha : ∃ l, a l ≠ 0) (hb : ∃ r, b r ≠ 0)
    (hu : braket (sharpProductVector a y) (sharpProductVector a y') = 0)
    (hv : braket (sharpProductVector x b) (sharpProductVector x' b) = 0) :
    sharpPartialTraceGamma (sharpProductVector a y) (sharpProductVector x b)
      (sharpProductVector a y') (sharpProductVector x' b) =
        -conj ((ketBra (sharpProductVector a y) (sharpProductVector x b)).trace) *
          (ketBra (sharpProductVector a y') (sharpProductVector x' b)).trace := by
  rw [sharpProductVector_braket] at hu hv
  have hy : braket y y' = 0 := (mul_eq_zero.mp hu).resolve_left (sharp_braket_self_ne_zero a ha)
  have hx : braket x x' = 0 := (mul_eq_zero.mp hv).resolve_right (sharp_braket_self_ne_zero b hb)
  unfold sharpPartialTraceGamma ptraceInner
  rw [sharpProductVector_ptraceL, sharpProductVector_ptraceL,
    sharpProductVector_ptraceR, sharpProductVector_ptraceR,
    zeroReserve_hsInner_smul, zeroReserve_hsInner_smul,
    hsInner_ketBra, hsInner_ketBra, hy, hx]
  simp only [map_zero, mul_zero, zero_mul, zero_add, zero_sub, neg_mul]

/-- Three negative scalar cross products cannot all equal one. -/
theorem sharp_negative_trace_three_cycle (z₀ z₁ z₂ : ℂ)
    (h01 : -conj z₀ * z₁ = 1) (h12 : -conj z₁ * z₂ = 1)
    (h20 : -conj z₂ * z₀ = 1) : False := by
  have he : -((Complex.normSq z₀ * Complex.normSq z₁ * Complex.normSq z₂ : ℝ) : ℂ) = 1 := by
    calc
      _ = (-conj z₀ * z₁) * (-conj z₁ * z₂) * (-conj z₂ * z₀) := by
        simp only [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
        ring
      _ = 1 := by rw [h01, h12, h20]; norm_num
  have hre := congrArg Complex.re he
  simp only [Complex.neg_re, Complex.ofReal_re, Complex.one_re] at hre
  have hnon := mul_nonneg (mul_nonneg (Complex.normSq_nonneg z₀)
    (Complex.normSq_nonneg z₁)) (Complex.normSq_nonneg z₂)
  linarith

/-- Three distinct orthonormal gamma-one rays cannot have opposite fixed
local factors. This leaves the shared-factor orientation for the rank-three
all-product branch. -/
theorem sharpProductFamily_opposite_orientation_impossible
    {ι L R : Type*} [Fintype L] [Fintype R] [DecidableEq ι]
    (a : L → ℂ) (b : R → ℂ) (x : ι → L → ℂ) (y : ι → R → ℂ)
    (ha : ∃ l, a l ≠ 0) (hb : ∃ r, b r ≠ 0)
    (hu : ∀ i j, braket (sharpProductVector a (y i)) (sharpProductVector a (y j)) =
      if i = j then 1 else 0)
    (hv : ∀ i j, braket (sharpProductVector (x i) b) (sharpProductVector (x j) b) =
      if i = j then 1 else 0)
    (hg : ∀ i j, sharpPartialTraceGamma (sharpProductVector a (y i))
      (sharpProductVector (x i) b) (sharpProductVector a (y j))
      (sharpProductVector (x j) b) = 1)
    (i j k : ι) (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i) : False := by
  let z (r : ι) := (ketBra (sharpProductVector a (y r)) (sharpProductVector (x r) b)).trace
  have hp (r s : ι) (hrs : r ≠ s) : -conj (z r) * z s = 1 := by
    have h := hg r s
    rw [sharpProductVector_opposite_gamma a b (x r) (x s) (y r) (y s) ha hb
      (by rw [hu, if_neg hrs]) (by rw [hv, if_neg hrs])] at h
    exact h
  exact sharp_negative_trace_three_cycle (z i) (z j) (z k) (hp i j hij) (hp j k hjk) (hp k i hki)

end ThreeCopyQutritWerner
