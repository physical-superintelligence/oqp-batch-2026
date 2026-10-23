module

public import CGLMPBounds.Fourier.Entries
public import CGLMPBounds.Defs.CGLMPValue

@[expose] public section


/-!
# The Fourier-phase measurements attain `I_d^F`

Supplement, Theorem A.1 ("Equality holds if … the four PVMs are `Π^t_a ⊗ I_k`") and the proof of
Lemma C.1 ("For `V_j = I`, Fourier conjugation gives (B.2), and the same sum evaluates its value as
(A.1)"): the standard Fourier-phase measurements (B.2) on `Φ_d` attain
`I_d^F = 4/(d(d - 1)) Σ_{h=1}^{d-1} (d - h) sec(πh/(2d))`.

The computation starts from (F.1), `Q_d(a,b|x,y) = f_d(r_{xy})/d` with
`f_d(r) = 1/(2d² sin²(π(r + 1/4)/d))` (`fourierTable_apply`). Then:
* `csc²(π(r + 1/4)/d) = 2 |Σ_{j<d} w_r^j|²` with `w_r = η ζ^r`, `η = e^{πi/(2d)}`, `ζ = η⁴`
  (`one_div_sin_sq_eq`);
* `Σ_{r<d} r z^r = d/(z - 1)` for `z^d = 1 ≠ z` (`sum_range_mul_pow_eq`), as in the source's
  `Σ_a a ω^{ah} = -d/(1 - ω^h)`;
* the pairing `u/(u⁴ - 1) + v/(v⁴ - 1) = -1/(u + v)` for `uv = 1` (`pair_identity`), with
  `u + v = 2 cos(πh/(2d))`;
* `Σ_{k<d} Σ_{j<k} φ(k - j) = Σ_{h=1}^{d-1} (d - h) φ(h)` (`sum_range_sum_range_sub`).

Main results:
* `sum_range_mul_one_div_sin_sq` : `Σ_{r<d} r csc²(π(r + 1/4)/d) = d²(d - 1) - d Σ_h (d - h) sec(πh/(2d))`;
* `cglmp_fourierTable` : `I_d(Q_d) = I_d^F` for `d ≥ 2`.
-/

namespace CGLMPBounds

noncomputable section

open Finset ComplexConjugate

/-! ### `Σ_{r<n} r z^r` -/

theorem sub_one_mul_sum_range_mul_pow (z : ℂ) (n : ℕ) :
    (z - 1) * ∑ r ∈ range n, (r : ℂ) * z ^ r
      = ((n : ℂ) - 1) * z ^ n - ∑ r ∈ range n, z ^ r + 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

/-- `Σ_{r<n} r z^r = n/(z - 1)` for `z^n = 1`, `z ≠ 1`. -/
theorem sum_range_mul_pow_eq {z : ℂ} {n : ℕ} (hz : z ^ n = 1) (hz1 : z ≠ 1) :
    ∑ r ∈ range n, (r : ℂ) * z ^ r = n / (z - 1) := by
  have hz0 : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have hg : ∑ r ∈ range n, z ^ r = 0 := by
    rw [geom_sum_eq hz1 n, hz, sub_self, zero_div]
  have h := sub_one_mul_sum_range_mul_pow z n
  rw [hz, hg, mul_one, sub_zero, sub_add_cancel] at h
  rw [eq_div_iff hz0, mul_comm]
  exact h

theorem sum_range_natCast_complex (n : ℕ) :
    ∑ r ∈ range n, (r : ℂ) = (n : ℂ) * ((n : ℂ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-! ### The pairing identity -/

/-- For `uv = 1`: `u/(u⁴ - 1) + v/(v⁴ - 1) = -1/(u + v)`. -/
theorem pair_identity {u v : ℂ} (huv : u * v = 1) (hu4 : u ^ 4 - 1 ≠ 0) (hv4 : v ^ 4 - 1 ≠ 0)
    (hs : u + v ≠ 0) : u / (u ^ 4 - 1) + v / (v ^ 4 - 1) = -1 / (u + v) := by
  rw [div_add_div _ _ hu4 hv4, div_eq_div_iff (mul_ne_zero hu4 hv4) hs]
  linear_combination ((u * v + 1) * (u ^ 2 + v ^ 2) + (u ^ 4 + v ^ 4) + (u * v) ^ 3
    + (u * v) ^ 2 + u * v - 1) * huv

/-! ### The roots of unity `η = e^{πi/(2d)}` and `ζ = η⁴ = e^{2πi/d}` -/

/-- `η = e^{πi/(2d)}`. -/
def etaD (d : ℕ) : ℂ := Complex.exp (((Real.pi / (2 * d) : ℝ) : ℂ) * Complex.I)

theorem etaD_ne_zero (d : ℕ) : etaD d ≠ 0 := Complex.exp_ne_zero _

theorem etaD_pow_four (d : ℕ) : etaD d ^ 4 = Complex.exp (2 * Real.pi * Complex.I / d) := by
  unfold etaD
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem isPrimitiveRoot_etaD_pow_four {d : ℕ} (hd : d ≠ 0) : IsPrimitiveRoot (etaD d ^ 4) d := by
  rw [etaD_pow_four]
  exact Complex.isPrimitiveRoot_exp d hd

/-- `conj(e^{ix}) = (e^{ix})⁻¹` for real `x`. -/
theorem conj_exp_ofReal_mul_I (x : ℝ) :
    conj (Complex.exp ((x : ℂ) * Complex.I)) = (Complex.exp ((x : ℂ) * Complex.I))⁻¹ := by
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, Complex.exp_neg]

/-- `η^h + η^{-h} = 2 cos(πh/(2d))`. -/
theorem etaD_pow_add_inv_pow (d h : ℕ) :
    etaD d ^ h + (etaD d)⁻¹ ^ h = ((2 * Real.cos (Real.pi * h / (2 * d)) : ℝ) : ℂ) := by
  have e1 : etaD d ^ h = Complex.exp (((Real.pi * h / (2 * d) : ℝ) : ℂ) * Complex.I) := by
    unfold etaD
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have e2 : (etaD d)⁻¹ ^ h = Complex.exp (-((Real.pi * h / (2 * d) : ℝ) : ℂ) * Complex.I) := by
    rw [inv_pow, e1, ← Complex.exp_neg]
    congr 1
    ring
  rw [e1, e2, ← Complex.two_cos, Complex.ofReal_mul, Complex.ofReal_cos, Complex.ofReal_ofNat]

/-- `cos(πh/(2d)) > 0` for `h < d`. -/
theorem cos_pi_mul_div_pos {d h : ℕ} (hhd : h < d) : 0 < Real.cos (Real.pi * h / (2 * d)) := by
  have hd : (0 : ℝ) < d := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le h) hhd)
  have hh : (h : ℝ) < d := by exact_mod_cast hhd
  apply Real.cos_pos_of_mem_Ioo
  rw [Set.mem_Ioo]
  constructor
  · have : 0 ≤ Real.pi * h / (2 * d) := by positivity
    linarith [Real.pi_pos]
  · rw [div_lt_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]

/-! ### `csc²` as a squared geometric sum -/

/-- `csc²(π(r + 1/4)/d) = 2 Σ_{j,k<d} η^j η^{-k} (ζ^j ζ^{-k})^r` for `r < d`, `ζ = η⁴`. -/
theorem one_div_sin_sq_eq (d r : ℕ) (hr : r < d) :
    ((1 / Real.sin (Real.pi * ((r : ℝ) + 1 / 4) / d) ^ 2 : ℝ) : ℂ)
      = 2 * ∑ j ∈ range d, ∑ k ∈ range d,
          (etaD d ^ j * (etaD d)⁻¹ ^ k) * ((etaD d ^ 4) ^ j * (etaD d ^ 4)⁻¹ ^ k) ^ r := by
  have hd : (0 : ℝ) < d := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le r) hr)
  have hd0 : (d : ℝ) ≠ 0 := hd.ne'
  have hrd : (r : ℝ) + 1 / 4 < d := by
    have : (r : ℝ) + 1 ≤ d := by exact_mod_cast hr
    linarith
  have hsin_pos : 0 < Real.sin (Real.pi * ((r : ℝ) + 1 / 4) / d) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact div_pos (by positivity) hd
    · rw [div_lt_iff₀ hd]
      nlinarith [Real.pi_pos]
  have hsin0 : Real.sin (Real.pi * ((r : ℝ) + 1 / 4) / d) ≠ 0 := hsin_pos.ne'
  have hβ2 : 2 * Real.pi * ((r : ℝ) + 1 / 4) / d / 2 = Real.pi * ((r : ℝ) + 1 / 4) / d := by
    ring
  have hdβ : (d : ℝ) * (2 * Real.pi * ((r : ℝ) + 1 / 4) / d) / 2
      = Real.pi / 4 + ((r : ℤ) : ℝ) * Real.pi := by
    push_cast
    field_simp
    ring
  have hnorm := normSq_geom_exp d (2 * Real.pi * ((r : ℝ) + 1 / 4) / d) (by rw [hβ2]; exact hsin0)
  rw [hdβ, sin_sq_add_int_mul_pi, sin_sq_pi_div_four, hβ2] at hnorm
  -- `w = e^{iβ} = η ζ^r`
  have hw : Complex.exp (((2 * Real.pi * ((r : ℝ) + 1 / 4) / d : ℝ) : ℂ) * Complex.I)
      = etaD d * (etaD d ^ 4) ^ r := by
    rw [etaD_pow_four, etaD, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hS : ((Complex.normSq (∑ j ∈ range d,
        Complex.exp (((2 * Real.pi * ((r : ℝ) + 1 / 4) / d : ℝ) : ℂ) * Complex.I) ^ j) : ℝ) : ℂ)
      = ∑ j ∈ range d, ∑ k ∈ range d,
          Complex.exp (((2 * Real.pi * ((r : ℝ) + 1 / 4) / d : ℝ) : ℂ) * Complex.I) ^ j
            * (Complex.exp (((2 * Real.pi * ((r : ℝ) + 1 / 4) / d : ℝ) : ℂ) * Complex.I))⁻¹ ^ k := by
    rw [← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
    simp only [map_pow, conj_exp_ofReal_mul_I]
  have h2 : (1 / Real.sin (Real.pi * ((r : ℝ) + 1 / 4) / d) ^ 2 : ℝ)
      = 2 * Complex.normSq (∑ j ∈ range d,
          Complex.exp (((2 * Real.pi * ((r : ℝ) + 1 / 4) / d : ℝ) : ℂ) * Complex.I) ^ j) := by
    rw [hnorm]
    ring
  rw [h2, Complex.ofReal_mul, hS, hw, Complex.ofReal_ofNat]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
  rw [mul_inv]
  ring

/-! ### Double sums -/

/-- Split a square double sum into its diagonal and its pairs `j < k`. -/
theorem sum_range_sum_range_eq (f : ℕ → ℕ → ℂ) (n : ℕ) :
    ∑ j ∈ range n, ∑ k ∈ range n, f j k
      = ∑ j ∈ range n, f j j + ∑ k ∈ range n, ∑ j ∈ range k, (f j k + f k j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : ∑ j ∈ range (n + 1), ∑ k ∈ range (n + 1), f j k
        = ∑ j ∈ range n, ∑ k ∈ range n, f j k + ∑ j ∈ range n, f j n
          + ∑ k ∈ range n, f n k + f n n := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ (f n)]
      simp only [Finset.sum_range_succ, Finset.sum_add_distrib]
      ring
    rw [h1, ih, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_add_distrib]
    ring

/-- `Σ_{k<n} Σ_{j<k} φ(k - j) = Σ_{h=1}^{n-1} (n - h) φ(h)`. -/
theorem sum_range_sum_range_sub (φ : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ range n, ∑ j ∈ range k, φ (k - j) = ∑ h ∈ Ico 1 n, ((n : ℝ) - h) * φ h := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hr : ∑ j ∈ range n, φ (n - j) = ∑ h ∈ Ico 1 (n + 1), φ h := by
      have e1 : ∑ j ∈ range n, φ (n - j) = ∑ j ∈ range n, φ (n - 1 - j + 1) := by
        refine Finset.sum_congr rfl (fun j hj => ?_)
        rw [Finset.mem_range] at hj
        congr 1
        omega
      have e2 : ∑ j ∈ range n, φ (n - 1 - j + 1) = ∑ j ∈ range n, φ (j + 1) :=
        Finset.sum_range_reflect (fun i => φ (i + 1)) n
      have e3 : ∑ h ∈ Ico 1 (n + 1), φ h = ∑ j ∈ range n, φ (j + 1) := by
        rw [Finset.sum_Ico_eq_sum_range, show n + 1 - 1 = n by omega]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [add_comm]
      rw [e1, e2, e3]
    have hs : ∑ h ∈ Ico 1 (n + 1), (((n + 1 : ℕ) : ℝ) - h) * φ h
        = ∑ h ∈ Ico 1 (n + 1), ((n : ℝ) - h) * φ h + ∑ h ∈ Ico 1 (n + 1), φ h := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun h _ => ?_)
      push_cast
      ring
    have ht : ∑ h ∈ Ico 1 (n + 1), ((n : ℝ) - h) * φ h = ∑ h ∈ Ico 1 n, ((n : ℝ) - h) * φ h := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        simp
      · rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ n), sub_self, zero_mul, add_zero]
    rw [Finset.sum_range_succ, ih, hr, hs, ht]

/-! ### The trigonometric sum -/

/-- The diagonal terms: `η^j η^{-j} Σ_r r (ζ^j ζ^{-j})^r = d(d - 1)/2`. -/
theorem fourier_diag (d j : ℕ) :
    (etaD d ^ j * (etaD d)⁻¹ ^ j) * ∑ r ∈ range d, (r : ℂ) * ((etaD d ^ 4) ^ j * (etaD d ^ 4)⁻¹ ^ j) ^ r
      = (d : ℂ) * ((d : ℂ) - 1) / 2 := by
  have h1 : etaD d ^ j * (etaD d)⁻¹ ^ j = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (etaD_ne_zero d), one_pow]
  have h4 : (etaD d ^ 4) ^ j * (etaD d ^ 4)⁻¹ ^ j = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (pow_ne_zero 4 (etaD_ne_zero d)), one_pow]
  rw [h1, h4, one_mul]
  simp only [one_pow, mul_one]
  exact sum_range_natCast_complex d

/-- The paired off-diagonal terms for `j < k < d`. -/
theorem fourier_pair {d j k : ℕ} (hjk : j < k) (hkd : k < d) :
    (etaD d ^ j * (etaD d)⁻¹ ^ k) * ∑ r ∈ range d, (r : ℂ) * ((etaD d ^ 4) ^ j * (etaD d ^ 4)⁻¹ ^ k) ^ r
      + (etaD d ^ k * (etaD d)⁻¹ ^ j)
        * ∑ r ∈ range d, (r : ℂ) * ((etaD d ^ 4) ^ k * (etaD d ^ 4)⁻¹ ^ j) ^ r
      = ((-(d : ℝ) / (2 * Real.cos (Real.pi * ((k - j : ℕ) : ℝ) / (2 * d))) : ℝ) : ℂ) := by
  have hd : d ≠ 0 := by omega
  have hη := etaD_ne_zero d
  have hη4 : etaD d ^ 4 ≠ 0 := pow_ne_zero 4 hη
  have hprim := isPrimitiveRoot_etaD_pow_four hd
  obtain ⟨h, rfl⟩ : ∃ h, k = j + h := ⟨k - j, by omega⟩
  have hh0 : h ≠ 0 := by omega
  have hhd : h < d := by omega
  rw [show j + h - j = h by omega]
  -- the exponents
  have eA : etaD d ^ j * (etaD d)⁻¹ ^ (j + h) = (etaD d)⁻¹ ^ h := by
    rw [pow_add, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hη, one_pow, one_mul]
  have eB : etaD d ^ (j + h) * (etaD d)⁻¹ ^ j = etaD d ^ h := by
    rw [pow_add, mul_comm (etaD d ^ j), mul_assoc, ← mul_pow, mul_inv_cancel₀ hη, one_pow,
      mul_one]
  have eC : (etaD d ^ 4) ^ j * (etaD d ^ 4)⁻¹ ^ (j + h) = ((etaD d ^ 4) ^ h)⁻¹ := by
    rw [pow_add, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hη4, one_pow, one_mul, inv_pow]
  have eD : (etaD d ^ 4) ^ (j + h) * (etaD d ^ 4)⁻¹ ^ j = (etaD d ^ 4) ^ h := by
    rw [pow_add, mul_comm ((etaD d ^ 4) ^ j), mul_assoc, ← mul_pow, mul_inv_cancel₀ hη4, one_pow,
      mul_one]
  rw [eA, eB, eC, eD]
  -- the root of unity `z = ζ^h` and its inverse
  have hz : (etaD d ^ 4) ^ h ≠ 1 := hprim.pow_ne_one_of_pos_of_lt hh0 hhd
  have hzd : ((etaD d ^ 4) ^ h) ^ d = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow]
  have hz' : ((etaD d ^ 4) ^ h)⁻¹ ≠ 1 := inv_ne_one.mpr hz
  have hzd' : (((etaD d ^ 4) ^ h)⁻¹) ^ d = 1 := by rw [inv_pow, hzd, inv_one]
  rw [sum_range_mul_pow_eq hzd' hz', sum_range_mul_pow_eq hzd hz]
  -- the pairing identity with `u = η^h`, `v = η^{-h}`
  have hu4 : (etaD d ^ h) ^ 4 = (etaD d ^ 4) ^ h := by rw [← pow_mul, ← pow_mul, mul_comm]
  have hv4 : ((etaD d)⁻¹ ^ h) ^ 4 = ((etaD d ^ 4) ^ h)⁻¹ := by rw [inv_pow, inv_pow, hu4]
  have huv : etaD d ^ h * (etaD d)⁻¹ ^ h = 1 := by rw [← mul_pow, mul_inv_cancel₀ hη, one_pow]
  have hcos := cos_pi_mul_div_pos hhd
  have hs : etaD d ^ h + (etaD d)⁻¹ ^ h ≠ 0 := by
    rw [etaD_pow_add_inv_pow]
    exact Complex.ofReal_ne_zero.mpr (mul_pos two_pos hcos).ne'
  have hU : (etaD d ^ h) ^ 4 - 1 ≠ 0 := by rw [hu4]; exact sub_ne_zero.mpr hz
  have hV : ((etaD d)⁻¹ ^ h) ^ 4 - 1 ≠ 0 := by rw [hv4]; exact sub_ne_zero.mpr hz'
  have hp := pair_identity huv hU hV hs
  rw [hu4, hv4, etaD_pow_add_inv_pow] at hp
  calc (etaD d)⁻¹ ^ h * ((d : ℂ) / (((etaD d ^ 4) ^ h)⁻¹ - 1))
        + etaD d ^ h * ((d : ℂ) / ((etaD d ^ 4) ^ h - 1))
      = (d : ℂ) * (etaD d ^ h / ((etaD d ^ 4) ^ h - 1)
          + (etaD d)⁻¹ ^ h / (((etaD d ^ 4) ^ h)⁻¹ - 1)) := by ring
    _ = (d : ℂ) * (-1 / ((2 * Real.cos (Real.pi * h / (2 * d)) : ℝ) : ℂ)) := by rw [hp]
    _ = ((-(d : ℝ) / (2 * Real.cos (Real.pi * h / (2 * d))) : ℝ) : ℂ) := by
        push_cast
        ring

/-- `Σ_{r<d} r csc²(π(r + 1/4)/d) = d²(d - 1) - d Σ_{h=1}^{d-1} (d - h) sec(πh/(2d))`. -/
theorem sum_range_mul_one_div_sin_sq (d : ℕ) (hd : d ≠ 0) :
    ∑ r ∈ range d, (r : ℝ) * (1 / Real.sin (Real.pi * ((r : ℝ) + 1 / 4) / d) ^ 2)
      = (d : ℝ) ^ 2 * ((d : ℝ) - 1)
        - d * ∑ h ∈ Ico 1 d, ((d : ℝ) - h) / Real.cos (Real.pi * h / (2 * d)) := by
  apply Complex.ofReal_injective
  -- the complex form of the left side
  have hL : ((∑ r ∈ range d, (r : ℝ) * (1 / Real.sin (Real.pi * ((r : ℝ) + 1 / 4) / d) ^ 2) : ℝ) : ℂ)
      = 2 * ∑ j ∈ range d, ∑ k ∈ range d, (etaD d ^ j * (etaD d)⁻¹ ^ k)
          * ∑ r ∈ range d, (r : ℂ) * ((etaD d ^ 4) ^ j * (etaD d ^ 4)⁻¹ ^ k) ^ r := by
    rw [Complex.ofReal_sum]
    have hterm : ∀ r ∈ range d,
        (((r : ℝ) * (1 / Real.sin (Real.pi * ((r : ℝ) + 1 / 4) / d) ^ 2) : ℝ) : ℂ)
          = (r : ℂ) * (2 * ∑ j ∈ range d, ∑ k ∈ range d,
              (etaD d ^ j * (etaD d)⁻¹ ^ k) * ((etaD d ^ 4) ^ j * (etaD d ^ 4)⁻¹ ^ k) ^ r) := by
      intro r hr
      rw [Complex.ofReal_mul, Complex.ofReal_natCast, one_div_sin_sq_eq d r (Finset.mem_range.mp hr)]
    rw [Finset.sum_congr rfl hterm]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun r _ => ?_))
    ring
  rw [hL, sum_range_sum_range_eq
    (fun j k => (etaD d ^ j * (etaD d)⁻¹ ^ k)
      * ∑ r ∈ range d, (r : ℂ) * ((etaD d ^ 4) ^ j * (etaD d ^ 4)⁻¹ ^ k) ^ r) d]
  have hdiag : ∑ j ∈ range d, ((etaD d ^ j * (etaD d)⁻¹ ^ j)
      * ∑ r ∈ range d, (r : ℂ) * ((etaD d ^ 4) ^ j * (etaD d ^ 4)⁻¹ ^ j) ^ r)
      = ((d : ℝ) * ((d : ℝ) * ((d : ℝ) - 1) / 2) : ℝ) := by
    rw [Finset.sum_congr rfl (fun j _ => fourier_diag d j), Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    push_cast
    ring
  have hoff : ∑ k ∈ range d, ∑ j ∈ range k,
      ((etaD d ^ j * (etaD d)⁻¹ ^ k)
          * ∑ r ∈ range d, (r : ℂ) * ((etaD d ^ 4) ^ j * (etaD d ^ 4)⁻¹ ^ k) ^ r
        + (etaD d ^ k * (etaD d)⁻¹ ^ j)
          * ∑ r ∈ range d, (r : ℂ) * ((etaD d ^ 4) ^ k * (etaD d ^ 4)⁻¹ ^ j) ^ r)
      = ((∑ h ∈ Ico 1 d, ((d : ℝ) - h)
          * (-(d : ℝ) / (2 * Real.cos (Real.pi * h / (2 * d))))) : ℝ) := by
    have h1 : ∀ k ∈ range d, ∑ j ∈ range k,
        ((etaD d ^ j * (etaD d)⁻¹ ^ k)
            * ∑ r ∈ range d, (r : ℂ) * ((etaD d ^ 4) ^ j * (etaD d ^ 4)⁻¹ ^ k) ^ r
          + (etaD d ^ k * (etaD d)⁻¹ ^ j)
            * ∑ r ∈ range d, (r : ℂ) * ((etaD d ^ 4) ^ k * (etaD d ^ 4)⁻¹ ^ j) ^ r)
        = ∑ j ∈ range k, (((-(d : ℝ) / (2 * Real.cos (Real.pi * ((k - j : ℕ) : ℝ) / (2 * d))))
            : ℝ) : ℂ) := by
      intro k hk
      refine Finset.sum_congr rfl (fun j hj => ?_)
      exact fourier_pair (Finset.mem_range.mp hj) (Finset.mem_range.mp hk)
    rw [Finset.sum_congr rfl h1, ← sum_range_sum_range_sub
      (fun h => -(d : ℝ) / (2 * Real.cos (Real.pi * h / (2 * d)))) d, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Complex.ofReal_sum]
  rw [hdiag, hoff]
  have hsum : ∑ h ∈ Ico 1 d, ((d : ℝ) - h) * (-(d : ℝ) / (2 * Real.cos (Real.pi * h / (2 * d))))
      = -((d : ℝ) / 2) * ∑ h ∈ Ico 1 d, ((d : ℝ) - h) / Real.cos (Real.pi * h / (2 * d)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    ring
  rw [hsum]
  push_cast
  ring

/-! ### `I_d(Q_d) = I_d^F` -/

/-- For a function of the residual, summing over Bob's outcomes is summing over `ℤ_d`. -/
theorem sum_residual_comp {d : ℕ} [NeZero d] (g : ℕ → ℝ) (x y : Fin 2) (a : ZMod d) :
    ∑ b : ZMod d, g (residual d x y a b) = ∑ c : ZMod d, g c.val := by
  unfold residual
  split_ifs
  · exact Fintype.sum_equiv (Equiv.subLeft a) _ _ (fun _ => rfl)
  · exact Fintype.sum_equiv (Equiv.subRight a) _ _ (fun _ => rfl)
  · exact Fintype.sum_equiv ((Equiv.subRight a).trans (Equiv.subRight 1)) _ _ (fun _ => rfl)

theorem sum_zmod_val {d : ℕ} [NeZero d] (g : ℕ → ℝ) :
    ∑ c : ZMod d, g c.val = ∑ r ∈ range d, g r := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)
  exact Fin.sum_univ_eq_sum_range g (n + 1)

/-- `S_d(Q_d) = 4 Σ_{r<d} r f_d(r)`. -/
theorem cglmpS_fourierTable (d : ℕ) [NeZero d] :
    cglmpS d (fourierTable d) = 4 * ∑ r ∈ range d, (r : ℝ) * fourierResidualLaw d r := by
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hctx : ∀ x y : Fin 2, ∑ a : ZMod d, ∑ b : ZMod d,
      (residual d x y a b : ℝ) * fourierTable d x y a b
        = ∑ r ∈ range d, (r : ℝ) * fourierResidualLaw d r := by
    intro x y
    have hrow : ∀ a : ZMod d, ∑ b : ZMod d, (residual d x y a b : ℝ) * fourierTable d x y a b
        = (∑ r ∈ range d, (r : ℝ) * fourierResidualLaw d r) / d := by
      intro a
      simp only [fourierTable_apply]
      rw [sum_residual_comp (fun r => (r : ℝ) * (fourierResidualLaw d r / d)) x y a,
        sum_zmod_val (fun r => (r : ℝ) * (fourierResidualLaw d r / d)), Finset.sum_div]
      refine Finset.sum_congr rfl (fun r _ => ?_)
      show (r : ℝ) * (fourierResidualLaw d r / d) = r * fourierResidualLaw d r / d
      ring
    rw [Finset.sum_congr rfl (fun a _ => hrow a), Finset.sum_const, Finset.card_univ, ZMod.card,
      nsmul_eq_mul]
    exact mul_div_cancel₀ _ hd
  unfold cglmpS
  simp only [hctx, Fin.sum_univ_two]
  ring

/-- `Σ_{r<d} r f_d(r) = (d - 1)/2 - (1/(2d)) Σ_{h=1}^{d-1} (d - h) sec(πh/(2d))`. -/
theorem sum_mul_fourierResidualLaw (d : ℕ) (hd : d ≠ 0) :
    ∑ r ∈ range d, (r : ℝ) * fourierResidualLaw d r
      = ((d : ℝ) - 1) / 2
        - 1 / (2 * d) * ∑ h ∈ Ico 1 d, ((d : ℝ) - h) / Real.cos (Real.pi * h / (2 * d)) := by
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  have hT := sum_range_mul_one_div_sin_sq d hd
  have e : ∑ r ∈ range d, (r : ℝ) * fourierResidualLaw d r
      = 1 / (2 * (d : ℝ) ^ 2)
        * ∑ r ∈ range d, (r : ℝ) * (1 / Real.sin (Real.pi * ((r : ℝ) + 1 / 4) / d) ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    unfold fourierResidualLaw
    ring
  rw [e, hT]
  -- keep the secant sum as an atom: `field_simp` would normalize the `cos` arguments differently
  -- on the two sides (build 48)
  generalize ∑ h ∈ Ico 1 d, ((d : ℝ) - h) / Real.cos (Real.pi * h / (2 * d)) = S
  field_simp

/-- **The Fourier-phase measurements attain `I_d^F`.** `I_d(Q_d) = I_d^F` for `d ≥ 2`. -/
theorem cglmp_fourierTable (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    cglmp d (fourierTable d) = cglmpFourierValue d := by
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    intro h
    linarith
  unfold cglmp cglmpFourierValue
  rw [cglmpS_fourierTable, sum_mul_fourierResidualLaw d (NeZero.ne d)]
  generalize ∑ h ∈ Ico 1 d, ((d : ℝ) - h) / Real.cos (Real.pi * h / (2 * d)) = S
  field_simp
  ring

end

end CGLMPBounds
