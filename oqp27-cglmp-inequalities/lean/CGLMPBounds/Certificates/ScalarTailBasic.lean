module

public import CGLMPBounds.Defs.ScalarTail

@[expose] public section


/-!
# Uniform bounds for the scalar terms in Appendix J

This file develops the first two sentences of supplement p. 38. The product
difference estimate is a finite telescope proved by induction, and the bound
for `scalarE` retains the source's constant `1+(k+1)^2`.

The source coefficients, their ten interval bounds, convergence of the actual
scalar series, and its comparison with the finite polynomial certificate are
separate obligations. No such result is assumed in an endpoint here.
-/

namespace CGLMPBounds.Certificates

open Finset

theorem scalarRatio_den_pos (j : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) :
    0 < 1 + ((j : ℝ) + 1) * θ := by
  positivity

/-- Every factor lies in the unit interval for the full y-domain used by (J.3). -/
theorem scalarRatio_mem_unitInterval (j : ℕ) {θ y : ℝ}
    (hθ : 0 ≤ θ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    scalarRatio j θ y ∈ Set.Icc (0 : ℝ) 1 := by
  have hden := scalarRatio_den_pos j hθ
  constructor
  · exact div_nonneg (add_nonneg hy.1 (mul_nonneg (Nat.cast_nonneg _) hθ)) hden.le
  · unfold scalarRatio
    apply (div_le_iff₀ hden).2
    nlinarith [hy.2]

/-- The source's factor perturbation bound. The assumption j≥1 is necessary
for this exact jθ bound; only those factors enter `scalarQ`. -/
theorem scalarRatio_sub_abs_le (j : ℕ) (hj : 1 ≤ j) {θ y : ℝ}
    (hθ : 0 ≤ θ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |scalarRatio j θ y - y| ≤ (j : ℝ) * θ := by
  have hden := scalarRatio_den_pos j hθ
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hden1 : (1 : ℝ) ≤ 1 + ((j : ℝ) + 1) * θ := by
    have := mul_nonneg (show (0 : ℝ) ≤ (j : ℝ) + 1 by positivity) hθ
    linarith
  have hlin : |(j : ℝ) - ((j : ℝ) + 1) * y| ≤ j := by
    apply abs_le.mpr
    have hprod0 := mul_nonneg (show (0 : ℝ) ≤ (j : ℝ) + 1 by positivity) hy.1
    have hprod1 := mul_nonneg (show (0 : ℝ) ≤ (j : ℝ) + 1 by positivity)
      (sub_nonneg.mpr hy.2)
    constructor <;> nlinarith
  have heq : scalarRatio j θ y - y =
      θ * ((j : ℝ) - ((j : ℝ) + 1) * y) / (1 + ((j : ℝ) + 1) * θ) := by
    unfold scalarRatio
    field_simp [hden.ne']
    <;> ring
  rw [heq, abs_div, abs_mul, abs_of_nonneg hθ, abs_of_pos hden]
  calc
    _ ≤ θ * (j : ℝ) / (1 + ((j : ℝ) + 1) * θ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlin hθ) hden.le
    _ ≤ θ * (j : ℝ) := by
      apply (div_le_iff₀ hden).2
      exact le_mul_of_one_le_right (mul_nonneg hθ hj0) hden1
    _ = (j : ℝ) * θ := by ring

@[simp] theorem scalarQ_zero (θ y : ℝ) : scalarQ 0 θ y = 1 := by
  simp [scalarQ]

theorem scalarQ_succ (k : ℕ) (θ y : ℝ) :
    scalarQ (k + 1) θ y = scalarQ k θ y * scalarRatio (k + 1) θ y := by
  simp [scalarQ, Finset.prod_range_succ]

theorem scalarQ_mem_unitInterval (k : ℕ) {θ y : ℝ}
    (hθ : 0 ≤ θ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    scalarQ k θ y ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.prod_nonneg fun i _ => (scalarRatio_mem_unitInterval (i + 1) hθ hy).1
  · exact Finset.prod_le_one₀
      (fun i _ => (scalarRatio_mem_unitInterval (i + 1) hθ hy).1)
      (fun i _ => (scalarRatio_mem_unitInterval (i + 1) hθ hy).2)

/-- The product telescope: the accumulated error is at most
`θ*(1+2+...+k)=θ*k*(k+1)/2`. -/
theorem scalarQ_sub_pow_abs_le (k : ℕ) {θ y : ℝ}
    (hθ : 0 ≤ θ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |scalarQ k θ y - y ^ k| ≤ ((k : ℝ) * ((k : ℝ) + 1) / 2) * θ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hq := scalarRatio_mem_unitInterval (k + 1) hθ hy
    have hp0 : 0 ≤ y ^ k := pow_nonneg hy.1 k
    have hp1 : y ^ k ≤ 1 := pow_le_one₀ hy.1 hy.2
    have hfactor := scalarRatio_sub_abs_le (k + 1) (by omega) hθ hy
    calc
      |scalarQ (k + 1) θ y - y ^ (k + 1)| =
          |(scalarQ k θ y - y ^ k) * scalarRatio (k + 1) θ y +
            y ^ k * (scalarRatio (k + 1) θ y - y)| := by
        rw [scalarQ_succ, pow_succ]
        congr 1
        ring
      _ ≤ |scalarQ k θ y - y ^ k| * scalarRatio (k + 1) θ y +
          y ^ k * |scalarRatio (k + 1) θ y - y| := by
        simpa only [abs_mul, abs_of_nonneg hq.1, abs_of_nonneg hp0] using
          abs_add_le ((scalarQ k θ y - y ^ k) * scalarRatio (k + 1) θ y)
            (y ^ k * (scalarRatio (k + 1) θ y - y))
      _ ≤ |scalarQ k θ y - y ^ k| + |scalarRatio (k + 1) θ y - y| := by
        exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) hq.2)
          (mul_le_of_le_one_left (abs_nonneg _) hp1)
      _ ≤ ((k : ℝ) * ((k : ℝ) + 1) / 2) * θ + ((k + 1 : ℕ) : ℝ) * θ :=
        add_le_add ih hfactor
      _ = (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1) / 2) * θ := by
        push_cast
        ring

@[simp] theorem scalarE_at_zero (k : ℕ) (y : ℝ) : scalarE k 0 y = 0 := by
  simp [scalarE]

/-- Rewrite the two product terms using a_k=b_k+(k+1). This is the cancellation
needed to retain the manuscript's bound instead of a larger quadratic constant. -/
theorem scalarE_rewrite (k : ℕ) {θ y : ℝ} (hθ : θ ≠ 0) :
    scalarE k θ y = y ^ k + (y ^ k - scalarQ k θ y) / θ
      - ((k : ℝ) + 1) * scalarQ k θ y
      + ((k : ℝ) * ((k : ℝ) + 1) / 2) *
        (scalarQ (k - 1) θ y - scalarQ k θ y) := by
  rw [scalarE, if_neg hθ]
  field_simp [hθ]
  <;> ring

/-- The pointwise source bound on the positive-theta domain. -/
theorem scalarE_abs_le (k : ℕ) {θ y : ℝ} (hθ : 0 < θ)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |scalarE k θ y| ≤ 1 + ((k : ℝ) + 1) ^ 2 := by
  let b : ℝ := (k : ℝ) * ((k : ℝ) + 1) / 2
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hk : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  have hQ := scalarQ_mem_unitInterval k hθ.le hy
  have hP := scalarQ_mem_unitInterval (k - 1) hθ.le hy
  have hy0 : 0 ≤ y ^ k := pow_nonneg hy.1 k
  have hy1 : |y ^ k| ≤ 1 := by
    rw [abs_of_nonneg hy0]
    exact pow_le_one₀ hy.1 hy.2
  have hdiff : |scalarQ (k - 1) θ y - scalarQ k θ y| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith [hQ.1, hQ.2, hP.1, hP.2]
  have hquot : |(y ^ k - scalarQ k θ y) / θ| ≤ b := by
    rw [abs_div, abs_of_pos hθ]
    apply (div_le_iff₀ hθ).2
    rw [abs_sub_comm]
    exact scalarQ_sub_pow_abs_le k hθ.le hy
  have hlinear : |((k : ℝ) + 1) * scalarQ k θ y| ≤ (k : ℝ) + 1 := by
    rw [abs_mul, abs_of_nonneg hk, abs_of_nonneg hQ.1]
    exact mul_le_of_le_one_right hk hQ.2
  have hlast : |b * (scalarQ (k - 1) θ y - scalarQ k θ y)| ≤ b := by
    rw [abs_mul, abs_of_nonneg hb]
    exact mul_le_of_le_one_right hb hdiff
  rw [scalarE_rewrite k hθ.ne']
  change |y ^ k + (y ^ k - scalarQ k θ y) / θ
      - ((k : ℝ) + 1) * scalarQ k θ y
      + b * (scalarQ (k - 1) θ y - scalarQ k θ y)| ≤ _
  calc
    _ ≤ |y ^ k + (y ^ k - scalarQ k θ y) / θ
        - ((k : ℝ) + 1) * scalarQ k θ y| +
        |b * (scalarQ (k - 1) θ y - scalarQ k θ y)| := abs_add_le _ _
    _ ≤ (|y ^ k| + |(y ^ k - scalarQ k θ y) / θ|) +
        |((k : ℝ) + 1) * scalarQ k θ y| +
        |b * (scalarQ (k - 1) θ y - scalarQ k θ y)| := by
      apply add_le_add _ le_rfl
      rw [sub_eq_add_neg]
      exact (abs_add_le _ _).trans
        (by rw [abs_neg]; exact add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (1 + b) + ((k : ℝ) + 1) + b :=
      add_le_add (add_le_add (add_le_add hy1 hquot) hlinear) hlast
    _ = 1 + ((k : ℝ) + 1) ^ 2 := by dsimp [b]; ring

/-- The bound also holds at the source's explicitly filled removable value. -/
theorem scalarE_abs_le_of_nonneg (k : ℕ) {θ y : ℝ} (hθ : 0 ≤ θ)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |scalarE k θ y| ≤ 1 + ((k : ℝ) + 1) ^ 2 := by
  rcases hθ.eq_or_lt with hzero | hpos
  · subst θ
    simp only [scalarE_at_zero, abs_zero]
    positivity
  · exact scalarE_abs_le k hpos hy

/-- The odd-index version used in the coefficient and tail estimates. -/
theorem scalarE_odd_abs_le (n : ℕ) (hn : 0 < n) {θ y : ℝ} (hθ : 0 ≤ θ)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |scalarE (2 * n - 1) θ y| ≤ 1 + 4 * (n : ℝ) ^ 2 := by
  have hnId : (2 * n - 1) + 1 = 2 * n := Nat.sub_add_cancel (by omega)
  have hcast : ((2 * n - 1 : ℕ) : ℝ) + 1 = 2 * (n : ℝ) := by
    exact_mod_cast hnId
  calc
    _ ≤ 1 + (((2 * n - 1 : ℕ) : ℝ) + 1) ^ 2 :=
      scalarE_abs_le_of_nonneg (2 * n - 1) hθ hy
    _ = _ := by rw [hcast]; ring

/-- The ten rounding weights in (J.3) sum to exactly 1550. -/
theorem scalar_rounding_weight_sum :
    (∑ i : Fin 10, (1 + 4 * (((i.val + 1 : ℕ) : ℝ) ^ 2))) = 1550 := by
  norm_num [Fin.sum_univ_succ]

end CGLMPBounds.Certificates
