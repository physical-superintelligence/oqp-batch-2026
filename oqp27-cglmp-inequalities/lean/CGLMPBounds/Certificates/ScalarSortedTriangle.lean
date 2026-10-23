module

public import CGLMPBounds.Certificates.ScalarTriangle
public import CGLMPBounds.Certificates.ScalarPartitionContinuity

@[expose] public section


/-! Specialization of the scalar margins to the three increasing vertices in D.1. -/

namespace CGLMPBounds.Certificates

theorem scalar_sorted_triangle_margin (d h i j k : ℕ) (hd : 3 ≤ d)
    (hh0 : 0 < h) (hhd : h < d) (hij : i < j) (hjk : j < k) (hkd : k < d) :
    5 * ((d : ℝ) - 2) * |scalarErrorTriangle d i j k| ≤
      2 * d * (scalarIntegralError d h + scalarPartitionCoefficient d h -
        1 / (6 * ((d : ℝ) + 1))) := by
  let s : Fin 3 → ℕ := ![j - i, k - j, d - (k - i)]
  have hs0 : ∀ l, 0 < s l := by
    intro l
    fin_cases l
    · change 0 < j - i
      omega
    · change 0 < k - j
      omega
    · change 0 < d - (k - i)
      omega
  have hsum : ∑ l, s l = d := by
    rw [Fin.sum_univ_three]
    change (j - i) + (k - j) + (d - (k - i)) = d
    omega
  have hskew : (∑ l, scalarErrorSkew d (s l)) = scalarErrorTriangle d i j k := by
    rw [Fin.sum_univ_three]
    change scalarErrorSkew d (j - i) + scalarErrorSkew d (k - j) +
      scalarErrorSkew d (d - (k - i)) = scalarErrorTriangle d i j k
    rw [scalarErrorSkew_reflect d (k - i) (by omega)] <;> rfl
  have hm := scalar_cyclic_triangle_margin d h hd hh0 hhd s hs0 hsum
  rw [hskew] at hm
  have hs := scalarPartitionCoefficient_lower d h (by omega) hhd.le
  have hb : (5 * ((d : ℝ) - 2) * |scalarErrorTriangle d i j k|) / (2 * d) ≤
      scalarIntegralError d h + scalarPartitionCoefficient d h -
        1 / (6 * ((d : ℝ) + 1)) := by
    have hquot : (5 * ((d : ℝ) - 2) * |scalarErrorTriangle d i j k|) / (2 * d) =
        (5 * ((d : ℝ) - 2) / (2 * d)) * |scalarErrorTriangle d i j k| := by ring
    rw [hquot]
    linarith
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hout := (div_le_iff₀ (show (0 : ℝ) < 2 * d by positivity)).1 hb
  simpa only [mul_comm] using hout

end CGLMPBounds.Certificates
