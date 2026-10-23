module

public import CGLMPBounds.Defs.ScalarSeries

@[expose] public section


/-! Domain parametrizations and the explicit error propagation in Appendix J. -/

namespace CGLMPBounds.Certificates

theorem scalarY_mem {θ u : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (1 / 2))
    (hu : u ∈ Set.Icc (0 : ℝ) 1) : scalarY θ u ∈ Set.Icc θ (1 - θ) := by
  have hfactor : 0 ≤ 1 - 2 * θ := by linarith [hθ.2]
  have hlo := mul_nonneg hfactor hu.1
  have hup := mul_le_mul_of_nonneg_left hu.2 hfactor
  unfold scalarY
  constructor <;> nlinarith

theorem scalarY_mem_unitInterval {θ u : ℝ}
    (hθ : θ ∈ Set.Icc (0 : ℝ) (1 / 2)) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    scalarY θ u ∈ Set.Icc (0 : ℝ) 1 := by
  have h := scalarY_mem hθ hu
  constructor <;> linarith [h.1, h.2, hθ.1]

/-- The parametrization retains the degenerate rectangle at theta=1/2. -/
theorem exists_scalarY {θ y : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (1 / 2))
    (hy : y ∈ Set.Icc θ (1 - θ)) :
    ∃ u ∈ Set.Icc (0 : ℝ) 1, scalarY θ u = y := by
  by_cases hz : 1 - 2 * θ = 0
  · refine ⟨0, by norm_num, ?_⟩
    unfold scalarY
    nlinarith [hy.1, hy.2]
  have hpos : 0 < 1 - 2 * θ :=
    lt_of_le_of_ne (by linarith [hθ.2]) (Ne.symm hz)
  refine ⟨(y - θ) / (1 - 2 * θ), ⟨div_nonneg (sub_nonneg.mpr hy.1) hpos.le, ?_⟩, ?_⟩
  · apply (div_le_one hpos).2
    linarith [hy.2]
  · unfold scalarY
    rw [mul_div_cancel₀ _ hz]
    ring

theorem scalarX_mem_unitInterval {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (1 / 3))
    (α : Fin 3 → ℝ) (hα : ∀ j, 0 ≤ α j) (hsum : ∑ j, α j = 1) (j : Fin 3) :
    scalarX θ α j ∈ Set.Icc (0 : ℝ) 1 := by
  have hj : α j ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun k _ => hα k) (Finset.mem_univ j)
  have hfactor : 0 ≤ 1 - 3 * θ := by linarith [hθ.2]
  have hlo := mul_nonneg hfactor (hα j)
  have hup := mul_le_mul_of_nonneg_left hj hfactor
  unfold scalarX
  constructor <;> nlinarith [hθ.1]

/-- All original triangle points are represented, including the single point
at theta=1/3. No division by a vanishing parameter is used at that boundary. -/
theorem exists_scalarX {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (1 / 3))
    (x : Fin 3 → ℝ) (hx : ∀ j, θ ≤ x j) (hsum : ∑ j, x j = 1) :
    ∃ α : Fin 3 → ℝ, (∀ j, 0 ≤ α j) ∧ (∑ j, α j = 1) ∧ scalarX θ α = x := by
  by_cases hz : 1 - 3 * θ = 0
  · have hzsum : (∑ j : Fin 3, (x j - θ)) = 0 := by
      rw [Finset.sum_sub_distrib, hsum]
      norm_num
      linarith
    have heq (j : Fin 3) : x j = θ := by
      have hj := (Finset.sum_eq_zero_iff_of_nonneg
        (fun k (_ : k ∈ (Finset.univ : Finset (Fin 3))) => sub_nonneg.mpr (hx k))).1
          hzsum j (Finset.mem_univ j)
      linarith
    refine ⟨fun _ => 1 / 3, by intro j; norm_num, by norm_num, ?_⟩
    funext j
    simp only [scalarX, hz, zero_mul, add_zero, heq]
  have hpos : 0 < 1 - 3 * θ :=
    lt_of_le_of_ne (by linarith [hθ.2]) (Ne.symm hz)
  refine ⟨fun j => (x j - θ) / (1 - 3 * θ),
    (fun j => div_nonneg (sub_nonneg.mpr (hx j)) hpos.le), ?_, ?_⟩
  · rw [← Finset.sum_div, Finset.sum_sub_distrib, hsum]
    apply (div_eq_one_iff_eq hz).2
    norm_num
    <;> ring
  · funext j
    unfold scalarX
    rw [mul_div_cancel₀ _ hz]
    ring

/-- The explicit perturbation calculation at the end of Appendix J. This
generic real inequality is instantiated with proved series errors and both
finite polynomial certificates; it is not itself the source endpoint. -/
theorem scalar_master_perturbation (θ ε E Et O Ot : ℝ)
    (hE : |E - Et| ≤ ε) (hO : |O - Ot| ≤ 6 * (1 - 2 * θ) * ε)
    (hp : 0 < 1 / 6 - ε * (16 - 30 * θ) + Et + (5 / 2) * Ot)
    (hm : 0 < 1 / 6 - ε * (16 - 30 * θ) + Et - (5 / 2) * Ot) :
    1 / 6 < 1 / 3 + E - (5 / 2) * |O| := by
  obtain ⟨hEl, hEu⟩ := abs_le.mp hE
  obtain ⟨hOl, hOu⟩ := abs_le.mp hO
  by_cases hsign : 0 ≤ O
  · rw [abs_of_nonneg hsign]
    nlinarith
  · rw [abs_of_neg (lt_of_not_ge hsign)]
    nlinarith

end CGLMPBounds.Certificates
