module

public import CGLMPBounds.Companion.SourceCost

@[expose] public section


/-!
# The exact companion Bell-gap coefficient

Convert the actual tuple's one-edge cost into (C.3). Both coefficient orientations
are retained: the imaginary term has the positive complementary-secant coefficient.
The final theorem also retains the common reducing isometry from the construction.
-/

open Matrix Finset
namespace CGLMPBounds.Companion
noncomputable section

variable {d n : ℕ} [NeZero d]

/-- The source summand before its factor `1/(2d²)`. -/
def gapPair (d j k : ℕ) (z : ℂ) : ℝ :=
  (1 - z.re) / Real.cos (Real.pi * ((k - j : ℕ) : ℝ) / (2 * d)) +
    z.im / Real.cos (Real.pi * ((d - k + j : ℕ) : ℝ) / (2 * d))

/-- The exact source gap, summing each ordered frequency pair once. -/
def companionGap {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : Fin d → Matrix.unitaryGroup ι ℂ) : ℝ :=
  (∑ j : Fin d, ∑ k : Fin d,
    if j < k then gapPair d j.val k.val (unitaryCorrelation V j k) else 0) /
      (2 * (d : ℝ) ^ 2)

lemma complementary_cos {j k : ℕ} (hjk : j < k) (hkd : k < d) :
    Real.cos (Real.pi * ((d - k + j : ℕ) : ℝ) / (2 * d)) =
      Real.sin (Real.pi * ((k - j : ℕ) : ℝ) / (2 * d)) := by
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have ha : (d - k + j : ℕ) = d - (k - j) := by omega
  rw [ha, Nat.cast_sub (by omega : k - j ≤ d)]
  have hangle : Real.pi * ((d : ℝ) - (k - j : ℕ)) / (2 * d) =
      Real.pi / 2 - Real.pi * ((k - j : ℕ) : ℝ) / (2 * d) := by
    field_simp [hdR]
    <;> ring
  rw [hangle, Real.cos_pi_div_two_sub]

lemma gapPair_eq {j k : ℕ} (hjk : j < k) (hkd : k < d) (z : ℂ) :
    gapPair d j k z =
      1 / Real.cos (Real.pi * ((k - j : ℕ) : ℝ) / (2 * d)) -
        pairedCorrelation d j k z := by
  unfold gapPair pairedCorrelation
  rw [complementary_cos hjk hkd, sub_div]
  ring

lemma sum_fin_strictPairs (f : ℕ → ℕ → ℝ) :
    (∑ j : Fin d, ∑ k : Fin d, if j < k then f j.val k.val else 0) =
      ∑ k ∈ range d, ∑ j ∈ range k, f j k := by
  rw [Finset.sum_comm]
  calc
    _ = ∑ k : Fin d, ∑ j ∈ range d, if j < k.val then f j k.val else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      exact Fin.sum_univ_eq_sum_range (fun j : ℕ => if j < k.val then f j k.val else 0) d
    _ = ∑ k : Fin d, ∑ j ∈ range k.val, f j k.val := by
      apply Finset.sum_congr rfl
      intro k _
      rw [← Finset.sum_filter]
      congr 1
      ext j
      simp only [mem_filter, mem_range]
      omega
    _ = _ := Fin.sum_univ_eq_sum_range (fun k : ℕ => ∑ j ∈ range k, f j k) d

lemma companionGap_eq_range {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : Fin d → Matrix.unitaryGroup ι ℂ) :
    companionGap V =
      (∑ k ∈ range d, ∑ j ∈ range k,
        gapPair d j k (unitaryCorrelation (extendUnitary V) j k)) / (2 * (d : ℝ) ^ 2) := by
  unfold companionGap
  have he : ∀ j k : Fin d,
      unitaryCorrelation (extendUnitary V) j.val k.val = unitaryCorrelation V j k := by
    intro j k
    simp only [unitaryCorrelation, extendUnitary_fin]
  rw [← sum_fin_strictPairs]
  simp only [he]

/-- The reference secant sum in (A.1), expressed with the same frequency pairs. -/
lemma cglmpFourierValue_eq_pairs :
    cglmpFourierValue d =
      (4 / ((d : ℝ) * ((d : ℝ) - 1))) *
        ∑ k ∈ range d, ∑ j ∈ range k,
          1 / Real.cos (Real.pi * ((k - j : ℕ) : ℝ) / (2 * d)) := by
  rw [sum_range_sum_range_sub (fun h : ℕ =>
    1 / Real.cos (Real.pi * (h : ℝ) / (2 * d))) d]
  simp only [cglmpFourierValue, mul_one_div]

lemma companionGap_eq_difference {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : Fin d → Matrix.unitaryGroup ι ℂ) :
    companionGap V =
      ((∑ k ∈ range d, ∑ j ∈ range k,
          1 / Real.cos (Real.pi * ((k - j : ℕ) : ℝ) / (2 * d))) -
        ∑ k ∈ range d, ∑ j ∈ range k,
          pairedCorrelation d j k (unitaryCorrelation (extendUnitary V) j k)) /
            (2 * (d : ℝ) ^ 2) := by
  rw [companionGap_eq_range]
  congr 1
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  exact gapPair_eq (mem_range.mp hj) (mem_range.mp hk) _

/-- Source (C.3), for the tuple obtained from the actual original clock. -/
theorem original_Bell_gap (hd : 2 ≤ d) (hn : 1 ≤ n)
    (P : Fin 4 → ZMod d → Base n) (hP : ∀ t, IsPVM (P t))
    (V : Fin d → Matrix.unitaryGroup (CompanionMultiplicity n) ℂ)
    (hclock : sourceClock P hP = tupleClock V) :
    cglmpFourierValue d - cglmp d (tracialTable ![P 0, P 2] ![P 1, P 3]) =
      (8 * (d : ℝ) / ((d : ℝ) - 1)) * companionGap V := by
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have htwo : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hcost := original_residual_sum_eq_formula hn P hP V hclock
  rw [cglmpFourierValue_eq_pairs, cglmp, companionGap_eq_difference]
  field_simp [hdR, hd1] at hcost ⊢
  nlinarith [hcost]

/-- The exact Bell gap together with the original common reducing summand.
The multiplicity coordinates are `Fin 4 × Fin n`, of cardinality `4*n`. -/
theorem exists_companion_tuple_gap_reducing (hd : 2 ≤ d) (hn : 1 ≤ n)
    (P : Fin 4 → ZMod d → Base n) (hP : ∀ t, IsPVM (P t)) :
    ∃ V : Fin d → Matrix.unitaryGroup (CompanionMultiplicity n) ℂ,
      (∀ j, (V j : Matrix (CompanionMultiplicity n) (CompanionMultiplicity n) ℂ) ^ 4 = 1) ∧
      cglmpFourierValue d - cglmp d (tracialTable ![P 0, P 2] ![P 1, P 3]) =
        (8 * (d : ℝ) / ((d : ℝ) - 1)) * companionGap V ∧
      sourceClock P hP = tupleClock V ∧
      (sourceEmbedding P)ᴴ * sourceEmbedding P = 1 ∧
      (∀ t a, tupleMeasurement V t a * sourceEmbedding P = sourceEmbedding P * P t a) ∧
      (∀ t a, Commute (tupleMeasurement V t a) (sourceEmbedding P * (sourceEmbedding P)ᴴ)) := by
  obtain ⟨V, hfour, hclock, hiso, hinter, hcomm⟩ := exists_companion_tuple_reducing P hP
  exact ⟨V, hfour, original_Bell_gap hd hn P hP V hclock, hclock, hiso, hinter, hcomm⟩

end
end CGLMPBounds.Companion
