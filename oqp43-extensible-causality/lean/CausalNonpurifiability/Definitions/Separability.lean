module

public import CausalNonpurifiability.RobustnessEC
public import CausalNonpurifiability.Definitions.ConvexForm

@[expose] public section


/-!
# `CausalNonpurifiability.Definitions.Separability`

Definition 2.4 of the manuscript (`def:order`) in its own form: a process is causally separable
if it is a convex combination of a process of order `A ≺ B` and a process of order `B ≺ A`
(`CausallySeparableConvex`, `Definitions/ConvexForm.lean`). The library uses the sum form `CausallySeparable`
(`W ∈ O_{A≺B} + O_{B≺A}`); `causallySeparable_iff_convex` shows that the two agree for processes,
which is the sentence after Definition 2.4.
-/

set_option autoImplicit false

open Matrix
open scoped ComplexOrder

namespace CausalNonpurifiability

noncomputable section

/-- A positive operator with trace zero is zero. -/
theorem eq_zero_of_posSemidef_trace_eq_zero {ι : Type} [Fintype ι] [DecidableEq ι] {M : Op ι}
    (hM : M.PosSemidef) (h : M.trace = 0) : M = 0 := by
  have hs : ∀ i : ι, star (Pi.single i (1 : ℂ) : ι → ℂ) = Pi.single i 1 := by
    intro i
    ext k
    by_cases hk : k = i <;> simp [Pi.single_apply, hk]
  have hdiag : ∀ i : ι,
      star (Pi.single i (1 : ℂ) : ι → ℂ) ⬝ᵥ (M *ᵥ (Pi.single i (1 : ℂ) : ι → ℂ)) = M i i := by
    intro i
    rw [hs]
    simp [dotProduct, Matrix.mulVec, Pi.single_apply, mul_ite, ite_mul]
  have hnn : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ M i i := fun i _ => by
    rw [← hdiag]
    exact hM.dotProduct_mulVec_nonneg _
  have h' : ∑ i, M i i = 0 := h
  have hzero : ∀ i, M i i = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h' i (Finset.mem_univ i)
  ext k i
  have h0 : star (Pi.single i (1 : ℂ) : ι → ℂ) ⬝ᵥ (M *ᵥ (Pi.single i (1 : ℂ) : ι → ℂ)) = 0 := by
    rw [hdiag, hzero i]
  have hk := congrFun (hM.dotProduct_mulVec_zero_iff.mp h0) k
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite] using hk

variable (D : Ports)

/-- The process `I/(mn)`: both parties receive the maximally mixed state. -/
def mixedProcess : PMat D := ((((D.m * D.n : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) • (1 : PMat D)

variable {D}

theorem isSelfAdjoint_ofReal (c : ℝ) : IsSelfAdjoint (c : ℂ) :=
  isSelfAdjoint_iff.mpr (Complex.conj_ofReal c)

theorem orderedAB_realSmul {U : PMat D} (hU : OrderedAB D U) {c : ℝ} (hc : 0 ≤ c) :
    OrderedAB D ((c : ℂ) • U) :=
  ⟨genLV_smul (isSelfAdjoint_ofReal c) hU.1,
    posSemidef_complex_smul hU.2.1 (Complex.zero_le_real.mpr hc), by rw [map_smul, hU.2.2]⟩

theorem orderedBA_realSmul {V : PMat D} (hV : OrderedBA D V) {c : ℝ} (hc : 0 ≤ c) :
    OrderedBA D ((c : ℂ) • V) :=
  ⟨genLV_smul (isSelfAdjoint_ofReal c) hV.1,
    posSemidef_complex_smul hV.2.1 (Complex.zero_le_real.mpr hc), by rw [map_smul, hV.2.2]⟩

theorem valid_realSmul {U : PMat D} (hU : InLV D U) (hpsd : U.PosSemidef) {c : ℝ} (hc : 0 ≤ c)
    (htr : (c : ℂ) * U.trace = ((D.d * D.e : ℕ) : ℂ)) : Valid D ((c : ℂ) • U) :=
  ⟨genLV_smul (isSelfAdjoint_ofReal c) hU,
    posSemidef_complex_smul hpsd (Complex.zero_le_real.mpr hc),
    by rw [Matrix.trace_smul, smul_eq_mul, htr]⟩

variable (D)

theorem mixedProcess_valid : Valid D (mixedProcess D) := by
  refine ⟨genLV_smul (isSelfAdjoint_ofReal _) genLV_one,
    posSemidef_complex_smul Matrix.PosSemidef.one
      (Complex.zero_le_real.mpr (inv_nonneg.mpr (Nat.cast_nonneg _))), ?_⟩
  have hm : (D.m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 D.m_ne_zero
  have hn : (D.n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 D.n_ne_zero
  rw [mixedProcess, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
  simp only [Fintype.card_prod, Fintype.card_fin]
  push_cast
  rw [inv_mul_eq_div, div_eq_iff (mul_ne_zero hm hn)]
  ring

theorem mixedProcess_orderedAB : OrderedAB D (mixedProcess D) :=
  ⟨(mixedProcess_valid D).1, (mixedProcess_valid D).2.1, by rw [mixedProcess, map_smul, R_BO_one]⟩

theorem mixedProcess_orderedBA : OrderedBA D (mixedProcess D) :=
  ⟨(mixedProcess_valid D).1, (mixedProcess_valid D).2.1, by rw [mixedProcess, map_smul, R_AO_one]⟩

/-- **Definition 2.4 and the sum form agree for processes**. -/
theorem causallySeparable_iff_convex {W : PMat D} (hW : Valid D W) :
    CausallySeparable D W ↔ CausallySeparableConvex D W := by
  constructor
  · rintro ⟨-, U, V, hU, hV, hUV⟩
    obtain ⟨a, ha_eq, ha0⟩ : ∃ a : ℝ, U.trace = (a : ℂ) ∧ 0 ≤ a :=
      ⟨U.trace.re, Complex.ext (by simp) (by simp [trace_im_zero hU.2.1]), trace_re_nonneg hU.2.1⟩
    obtain ⟨b, hb_eq, hb0⟩ : ∃ b : ℝ, V.trace = (b : ℂ) ∧ 0 ≤ b :=
      ⟨V.trace.re, Complex.ext (by simp) (by simp [trace_im_zero hV.2.1]), trace_re_nonneg hV.2.1⟩
    obtain ⟨t, ht_eq, ht0⟩ : ∃ t : ℝ, ((D.d * D.e : ℕ) : ℂ) = (t : ℂ) ∧ 0 < t :=
      ⟨((D.d * D.e : ℕ) : ℝ), (Complex.ofReal_natCast _).symm,
        by exact_mod_cast Nat.mul_pos D.d_pos D.e_pos⟩
    have hab : a + b = t := by
      have h : U.trace + V.trace = ((D.d * D.e : ℕ) : ℂ) := by
        rw [← Matrix.trace_add, ← hUV]
        exact hW.2.2
      rw [ha_eq, hb_eq, ht_eq, ← Complex.ofReal_add] at h
      exact Complex.ofReal_injective h
    have ht_ne : t ≠ 0 := ht0.ne'
    by_cases ha : a = 0
    · have hU0 : U = 0 :=
        eq_zero_of_posSemidef_trace_eq_zero hU.2.1 (by rw [ha_eq, ha, Complex.ofReal_zero])
      refine ⟨0, mixedProcess D, V, le_rfl, zero_le_one, mixedProcess_valid D,
        mixedProcess_orderedAB D, ⟨hV.1, hV.2.1, ?_⟩, hV, ?_⟩
      · rw [hb_eq, ht_eq]
        congr 1
        linarith
      · rw [hUV, hU0]
        simp
    · by_cases hb : b = 0
      · have hV0 : V = 0 :=
          eq_zero_of_posSemidef_trace_eq_zero hV.2.1 (by rw [hb_eq, hb, Complex.ofReal_zero])
        refine ⟨1, U, mixedProcess D, zero_le_one, le_rfl, ⟨hU.1, hU.2.1, ?_⟩, hU,
          mixedProcess_valid D, mixedProcess_orderedBA D, ?_⟩
        · rw [ha_eq, ht_eq]
          congr 1
          linarith
        · rw [hUV, hV0]
          simp
      · have ha' : 0 < a := lt_of_le_of_ne ha0 (Ne.symm ha)
        have hb' : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hb)
        have ha_ne : a ≠ 0 := ha
        have hb_ne : b ≠ 0 := hb
        refine ⟨a / t, ((t / a : ℝ) : ℂ) • U, ((t / b : ℝ) : ℂ) • V, div_nonneg ha0 ht0.le,
          (div_le_one ht0).mpr (by linarith), ?_, orderedAB_realSmul hU (div_nonneg ht0.le ha0),
          ?_, orderedBA_realSmul hV (div_nonneg ht0.le hb0), ?_⟩
        · refine valid_realSmul hU.1 hU.2.1 (div_nonneg ht0.le ha0) ?_
          rw [ha_eq, ht_eq, ← Complex.ofReal_mul, div_mul_cancel₀ t ha_ne]
        · refine valid_realSmul hV.1 hV.2.1 (div_nonneg ht0.le hb0) ?_
          rw [hb_eq, ht_eq, ← Complex.ofReal_mul, div_mul_cancel₀ t hb_ne]
        · have h1 : a / t * (t / a) = 1 := by field_simp
          have hsub : 1 - a / t = b / t := by
            rw [eq_div_iff ht_ne, sub_mul, one_mul, div_mul_cancel₀ a ht_ne]
            linarith
          have h2 : (1 - a / t) * (t / b) = 1 := by
            rw [hsub]
            field_simp
          rw [hUV, smul_smul, smul_smul, ← Complex.ofReal_mul, ← Complex.ofReal_mul, h1, h2,
            Complex.ofReal_one, one_smul, one_smul]
  · rintro ⟨q, WA, WB, hq0, hq1, -, hAo, -, hBo, hWq⟩
    exact ⟨hW, _, _, orderedAB_realSmul hAo hq0, orderedBA_realSmul hBo (by linarith), hWq⟩

end

end CausalNonpurifiability
