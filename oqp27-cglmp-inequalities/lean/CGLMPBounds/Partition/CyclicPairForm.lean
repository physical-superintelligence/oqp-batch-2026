module

public import CGLMPBounds.Partition.CircularWrapAlgebra
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section


/-! Finite cyclic assignment algebra behind D.3. The scalar wrap value
is subtracted explicitly before the two orientations are paired. The
weights are arbitrary actual count masses; no analytic averaging or
positivity conclusion is hidden in this finite identity. -/

namespace CGLMPBounds.Partition
open scoped Matrix
noncomputable section

private lemma cyclic_corr_self {r : ℕ} (hr : 0 < r)
    (V : Circulation.Mat r) (hV : Vᴴ * V = 1) : Circulation.corr V V = 1 := by
  simp [Circulation.corr, Circulation.tr, hV, Nat.ne_of_gt hr]

private lemma cyclic_pair_ordered_term {d r : ℕ} (hd : 0 < d) (hr : 0 < r)
    (V : Fin d → Circulation.Mat r) (hV : ∀ j, (V j)ᴴ * V j = 1)
    (p : ℕ → ℝ) (A B : ℝ) (a h : Fin d) :
    p h.val *
      (A * (1 - (Circulation.corr (V a) (sourceCyclicExtension hd V (a.val + h.val))).re) +
        B * (Circulation.corr (V a) (sourceCyclicExtension hd V (a.val + h.val))).im -
          (if a.val + h.val < d then 0 else A - B)) =
      (if a < a + h then p ((a + h).val - a.val) *
        (A * (1 - (Circulation.corr (V a) (V (a + h))).re) +
          B * (Circulation.corr (V a) (V (a + h))).im)
      else if a + h < a then p (d - (a.val - (a + h).val)) *
        (B * (1 - (Circulation.corr (V (a + h)) (V a)).re) +
          A * (Circulation.corr (V (a + h)) (V a)).im)
      else 0) := by
  have hext := sourceCyclicExtension_one_turn hd V a h.isLt.le
  have hmod : (⟨(a.val + h.val) % d, Nat.mod_lt _ hd⟩ : Fin d) = a + h := by
    apply Fin.ext
    exact (Fin.val_add a h).symm
  rw [hext, hmod]
  by_cases hh : h.val = 0
  · have hah : a + h = a := by
      apply Fin.ext
      simp [Fin.val_add, hh, Nat.mod_eq_of_lt a.isLt]
    have hlt : a.val + h.val < d := by omega
    simp [hlt, hah, cyclic_corr_self hr (V a) (hV a)]
  · by_cases hlt : a.val + h.val < d
    · have hval : (a + h).val = a.val + h.val := Fin.val_add_eq_of_add_lt hlt
      have hab : a < a + h := by change a.val < (a + h).val; omega
      have hdiff : (a + h).val - a.val = h.val := by omega
      simp only [if_pos hlt, if_pos hab, hdiff, sub_zero]
    · have hval : (a + h).val = a.val + h.val - d := by
        rw [Fin.val_add_eq_ite]
        simp only [if_pos (Nat.le_of_not_gt hlt)]
      have hba : a + h < a := by change (a + h).val < a.val; omega
      have hdiff : d - (a.val - (a + h).val) = h.val := by omega
      simp only [if_neg hlt, if_neg (not_lt_of_ge hba.le), if_pos hba, hdiff]
      rw [corr_wrapped_reverse (V (a + h)) (V a), wrapped_scalar_pair_kernel]

private lemma cyclic_pair_last_zero {d r : ℕ} (hd : 0 < d) (hr : 0 < r)
    (V : Fin d → Circulation.Mat r) (hV : ∀ j, (V j)ᴴ * V j = 1)
    (A B : ℝ) (a : Fin d) :
    A * (1 - (Circulation.corr (V a) (sourceCyclicExtension hd V (a.val + d))).re) +
      B * (Circulation.corr (V a) (sourceCyclicExtension hd V (a.val + d))).im -
        (if a.val + d < d then 0 else A - B) = 0 := by
  rw [sourceCyclicExtension_add_period, sourceCyclicExtension_base,
    corr_negative_I_right, cyclic_corr_self hr (V a) (hV a)]
  simp only [mul_one, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    neg_zero, sub_zero, mul_one, mul_neg_one,
    if_neg (show ¬a.val + d < d by omega)]
  ring

/-- The finite label/count sum becomes the actual source edge form.
The `h=0,d` endpoint contributions vanish against the scalar cut value;
the complementary distance carries the interchanged kernel weights. -/
theorem cyclic_count_pair_sum_eq_scalarEdgeForm {d r : ℕ} (hd : 0 < d) (hr : 0 < r)
    (V : Fin d → Circulation.Mat r) (hV : ∀ j, (V j)ᴴ * V j = 1)
    (p : ℕ → ℝ) (A B : ℝ) :
    (∑ h ∈ Finset.range (d + 1), p h * ∑ a : Fin d,
      (A * (1 - (Circulation.corr (V a) (sourceCyclicExtension hd V (a.val + h))).re) +
        B * (Circulation.corr (V a) (sourceCyclicExtension hd V (a.val + h))).im -
          (if a.val + h < d then 0 else A - B))) =
      scalarEdgeForm (fun h => A * p h + B * p (d - h)) V := by
  classical
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  rw [Finset.sum_range_succ]
  simp only [cyclic_pair_last_zero hd hr V hV, Finset.sum_const_zero, mul_zero, add_zero]
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hreindex (a : Fin d) :
      (∑ h : Fin d, p h.val *
        (A * (1 - (Circulation.corr (V a) (sourceCyclicExtension hd V (a.val + h.val))).re) +
          B * (Circulation.corr (V a) (sourceCyclicExtension hd V (a.val + h.val))).im -
            (if a.val + h.val < d then 0 else A - B))) =
      ∑ b : Fin d,
        (if a < b then p (b.val - a.val) *
          (A * (1 - (Circulation.corr (V a) (V b)).re) +
            B * (Circulation.corr (V a) (V b)).im)
        else if b < a then p (d - (a.val - b.val)) *
          (B * (1 - (Circulation.corr (V b) (V a)).re) +
            A * (Circulation.corr (V b) (V a)).im)
        else 0) := by
    apply Fintype.sum_equiv (Equiv.addLeft a)
    intro h
    exact cyclic_pair_ordered_term hd hr V hV p A B a h
  simp_rw [hreindex]
  have hsplit (a b : Fin d) :
      (if a < b then p (b.val - a.val) *
        (A * (1 - (Circulation.corr (V a) (V b)).re) +
          B * (Circulation.corr (V a) (V b)).im)
      else if b < a then p (d - (a.val - b.val)) *
        (B * (1 - (Circulation.corr (V b) (V a)).re) +
          A * (Circulation.corr (V b) (V a)).im)
      else 0) =
      (if a < b then p (b.val - a.val) *
        (A * (1 - (Circulation.corr (V a) (V b)).re) +
          B * (Circulation.corr (V a) (V b)).im) else 0) +
      (if b < a then p (d - (a.val - b.val)) *
        (B * (1 - (Circulation.corr (V b) (V a)).re) +
          A * (Circulation.corr (V b) (V a)).im) else 0) := by
    rcases lt_trichotomy a b with hab | hab | hba
    · simp [hab, not_lt_of_ge hab.le]
    · subst b; simp
    · simp [hba, not_lt_of_ge hba.le]
  simp_rw [hsplit, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun a b : Fin d => if b < a then
    p (d - (a.val - b.val)) *
      (B * (1 - (Circulation.corr (V b) (V a)).re) +
        A * (Circulation.corr (V b) (V a)).im) else 0)]
  rw [← Finset.sum_add_distrib]
  unfold scalarEdgeForm
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hab : a < b
  · simp only [if_pos hab]
    have hdif : d - (d - (b.val - a.val)) = b.val - a.val := by omega
    rw [hdif]
    ring
  · simp [hab]

end
end CGLMPBounds.Partition
