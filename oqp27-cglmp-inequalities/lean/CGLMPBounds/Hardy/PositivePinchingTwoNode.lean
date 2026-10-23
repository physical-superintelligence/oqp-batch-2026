module

public import CGLMPBounds.Hardy.TwoNodeResidue
public import CGLMPBounds.Hardy.PositivePinchingAlgebra

@[expose] public section


/-! The actual C.9 residue at the two inverse-involution nodes, with the
printed C.13 powers and the exact power of two after division by 1-x². -/

namespace CGLMPBounds.Hardy
noncomputable section

lemma inverse_two_node_scaled_identity (A B c : ℂ) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : A + B = 2) (p q : ℕ) :
    c * A⁻¹ ^ q * B⁻¹ ^ p / (A⁻¹ + B⁻¹) ^ (p + q + 1) / (A * B) =
      c * A ^ p * B ^ q / (2 : ℂ) ^ (p + q + 1) := by
  have hi : A⁻¹ + B⁻¹ = 2 / (A * B) := by
    field_simp [hA, hB]
    linear_combination hAB
  rw [hi]
  simp only [div_pow, mul_pow, inv_pow, pow_add, pow_one]
  field_simp [hA, hB]
  <;> ring

theorem twoNodeResidue_inverse_involution_nodes (m p q : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hm : p + q = m + 2)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    twoNodeResidue p q ((1 - x)⁻¹) (-(1 + x)⁻¹) / (1 - (x : ℂ) ^ 2) =
      (m.choose (p - 1) : ℂ) * (1 - (x : ℂ)) ^ (p - 1) *
        (1 + (x : ℂ)) ^ (q - 1) / (2 : ℂ) ^ (m + 1) := by
  cases p with
  | zero => omega
  | succ p =>
    cases q with
    | zero => omega
    | succ q =>
      have hm' : m = p + q := by omega
      subst m
      have hA : 0 < 1 - x := sub_pos.mpr hx.2
      have hB : 0 < 1 + x := by linarith [hx.1]
      have ha : 0 < (1 - x)⁻¹ := inv_pos.mpr hA
      have hb : -(1 + x)⁻¹ < 0 := neg_lt_zero.mpr (inv_pos.mpr hB)
      rw [twoNodeResidue_eq_source (p + 1) (q + 1) (by omega) (by omega) ha hb]
      have hdeg : p + 1 + (q + 1) - 2 = p + q := by omega
      have hden : p + 1 + (q + 1) - 1 = p + q + 1 := by omega
      simp only [hdeg, hden, Nat.add_sub_cancel, Nat.succ_eq_add_one,
        Complex.ofReal_inv, Complex.ofReal_neg, Complex.ofReal_sub,
        Complex.ofReal_add, Complex.ofReal_one, neg_neg, sub_neg_eq_add]
      have hprod : 1 - (x : ℂ) ^ 2 = (1 - (x : ℂ)) * (1 + (x : ℂ)) := by ring
      rw [hprod]
      exact inverse_two_node_scaled_identity _ _ _
        (by exact_mod_cast ne_of_gt hA) (by exact_mod_cast ne_of_gt hB) (by ring) p q

end
end CGLMPBounds.Hardy
