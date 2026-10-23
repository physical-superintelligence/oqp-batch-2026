module

public import CausalNonpurifiability.EC.Components
public import CausalNonpurifiability.EC.Compression
public import CausalNonpurifiability.RobustnessEC
public import CausalNonpurifiability.Definitions.Bias
public import CausalNonpurifiability.Definitions.Separability

@[expose] public section


/-!
# `CausalNonpurifiability.Bias`

`subsec:bias`. If `θ_m` and `θ_n` in `eq:centers` are replaced by the unbiased
states `P_m/2` and `P_n/2`, the operator `C` of `eq:C-def` becomes `(3/40) P_m ⊗ P_n`, which is
positive. The decomposition `eq:signed-decomposition` then consists of three positive causally
ordered operators (`U ∈ O_{A≺B}`, `V ∈ O_{B≺A}`, and `2 Q_C = (3/20) Π` in both cones), and the
resulting process is causally separable.
-/

set_option autoImplicit false

open Matrix
open scoped Kronecker ComplexOrder

namespace CausalNonpurifiability

section Rational

variable {m d n e : ℕ}

theorem Cunbiased_eq : Cunbiased m n = (3 / 40 : ℚ) • (P m ⊗ₖ P n) := by
  rw [Cunbiased, Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul, ← sub_smul, smul_smul]
  norm_num

theorem Cunbiased_eq_sq :
    Cunbiased m n = (3 / 40 : ℚ) • ((P m ⊗ₖ P n)ᵀ * (P m ⊗ₖ P n)) := by
  rw [Cunbiased_eq, ← Matrix.kroneckerMap_transpose, P_transpose, P_transpose,
    ← Matrix.mul_kronecker_mul, P_mul_P, P_mul_P]

theorem Qembed_half_half :
    Qembed d e (((1 / 2 : ℚ) • P m) ⊗ₖ ((1 / 2 : ℚ) • P n)) = (1 / 4 : ℚ) • Pi m d n e := by
  rw [Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul, Qembed_smul, Pi_eq_Qembed]
  norm_num

theorem Qembed_Cunbiased : Qembed d e (Cunbiased m n) = (3 / 40 : ℚ) • Pi m d n e := by
  rw [Cunbiased_eq, Qembed_smul, Pi_eq_Qembed]

/-- `eq:signed-decomposition` for the unbiased states. -/
theorem W0unbiased_signed :
    W0unbiased m d n e = U m d n e + V m d n e + (2 : ℚ) • Qembed d e (Cunbiased m n) := by
  rw [W0unbiased, Qembed_half_half, Qembed_Cunbiased, U, V]
  module

theorem RBOq_Pi (he : 0 < e) : RBOq (Pi m d n e) = Pi m d n e := by
  simp only [Pi, RBOq_kron4, trace_one_div_self he, one_smul]

theorem RAOq_Pi (hd : 0 < d) : RAOq (Pi m d n e) = Pi m d n e := by
  simp only [Pi, RAOq_kron4, trace_one_div_self hd, one_smul]

theorem Pi_LV_a (hd : 0 < d) : RBIBOq (Pi m d n e) - RAOq (RBIBOq (Pi m d n e)) = 0 := by
  simp only [Pi, RBIBOq_kron4, RAOq_smul, RAOq_kron4, trace_one_div_self hd, one_smul, sub_self]

theorem Pi_LV_b (he : 0 < e) : RAIAOq (Pi m d n e) - RBOq (RAIAOq (Pi m d n e)) = 0 := by
  simp only [Pi, RAIAOq_kron4, RBOq_smul, RBOq_kron4, trace_one_div_self he, one_smul, sub_self]

theorem Pi_LV_c (hd : 0 < d) (he : 0 < e) :
    Pi m d n e - RAOq (Pi m d n e) - RBOq (Pi m d n e) + RAOq (RBOq (Pi m d n e)) = 0 := by
  simp only [Pi, RAOq_kron4, RBOq_kron4, trace_one_div_self hd, trace_one_div_self he, one_smul]
  abel

theorem Pi_eq_sq : Pi m d n e = (1 : ℚ) • ((Pi m d n e)ᵀ * Pi m d n e) := by
  rw [Pi_transpose, Pi_mul_Pi, one_smul]

theorem trace_W0unbiased (hm : 2 ≤ m) (hn : 2 ≤ n) :
    trace (W0unbiased m d n e) = (d * e : ℕ) := by
  rw [W0unbiased_signed, Matrix.trace_add, Matrix.trace_add, Matrix.trace_smul, Qembed_Cunbiased,
    Matrix.trace_smul, trace_U hm hn, trace_V hm hn, trace_Pi hm hn, smul_eq_mul, smul_eq_mul]
  ring

end Rational

variable (D : Ports)

theorem pi_psd : (toC (Pi D.m D.d D.n D.e)).PosSemidef :=
  transpose_mul_self_sound _ _ _ Pi_eq_sq (by norm_num)

theorem pi_inLV : InLV D (toC (Pi D.m D.d D.n D.e)) := by
  refine ⟨isHermitian_map_of_transpose _ Pi_transpose, ?_, ?_, ?_⟩
  · rw [← toC_RBIBOq, ← toC_RAOq, ← toC_sub, Pi_LV_a D.d_pos, toC_zero]
  · rw [← toC_RAIAOq, ← toC_RBOq, ← toC_sub, Pi_LV_b D.e_pos, toC_zero]
  · rw [← toC_RBOq, ← toC_RAOq, ← toC_RAOq, ← toC_sub, ← toC_sub, ← toC_add,
      Pi_LV_c D.d_pos D.e_pos, toC_zero]

/-- `Π = Q_{P_m ⊗ P_n}` lies in both ordered cones. -/
theorem pi_orderedAB : OrderedAB D (toC (Pi D.m D.d D.n D.e)) :=
  ⟨pi_inLV D, pi_psd D, by rw [← toC_RBOq, RBOq_Pi D.e_pos]⟩

theorem pi_orderedBA : OrderedBA D (toC (Pi D.m D.d D.n D.e)) :=
  ⟨pi_inLV D, pi_psd D, by rw [← toC_RAOq, RAOq_Pi D.d_pos]⟩

/-- The third term `2 Q_C` of the unbiased decomposition is `(3/20) Π`. -/
theorem two_QC_Cunbiased :
    (2 : ℂ) • QC D (toC (Cunbiased D.m D.n)) = toC ((3 / 20 : ℚ) • Pi D.m D.d D.n D.e) := by
  rw [← toC_Qembed_eq_QC, Qembed_Cunbiased, toC_smul, toC_smul, smul_smul]
  norm_num

theorem orderedAB_two_QC_Cunbiased : OrderedAB D ((2 : ℂ) • QC D (toC (Cunbiased D.m D.n))) := by
  rw [two_QC_Cunbiased, toC_smul, show ((3 / 20 : ℚ) : ℂ) = ((3 / 20 : ℝ) : ℂ) by norm_num]
  obtain ⟨hLV, hpsd, hR⟩ := pi_orderedAB D
  exact ⟨genLV_smul (isSelfAdjoint_ofReal _) hLV,
    posSemidef_complex_smul hpsd (Complex.zero_le_real.mpr (by norm_num)), by rw [map_smul, hR]⟩

theorem orderedBA_two_QC_Cunbiased : OrderedBA D ((2 : ℂ) • QC D (toC (Cunbiased D.m D.n))) := by
  rw [two_QC_Cunbiased, toC_smul, show ((3 / 20 : ℚ) : ℂ) = ((3 / 20 : ℝ) : ℂ) by norm_num]
  obtain ⟨hLV, hpsd, hR⟩ := pi_orderedBA D
  exact ⟨genLV_smul (isSelfAdjoint_ofReal _) hLV,
    posSemidef_complex_smul hpsd (Complex.zero_le_real.mpr (by norm_num)), by rw [map_smul, hR]⟩

/-- **`subsec:bias`**: with the unbiased states `P_m/2`, `P_n/2` in place of
`θ_m`, `θ_n`, the operator `C` of `eq:C-def` is `(3/40) P_m ⊗ P_n`, which is positive; the
decomposition `eq:signed-decomposition` consists of three positive causally ordered operators;
and the resulting process is causally separable. -/
theorem claim_bias (hD : AllPortsGE2 D) :
    Cunbiased D.m D.n = (3 / 40 : ℚ) • (P D.m ⊗ₖ P D.n) ∧
    (toC (Cunbiased D.m D.n)).PosSemidef ∧
    toC (W0unbiased D.m D.d D.n D.e) =
      toC (U D.m D.d D.n D.e) + toC (V D.m D.d D.n D.e) + (2 : ℂ) • QC D (toC (Cunbiased D.m D.n)) ∧
    OrderedAB D (toC (U D.m D.d D.n D.e)) ∧ OrderedBA D (toC (V D.m D.d D.n D.e)) ∧
    OrderedAB D ((2 : ℂ) • QC D (toC (Cunbiased D.m D.n))) ∧
    OrderedBA D ((2 : ℂ) • QC D (toC (Cunbiased D.m D.n))) ∧
    CausallySeparable D (toC (W0unbiased D.m D.d D.n D.e)) := by
  have hsigned : toC (W0unbiased D.m D.d D.n D.e) =
      toC (U D.m D.d D.n D.e) + toC (V D.m D.d D.n D.e) +
        (2 : ℂ) • QC D (toC (Cunbiased D.m D.n)) := by
    rw [W0unbiased_signed, toC_add, toC_add, toC_smul, toC_Qembed_eq_QC]
    norm_num
  have hU := u_orderedAB D hD
  have hV := v_orderedBA D hD
  have hQA := orderedAB_two_QC_Cunbiased D
  have hAB : OrderedAB D (toC (U D.m D.d D.n D.e) + (2 : ℂ) • QC D (toC (Cunbiased D.m D.n))) :=
    orderedAB_add D hU hQA
  have hW : toC (W0unbiased D.m D.d D.n D.e) =
      (toC (U D.m D.d D.n D.e) + (2 : ℂ) • QC D (toC (Cunbiased D.m D.n))) +
        toC (V D.m D.d D.n D.e) := by
    rw [hsigned]; abel
  have hvalid : Valid D (toC (W0unbiased D.m D.d D.n D.e)) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hW]; exact genLV_add hAB.1 hV.1
    · rw [hW]; exact hAB.2.1.add hV.2.1
    · rw [trace_toC, trace_W0unbiased hD.1 hD.2.2.1]
      norm_cast
  refine ⟨Cunbiased_eq, transpose_mul_self_sound _ _ _ Cunbiased_eq_sq (by norm_num), hsigned,
    hU, hV, hQA, orderedBA_two_QC_Cunbiased D, hvalid, _, _, hAB, hV, hW⟩

end CausalNonpurifiability
