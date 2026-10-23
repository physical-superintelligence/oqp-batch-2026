module

public import ThreeCopyQutritWerner.CertificateX2Reduced

@[expose] public section


/-!
# Finite sanity checks of the route-X2 reduced tables

Kernel-evaluated facts about the concrete tables of `CertificateX2Reduced`: the label tables
are inverted by the arithmetic label maps, the six site permutations are distinct, the block keys
are sorted, and the h-blocks with their multiplicity weights exhaust the carrier rank
`17,314,479 = trace Π` (the completeness count of the bridge).
-/

set_option maxRecDepth 100000

namespace ThreeCopyQutritWerner

/-- Completeness count: `∑_b ν_b r_b = 17,314,479 = trace Π` over the 122 h-blocks. -/
theorem x2_completeness_count :
    ∑ b : x2Key 0, x2Weight 0 b * x2KeySize 0 b = 17314479 := by
  decide +kernel

/-- Block sizes per sector (`1486`, `5826`, `2933`). -/
theorem x2_size_counts :
    (∑ b : x2Key 0, x2KeySize 0 b) = 1486 ∧ (∑ b : x2Key 1, x2KeySize 1 b) = 5826 ∧
      (∑ b : x2Key 2, x2KeySize 2 b) = 2933 := by
  decide +kernel

/-- The S-label table is inverted by `x2SIdx` and lists valid pairs `a ≤ b < m_t`. -/
theorem x2_sLabel_valid : ∀ s : Fin 3, ∀ l : Fin 282,
    x2SIdx s (x2SLabel s l).1 (x2SLabel s l).2.1 (x2SLabel s l).2.2 = l ∧
      (x2SLabel s l).2.1 ≤ (x2SLabel s l).2.2 ∧
      (x2SLabel s l).2.2 < x2Mult s (x2SLabel s l).1 := by
  decide +kernel

/-- The A-label table is inverted by `x2AIdx` and lists valid pairs `a < b < m_t`. -/
theorem x2_aLabel_valid : ∀ s : Fin 3, ∀ l : Fin 231,
    x2AIdx s (x2ALabel s l).1 (x2ALabel s l).2.1 (x2ALabel s l).2.2 = l ∧
      (x2ALabel s l).2.1 < (x2ALabel s l).2.2 ∧
      (x2ALabel s l).2.2 < x2Mult s (x2ALabel s l).1 := by
  decide +kernel

/-- Global block indices do not wrap. -/
theorem x2_keyGlobal_val : ∀ s : Fin 3, ∀ b : x2Key s,
    (x2KeyGlobal s b).val = x2KeyOffset s + b.val := by
  decide +kernel

/-- Every block lists its types sorted, with nonzero multiplicities. -/
theorem x2_keyTypes_sorted : ∀ s : Fin 3, ∀ b : x2Key s,
    x2KeyTypes s b 0 ≤ x2KeyTypes s b 1 ∧ x2KeyTypes s b 1 ≤ x2KeyTypes s b 2 ∧
      0 < x2KeyMult s b 0 ∧ 0 < x2KeyMult s b 1 ∧ 0 < x2KeyMult s b 2 := by
  decide +kernel

/-- The six site permutations are distinct bijections of `Fin 3`. -/
theorem x2_perm3_spec : (∀ p : Fin 6, Function.Bijective (x2Perm3 p)) ∧
    Function.Injective x2Perm3 := by
  decide +kernel

end ThreeCopyQutritWerner
