module

public import ThreeCopyQutritWerner.CertificateX2InputIB

@[expose] public section


/-!
# Input stage: T2-blocks from four stored upper blocks

For a canonical arrangement (type-sorted, the last site of the largest type), `σ · x2Embed` at the pairs
`(x₀ ≤ y₀)`, `(x₁ ≤ y₁)` (first two sites) and every pair `(a₂ ≤ b₂)` of the last site is
`2 (U₁ ± U₂ ± U₃ ± U₄)` at slot `upos m₂ a₂ b₂`, with `U₁ = U((x₀,x₁),(y₀,y₁))`, `U₂ = U((y₀,x₁),(x₀,y₁))`,
`U₃ = U((x₀,y₁),(y₀,x₁))`, `U₄ = U((y₀,y₁),(x₀,x₁))` (stored upper blocks; signs per parity pattern, see
`x2Sel8_*`). `t2Check` is one natural linear combination of the four blocks with offset scalars
`s + 4` (`s = ±2`); `t2Check_sound` gives every slot.
-/

open scoped BigOperators

namespace ThreeCopyQutritWerner
namespace X2

/-- A T2-block: `T = s₁ U₁ + s₂ U₂ + s₃ U₃ + s₄ U₄` with offset scalars `sᵢ + 4`; the four blocks are
range- and slot-bounded (`2^240`). -/
noncomputable def t2Check (W L : ℕ) (s1 s2 s3 s4 U1 U2 U3 U4 T : ℕ) : Bool :=
  slotBoundCheck W 240 L U1 && slotBoundCheck W 240 L U2 && slotBoundCheck W 240 L U3 &&
    slotBoundCheck W 240 L U4 &&
    natAxpyCheck W L 2 [s1, s2, s3, s4] [U1, U2, U3, U4] T (natAxpyCorr W L 2 [U1, U2, U3, U4])

theorem t2Check_sound (W L : ℕ) (s1 s2 s3 s4 U1 U2 U3 U4 T : ℕ) (hW : 256 ≤ W)
    (hs : s1 ≤ 8 ∧ s2 ≤ 8 ∧ s3 ≤ 8 ∧ s4 ≤ 8)
    (hc : t2Check W L s1 s2 s3 s4 U1 U2 U3 U4 T = true) (k : ℕ) (hk : k < L) :
    ent W (W - 1) T k = ((s1 : ℤ) - 4) * ent W (W - 1) U1 k + (((s2 : ℤ) - 4) * ent W (W - 1) U2 k +
      (((s3 : ℤ) - 4) * ent W (W - 1) U3 k + ((s4 : ℤ) - 4) * ent W (W - 1) U4 k)) := by
  unfold t2Check at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, hax⟩ := hc
  obtain ⟨l1, b1⟩ := slotBoundCheck_sound W 240 L U1 (by omega) h1
  obtain ⟨l2, b2⟩ := slotBoundCheck_sound W 240 L U2 (by omega) h2
  obtain ⟨l3, b3⟩ := slotBoundCheck_sound W 240 L U3 (by omega) h3
  obtain ⟨l4, b4⟩ := slotBoundCheck_sound W 240 L U4 (by omega) h4
  have hl : ∀ k, lincomb W (sScalars 2 [s1, s2, s3, s4]) [U1, U2, U3, U4] k =
      ((s1 : ℤ) - 4) * ent W (W - 1) U1 k + (((s2 : ℤ) - 4) * ent W (W - 1) U2 k +
        (((s3 : ℤ) - 4) * ent W (W - 1) U3 k + ((s4 : ℤ) - 4) * ent W (W - 1) U4 k)) := by
    intro k
    simp only [sScalars, List.map_cons, List.map_nil, lincomb]
    norm_num
  have hE : ∀ E ∈ [U1, U2, U3, U4], E < 2 ^ (W * L) := by
    intro E hE
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hE
    rcases hE with rfl | rfl | rfl | rfl
    · exact l1
    · exact l2
    · exact l3
    · exact l4
  have hsb : ∀ s : ℕ, s ≤ 8 → |(s : ℤ) - 4| ≤ 4 := by
    intro s hs
    rw [abs_le]
    constructor <;> omega
  have hterm : ∀ (s U j : ℕ), s ≤ 8 → |ent W (W - 1) U j| ≤ 2 ^ 240 →
      |((s : ℤ) - 4) * ent W (W - 1) U j| ≤ 4 * 2 ^ 240 := by
    intro s U j hs hU
    rw [abs_mul]
    exact mul_le_mul (hsb s hs) hU (abs_nonneg _) (by norm_num)
  have hlin : ∀ j < L, |lincomb W (sScalars 2 [s1, s2, s3, s4]) [U1, U2, U3, U4] j| < 2 ^ (W - 1) := by
    intro j hj
    rw [hl]
    have t1 := hterm s1 U1 j hs.1 (b1 j hj)
    have t2 := hterm s2 U2 j hs.2.1 (b2 j hj)
    have t3 := hterm s3 U3 j hs.2.2.1 (b3 j hj)
    have t4 := hterm s4 U4 j hs.2.2.2 (b4 j hj)
    have hpow : (16 : ℤ) * 2 ^ 240 < 2 ^ (W - 1) := by
      calc (16 : ℤ) * 2 ^ 240 = 2 ^ 244 := by norm_num
        _ < 2 ^ (W - 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
    have a1 := abs_add_le (((s1 : ℤ) - 4) * ent W (W - 1) U1 j) (((s2 : ℤ) - 4) * ent W (W - 1) U2 j +
      (((s3 : ℤ) - 4) * ent W (W - 1) U3 j + ((s4 : ℤ) - 4) * ent W (W - 1) U4 j))
    have a2 := abs_add_le (((s2 : ℤ) - 4) * ent W (W - 1) U2 j)
      (((s3 : ℤ) - 4) * ent W (W - 1) U3 j + ((s4 : ℤ) - 4) * ent W (W - 1) U4 j)
    have a3 := abs_add_le (((s3 : ℤ) - 4) * ent W (W - 1) U3 j) (((s4 : ℤ) - 4) * ent W (W - 1) U4 j)
    linarith
  rw [← hl k, natAxpyCheck_sound W L 2 [s1, s2, s3, s4] [U1, U2, U3, U4] T (by omega) rfl hE hlin hax k hk]

end X2
end ThreeCopyQutritWerner
