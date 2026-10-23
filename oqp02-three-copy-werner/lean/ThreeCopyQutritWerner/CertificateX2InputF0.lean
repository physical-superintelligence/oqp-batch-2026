module

public import ThreeCopyQutritWerner.CertificateX2InputIB

@[expose] public section


/-!
# Input stage: runs of the core's input table from stored blocks

The core's input table stores `σ · x2Embed` in `W₂ = 384`-bit offset slots; the input stage computes the
same values in `W₁ = 256`-bit offset slots (T2-blocks). `widen W₁ W₂ n P` re-packs `n` slots of `P` at
`W₂` bits keeping the signed values (`widen_spec`); `runWidenOK W₁ W₂ E p n T q` compares the run of `n`
slots of `E` from slot `p` with the re-packed run of `T` from slot `q` (one shift, one mask, one
re-packing and one comparison), and `runWidenOK_sound` gives every slot of the run.
-/

open scoped BigOperators

namespace ThreeCopyQutritWerner
namespace X2

/-- `n` slots of `P` (`W₁` bits, offset `2^(W₁-1)`) re-packed at `W₂` bits (offset `2^(W₂-1)`). -/
noncomputable def widen (W1 W2 n P : ℕ) : ℕ :=
  spreadDC W1 W2 16 n P + (2 ^ (W2 - 1) - 2 ^ (W1 - 1)) * repunit W2 n

theorem widen_spec (W1 W2 n P : ℕ) (h1 : 1 ≤ W1) (h12 : W1 ≤ W2) :
    widen W1 W2 n P < 2 ^ (W2 * n) ∧ ∀ t < n, ent W2 (W2 - 1) (widen W1 W2 n P) t = ent W1 (W1 - 1) P t := by
  have hW1 : 1 ≤ W2 := by omega
  have hoff : 2 ^ (W1 - 1) ≤ 2 ^ (W2 - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcoef : ∀ t, dig W1 P t + (2 ^ (W2 - 1) - 2 ^ (W1 - 1)) < 2 ^ W2 := by
    intro t
    have hd := dig_lt W1 P t
    have h2 : 2 ^ W2 = 2 * 2 ^ (W2 - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have h3 : 2 ^ W1 = 2 * 2 ^ (W1 - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    omega
  have hsum : widen W1 W2 n P =
      ∑ t ∈ Finset.range n, (dig W1 P t + (2 ^ (W2 - 1) - 2 ^ (W1 - 1))) * (2 ^ W2) ^ t := by
    unfold widen
    rw [spreadDC_eq, repunit_eq W2 n hW1, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    rw [← pow_mul]
    ring
  constructor
  · rw [hsum, pow_mul]
    exact sum_digits_lt (2 ^ W2) _ hcoef n
  · intro t ht
    have hd : dig W2 (widen W1 W2 n P) t = dig W1 P t + (2 ^ (W2 - 1) - 2 ^ (W1 - 1)) := by
      rw [hsum]
      unfold dig
      rw [pow_mul 2 W2 t]
      exact sum_digit (2 ^ W2) n _ (Nat.two_pow_pos W2) hcoef t ht
    unfold ent
    rw [hd, Nat.cast_add, Nat.cast_sub hoff]
    push_cast
    ring

/-- The run of `n` slots of `E` (`W₂` bits) from slot `p` is the re-packed run of `T` (`W₁` bits) from
slot `q`. -/
noncomputable def runWidenOK (W1 W2 E p n T q : ℕ) : Bool :=
  Nat.beq ((E >>> (W2 * p)) &&& (2 ^ (W2 * n) - 1)) (widen W1 W2 n (T >>> (W1 * q)))

theorem runWidenOK_sound (W1 W2 E p n T q : ℕ) (h1 : 1 ≤ W1) (h12 : W1 ≤ W2)
    (hc : runWidenOK W1 W2 E p n T q = true) (t : ℕ) (ht : t < n) :
    ent W2 (W2 - 1) E (t + p) = ent W1 (W1 - 1) T (t + q) := by
  have heq := Nat.eq_of_beq_eq_true hc
  have hd : dig W2 E (t + p) = dig W2 (widen W1 W2 n (T >>> (W1 * q))) t := by
    rw [← dig_shift, ← dig_low W2 _ n t (by omega) ht, heq]
  have e2 := (widen_spec W1 W2 n (T >>> (W1 * q)) h1 h12).2 t ht
  unfold ent at e2 ⊢
  rw [hd, e2, dig_shift]

end X2
end ThreeCopyQutritWerner
