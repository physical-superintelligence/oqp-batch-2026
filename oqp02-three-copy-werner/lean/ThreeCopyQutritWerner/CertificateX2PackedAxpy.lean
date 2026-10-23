module

public import ThreeCopyQutritWerner.CertificateX2PackedCore

@[expose] public section


/-! Packed engine: soundness of the linear-combination check
`axpyCheck`. One kernel multiply-add `acc + a * F` of a scalar with a packed fiber covers every
slot of the fiber, so a passed check gives `∑ᵢ aᵢ (Fᵢ)ₖ = outₖ` for all slots `k` at once. -/

open scoped BigOperators

namespace ThreeCopyQutritWerner
namespace X2

/-- Slot `k` of the linear combination `∑ᵢ aᵢ Fᵢ` of decoded fibers. -/
def lincomb (W : ℕ) : List ℤ → List ℕ → ℕ → ℤ
  | a :: as, F :: Fs, k => a * ent W (W - 1) F k + lincomb W as Fs k
  | _, _, _ => 0

theorem axpyFold_eq (W L : ℕ) (hW : 1 ≤ W) :
    ∀ (as : List ℤ) (Fs : List ℕ) (acc : ℤ), (∀ F ∈ Fs, F < 2 ^ (W * L)) →
      axpyFold as (Fs.map (fun F : ℕ => (F : ℤ) - (offset W (W - 1) L : ℤ))) acc =
        acc + ∑ k ∈ Finset.range L, lincomb W as Fs k * 2 ^ (W * k)
  | [], Fs, acc, _ => by
    cases Fs <;> simp [axpyFold, lincomb]
  | a :: as, [], acc, _ => by
    simp [axpyFold, lincomb]
  | a :: as, F :: Fs, acc, hF => by
    simp only [List.map_cons, axpyFold, lincomb]
    rw [axpyFold_eq W L hW as Fs _ (fun G hG => hF G (by simp [hG])),
      ent_expansion W (W - 1) L F hW (hF F (by simp)), Finset.mul_sum, add_assoc,
      ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    ring

theorem toNat_digit_lt (W : ℕ) (hW : 1 ≤ W) (x : ℤ)
    (hx : -(2 ^ (W - 1)) ≤ x ∧ x < 2 ^ (W - 1)) :
    (x + 2 ^ (W - 1)).toNat < 2 ^ W ∧ (((x + 2 ^ (W - 1)).toNat : ℕ) : ℤ) = x + 2 ^ (W - 1) := by
  have hB2 : (2 : ℤ) ^ W = 2 * 2 ^ (W - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h0 : 0 ≤ x + 2 ^ (W - 1) := by linarith [hx.1]
  have hc : (((x + 2 ^ (W - 1)).toNat : ℕ) : ℤ) = x + 2 ^ (W - 1) := Int.toNat_of_nonneg h0
  refine ⟨?_, hc⟩
  have : (((x + 2 ^ (W - 1)).toNat : ℕ) : ℤ) < 2 ^ W := by
    rw [hc, hB2]
    linarith [hx.2]
  exact_mod_cast this

theorem balanced_sum_cast (W L : ℕ) (hW : 1 ≤ W) (c : ℕ → ℤ)
    (hc : ∀ k < L, -(2 ^ (W - 1)) ≤ c k ∧ c k < 2 ^ (W - 1)) :
    (∑ k ∈ Finset.range L, c k * 2 ^ (W * k)) + (offset W (W - 1) L : ℤ) =
      ((∑ k ∈ Finset.range L,
        (if k < L then (c k + 2 ^ (W - 1)).toNat else 0) * (2 ^ W) ^ k : ℕ) : ℤ) := by
  rw [offset, repunit_eq W L hW, Nat.cast_mul, Nat.cast_sum, Nat.cast_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  rw [if_pos hk', Nat.cast_mul, (toNat_digit_lt W hW (c k) (hc k hk')).2]
  push_cast
  first | (rw [← pow_mul]; ring) | ring

/-- Uniqueness of balanced base-`2^W` digits. -/
theorem balanced_unique (W L : ℕ) (hW : 1 ≤ W) (c d : ℕ → ℤ)
    (hc : ∀ k < L, -(2 ^ (W - 1)) ≤ c k ∧ c k < 2 ^ (W - 1))
    (hd : ∀ k < L, -(2 ^ (W - 1)) ≤ d k ∧ d k < 2 ^ (W - 1))
    (h : ∑ k ∈ Finset.range L, c k * 2 ^ (W * k) = ∑ k ∈ Finset.range L, d k * 2 ^ (W * k))
    (k : ℕ) (hk : k < L) : c k = d k := by
  have h1 := balanced_sum_cast W L hW c hc
  have h2 := balanced_sum_cast W L hW d hd
  rw [h] at h1
  have h4 := Nat.cast_injective (h1.symm.trans h2)
  have hfc : ∀ s, (if s < L then (c s + 2 ^ (W - 1)).toNat else 0) < 2 ^ W := by
    intro s
    split_ifs with hs
    · exact (toNat_digit_lt W hW (c s) (hc s hs)).1
    · positivity
  have hfd : ∀ s, (if s < L then (d s + 2 ^ (W - 1)).toNat else 0) < 2 ^ W := by
    intro s
    split_ifs with hs
    · exact (toNat_digit_lt W hW (d s) (hd s hs)).1
    · positivity
  have e1 := sum_digit (2 ^ W) L _ (by positivity) hfc k hk
  have e2 := sum_digit (2 ^ W) L _ (by positivity) hfd k hk
  rw [h4] at e1
  rw [e1] at e2
  simp only [if_pos hk] at e2
  have hcast : (((c k + 2 ^ (W - 1)).toNat : ℕ) : ℤ) = (((d k + 2 ^ (W - 1)).toNat : ℕ) : ℤ) := by
    rw [e2]
  rw [(toNat_digit_lt W hW (c k) (hc k hk)).2, (toNat_digit_lt W hW (d k) (hd k hk)).2] at hcast
  linarith

/-- Soundness of the linear-combination check. -/
theorem axpyCheck_sound (W L : ℕ) (as : List ℤ) (Fs : List ℕ) (outE : ℕ) (hW : 2 ≤ W)
    (hF : ∀ F ∈ Fs, F < 2 ^ (W * L))
    (hlin : ∀ k < L, |lincomb W as Fs k| < 2 ^ (W - 1))
    (hcheck : axpyCheck W L as Fs outE = true) (k : ℕ) (hk : k < L) :
    lincomb W as Fs k = ent W (W - 1) outE k := by
  simp only [axpyCheck, Bool.and_eq_true, Nat.blt_eq, decide_eq_true_eq] at hcheck
  obtain ⟨hr, he⟩ := hcheck
  have hW1 : 1 ≤ W := by omega
  rw [axpyFold_eq W L hW1 as Fs 0 hF, zero_add, ent_expansion W (W - 1) L outE hW1 hr] at he
  apply balanced_unique W L hW1 _ _ _ _ he k hk
  · intro i hi
    have := abs_lt.mp (hlin i hi)
    constructor <;> linarith [this.1, this.2]
  · intro i hi
    have h0 : (0 : ℤ) ≤ (dig W outE i : ℤ) := by positivity
    have h1 : (dig W outE i : ℤ) < 2 ^ W := by
      exact_mod_cast Nat.mod_lt _ (by positivity)
    have hB2 : (2 : ℤ) ^ W = 2 * 2 ^ (W - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    unfold ent
    constructor <;> linarith

/-- A bound for the slots of a linear combination. -/
theorem lincomb_abs_le (W : ℕ) (A Fb : ℤ) (hA : 0 ≤ A) (hFb : 0 ≤ Fb) (k : ℕ) :
    ∀ (as : List ℤ) (Fs : List ℕ), (∀ a ∈ as, |a| ≤ A) → (∀ F ∈ Fs, |ent W (W - 1) F k| ≤ Fb) →
      |lincomb W as Fs k| ≤ as.length * (A * Fb)
  | [], _, _, _ => by simp [lincomb]
  | _ :: _, [], _, _ => by simp [lincomb] <;> positivity
  | a :: as, F :: Fs, ha, hF => by
    simp only [lincomb, List.length_cons]
    have h1 := lincomb_abs_le W A Fb hA hFb k as Fs (fun b hb => ha b (by simp [hb]))
      (fun G hG => hF G (by simp [hG]))
    have h2 : |a * ent W (W - 1) F k| ≤ A * Fb := by
      rw [abs_mul]
      exact mul_le_mul (ha a (by simp)) (hF F (by simp)) (abs_nonneg _) hA
    calc |a * ent W (W - 1) F k + lincomb W as Fs k|
        ≤ |a * ent W (W - 1) F k| + |lincomb W as Fs k| := abs_add_le _ _
      _ ≤ A * Fb + as.length * (A * Fb) := add_le_add h2 h1
      _ = ((as.length + 1 : ℕ) : ℤ) * (A * Fb) := by push_cast; ring

end X2
end ThreeCopyQutritWerner
