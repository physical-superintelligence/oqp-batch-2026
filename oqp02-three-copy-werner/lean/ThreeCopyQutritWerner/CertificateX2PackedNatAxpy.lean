module

public import ThreeCopyQutritWerner.CertificateX2PackedAxpy

@[expose] public section


/-! Packed engine: natural-number linear-combination check.

Kernel steps are the cost driver, so this check uses only primitive `Nat.add`/`Nat.mul` per term.
Scalars are stored with an offset, `a' = a + 2^oA`; fibers enter as `E + (B - OFF)` with
`B = 2^(W L)`, i.e. their signed packed value plus `B`. Then
`∑ a'ᵢ (Vᵢ + B) ≡ ∑ aᵢ Vᵢ + 2^oA ∑ Vᵢ (mod B)`, and one correction `K` (shared by all
outputs of the same fibers) and one reduction mod `B` compare with the candidate. -/

open scoped BigOperators

namespace ThreeCopyQutritWerner
namespace X2

/-- `acc + ∑ aᵢ Fᵢ` over naturals, through the list recursor with primitive operations. -/
noncomputable def natAxpyFold (as : List ℕ) : List ℕ → ℕ → ℕ :=
  @List.rec ℕ (fun _ => List ℕ → ℕ → ℕ) (fun _ acc => acc)
    (fun a _ ih Fs acc =>
      @List.casesOn ℕ (fun _ => ℕ) Fs acc (fun F Fs' => ih Fs' (Nat.add acc (Nat.mul a F)))) as

/-- Plain sum of products of two lists (zip length). -/
def natDot : List ℕ → List ℕ → ℕ
  | a :: as, F :: Fs => a * F + natDot as Fs
  | _, _ => 0

/-- Fibers shifted to signed-value-plus-`B` form. -/
def natFibers (W L : ℕ) (Es : List ℕ) : List ℕ :=
  Es.map (fun E => E + (2 ^ (W * L) - offset W (W - 1) L))

/-- The correction shared by all outputs of one fiber list. -/
def natAxpyCorr (W L oA : ℕ) (Es : List ℕ) : ℕ :=
  2 ^ (W * L) - (2 ^ oA * (natFibers W L Es).sum) % 2 ^ (W * L) + offset W (W - 1) L

/-- Natural linear-combination check: offset scalars `as'` (`a = a' - 2^oA`), offset-`(W-1)`
fibers `Es` and candidate `outE`, all with `L` slots of width `W`. -/
noncomputable def natAxpyCheck (W L oA : ℕ) (as' : List ℕ) (Es : List ℕ) (outE : ℕ)
    (K : ℕ) : Bool :=
  Nat.blt outE (2 ^ (W * L)) &&
    Nat.beq (Nat.land (Nat.add (natAxpyFold as' (natFibers W L Es) 0) K) (2 ^ (W * L) - 1)) outE

theorem natAxpyFold_eq : ∀ (as Fs : List ℕ) (acc : ℕ), natAxpyFold as Fs acc = acc + natDot as Fs
  | [], Fs, acc => by cases Fs <;> rfl
  | a :: as, [], acc => rfl
  | a :: as, F :: Fs, acc => by
    show natAxpyFold as Fs (acc + a * F) = acc + (a * F + natDot as Fs)
    rw [natAxpyFold_eq as Fs (acc + a * F)]
    ring

/-- The signed scalars of offset scalars. -/
def sScalars (oA : ℕ) (as' : List ℕ) : List ℤ := as'.map (fun a : ℕ => (a : ℤ) - 2 ^ oA)

theorem offset_le_pow (W L : ℕ) (hW : 1 ≤ W) : offset W (W - 1) L ≤ 2 ^ (W * L) := by
  unfold offset
  rw [repunit_eq W L hW]
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, mul_add]
    have h5 : 1 ≤ 2 ^ W := Nat.one_le_two_pow
    have hle : 2 ^ (W - 1) ≤ 2 ^ W - 1 := by
      have h2 : 2 ^ W = 2 * 2 ^ (W - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      have h3 : 1 ≤ 2 ^ (W - 1) := Nat.one_le_two_pow
      omega
    have h1 : 2 ^ (W - 1) * 2 ^ (W * L) ≤ 2 ^ (W * L) * (2 ^ W - 1) := by
      rw [mul_comm]
      exact Nat.mul_le_mul_left _ hle
    have h4 : 2 ^ (W * (L + 1)) = 2 ^ (W * L) * 2 ^ W := by
      rw [mul_add, mul_one, pow_add]
    have h5' : 2 ^ W - 1 + 1 = 2 ^ W := Nat.sub_add_cancel h5
    have h6 : 2 ^ (W * L) * (2 ^ W - 1) + 2 ^ (W * L) = 2 ^ (W * L) * 2 ^ W := by
      calc 2 ^ (W * L) * (2 ^ W - 1) + 2 ^ (W * L) = 2 ^ (W * L) * (2 ^ W - 1 + 1) := by ring
        _ = 2 ^ (W * L) * 2 ^ W := by rw [h5']
    rw [h4]
    omega

theorem natDot_cast (W L oA : ℕ) (hW : 1 ≤ W) :
    ∀ (as' Es : List ℕ), as'.length = Es.length → (∀ E ∈ Es, E < 2 ^ (W * L)) →
      ((natDot as' (natFibers W L Es) : ℕ) : ℤ) =
        (∑ k ∈ Finset.range L, lincomb W (sScalars oA as') Es k * 2 ^ (W * k)) +
          2 ^ oA * (Es.map (fun E : ℕ => (E : ℤ) - (offset W (W - 1) L : ℤ))).sum +
          2 ^ (W * L) * (as'.map (fun a : ℕ => (a : ℤ))).sum
  | [], [], _, _ => by simp [natDot, natFibers, sScalars, lincomb]
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: as', E :: Es, h, hE => by
    have hlen : as'.length = Es.length := by simpa using h
    have ih := natDot_cast W L oA hW as' Es hlen (fun F hF => hE F (by simp [hF]))
    have hE0 : E < 2 ^ (W * L) := hE E (by simp)
    have hexp := ent_expansion W (W - 1) L E hW hE0
    have hoff := offset_le_pow W L hW
    have hsplit : (∑ k ∈ Finset.range L, (((a : ℤ) - 2 ^ oA) * ent W (W - 1) E k +
          lincomb W (List.map (fun a : ℕ => (a : ℤ) - 2 ^ oA) as') Es k) * 2 ^ (W * k)) =
        ((a : ℤ) - 2 ^ oA) * ((E : ℤ) - (offset W (W - 1) L : ℤ)) +
          ∑ k ∈ Finset.range L, lincomb W (List.map (fun a : ℕ => (a : ℤ) - 2 ^ oA) as') Es k *
            2 ^ (W * k) := by
      rw [hexp, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    simp only [natFibers, sScalars, List.map_cons, natDot, lincomb, List.sum_cons] at ih ⊢
    rw [Nat.cast_add, ih, hsplit]
    first | (push_cast [Nat.cast_sub hoff]; ring) | push_cast [Nat.cast_sub hoff]

theorem natFibers_sum_cast (W L : ℕ) (hW : 1 ≤ W) : ∀ (Es : List ℕ),
    (((natFibers W L Es).sum : ℕ) : ℤ) =
      (Es.map (fun E : ℕ => (E : ℤ) - (offset W (W - 1) L : ℤ))).sum +
        Es.length * (2 : ℤ) ^ (W * L)
  | [] => by simp [natFibers]
  | E :: Es => by
    have ih := natFibers_sum_cast W L hW Es
    have hoff := offset_le_pow W L hW
    simp only [natFibers, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    rw [Nat.cast_add, ih]
    first | (push_cast [Nat.cast_sub hoff]; ring) | push_cast [Nat.cast_sub hoff]

theorem ent_range (W E k : ℕ) (hW : 1 ≤ W) :
    -(2 ^ (W - 1) : ℤ) ≤ ent W (W - 1) E k ∧ ent W (W - 1) E k < 2 ^ (W - 1) := by
  have h0 : (0 : ℤ) ≤ (dig W E k : ℤ) := by positivity
  have h1 : (dig W E k : ℤ) < 2 ^ W := by
    exact_mod_cast Nat.mod_lt _ (by positivity)
  have hB2 : (2 : ℤ) ^ W = 2 * 2 ^ (W - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  unfold ent
  constructor <;> linarith

theorem mod_reduce (X O c SV SA B len : ℤ) (h0 : 0 ≤ X + O) (h1 : X + O < B) :
    (X + c * SV + B * SA + (B - (c * (SV + len * B)) % B + O)) % B = X + O := by
  have e1 : (c * (SV + len * B)) % B = (c * SV) % B := by
    rw [mul_add, show c * (len * B) = B * (c * len) by ring, Int.add_mul_emod_self_left]
  have e2 := Int.emod_def (c * SV) B
  rw [e1, e2, show X + c * SV + B * SA + (B - (c * SV - B * (c * SV / B)) + O) =
    (X + O) + B * (SA + 1 + c * SV / B) by ring, Int.add_mul_emod_self_left,
    Int.emod_eq_of_lt h0 h1]

/-- Soundness of the natural linear-combination check. -/
theorem natAxpyCheck_sound (W L oA : ℕ) (as' Es : List ℕ) (outE : ℕ) (hW : 2 ≤ W)
    (hlen : as'.length = Es.length) (hE : ∀ E ∈ Es, E < 2 ^ (W * L))
    (hlin : ∀ k < L, |lincomb W (sScalars oA as') Es k| < 2 ^ (W - 1))
    (hcheck : natAxpyCheck W L oA as' Es outE (natAxpyCorr W L oA Es) = true)
    (k : ℕ) (hk : k < L) :
    lincomb W (sScalars oA as') Es k = ent W (W - 1) outE k := by
  have hW1 : 1 ≤ W := by omega
  simp only [natAxpyCheck, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hcheck
  obtain ⟨hr, hm⟩ := hcheck
  rw [natAxpyFold_eq, zero_add] at hm
  have hm' : (natDot as' (natFibers W L Es) + natAxpyCorr W L oA Es) % 2 ^ (W * L) = outE := by
    rw [← Nat.and_two_pow_sub_one_eq_mod]
    exact hm
  have hmZ : ((natDot as' (natFibers W L Es) : ℤ) + (natAxpyCorr W L oA Es : ℤ)) %
      (2 : ℤ) ^ (W * L) = (outE : ℤ) := by
    have h := congrArg (fun x : ℕ => (x : ℤ)) hm'
    push_cast at h
    exact h
  have hmodle : (2 ^ oA * (natFibers W L Es).sum) % 2 ^ (W * L) ≤ 2 ^ (W * L) :=
    (Nat.mod_lt _ (by positivity)).le
  have hK : ((natAxpyCorr W L oA Es : ℕ) : ℤ) = (2 : ℤ) ^ (W * L) -
      ((2 : ℤ) ^ oA * (((natFibers W L Es).sum : ℕ) : ℤ)) % (2 : ℤ) ^ (W * L) +
        (offset W (W - 1) L : ℤ) := by
    unfold natAxpyCorr
    first | (push_cast [Nat.cast_sub hmodle]; ring) | push_cast [Nat.cast_sub hmodle]
  rw [hK, natDot_cast W L oA hW1 as' Es hlen hE, natFibers_sum_cast W L hW1 Es] at hmZ
  have hc : ∀ i < L, -(2 ^ (W - 1) : ℤ) ≤ lincomb W (sScalars oA as') Es i ∧
      lincomb W (sScalars oA as') Es i < 2 ^ (W - 1) := by
    intro i hi
    have := abs_lt.mp (hlin i hi)
    constructor <;> linarith [this.1, this.2]
  have hS := balanced_sum_cast W L hW1 (lincomb W (sScalars oA as') Es) hc
  have hfc : ∀ s, (if s < L then (lincomb W (sScalars oA as') Es s + 2 ^ (W - 1)).toNat else 0) <
      2 ^ W := by
    intro s
    split_ifs with hs
    · exact (toNat_digit_lt W hW1 _ (hc s hs)).1
    · positivity
  have hlt := sum_digits_lt (2 ^ W) _ hfc L
  have hrange0 : (0 : ℤ) ≤ (∑ k ∈ Finset.range L, lincomb W (sScalars oA as') Es k * 2 ^ (W * k)) +
      (offset W (W - 1) L : ℤ) := by
    rw [hS]
    positivity
  have hrange1 : (∑ k ∈ Finset.range L, lincomb W (sScalars oA as') Es k * 2 ^ (W * k)) +
      (offset W (W - 1) L : ℤ) < (2 : ℤ) ^ (W * L) := by
    rw [hS]
    have hlt' := lt_of_lt_of_eq hlt (show (2 ^ W) ^ L = 2 ^ (W * L) by rw [← pow_mul])
    exact_mod_cast hlt'
  rw [mod_reduce _ _ _ _ _ _ _ hrange0 hrange1] at hmZ
  have hfin : (∑ k ∈ Finset.range L, lincomb W (sScalars oA as') Es k * 2 ^ (W * k)) =
      ∑ k ∈ Finset.range L, ent W (W - 1) outE k * 2 ^ (W * k) := by
    rw [← ent_expansion W (W - 1) L outE hW1 hr]
    linarith [hmZ]
  exact balanced_unique W L hW1 _ _ hc (fun i _ => ent_range W outE i hW1) hfin k hk

end X2
end ThreeCopyQutritWerner
