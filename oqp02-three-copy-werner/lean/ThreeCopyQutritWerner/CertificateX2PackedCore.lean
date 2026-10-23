module

public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Tactic
public import ThreeCopyQutritWerner.CertificatePackedMaskedDigits
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.FreeCommRing
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.RingTheory.Valuation.IsTrivialOn
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Topology.Algebra.Module.UniformConvergence
public import Mathlib.Topology.Algebra.SeparationQuotient.Section
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


/-! Packed big-number engine, core arithmetic.

Signed integer data are stored as offset-encoded naturals: slot `k` (width `W` bits) of `E`
holds `v_k + 2^o`. One actual product of a reversed packed row with a block operand of `q`
contiguous fibers of length `n` yields every row-fiber dot product as a middle digit
(position `j*n + n - 1`). The check `rowBlockCheck` compares those digits with a compact
candidate by one spreading multiplication and one mask. `rowBlockCheck_sound` turns a passed
check into the exact signed dot-product identities. No data or numerical claim occurs here. -/

open scoped BigOperators
open Polynomial

namespace ThreeCopyQutritWerner
namespace X2

/-! ### Encodings -/

/-- Digit `k` of `E` in base `2^W`. -/
def dig (W E k : ℕ) : ℕ := E / 2 ^ (W * k) % 2 ^ W

/-- Signed entry `k` of an offset-`o` encoded packed natural `E`. -/
def ent (W o E k : ℕ) : ℤ := (dig W E k : ℤ) - 2 ^ o

/-- `∑_{s<L} 2^(W s)` in a kernel-friendly closed form. -/
def repunit (W L : ℕ) : ℕ := (2 ^ (W * L) - 1) / (2 ^ W - 1)

/-- The offset `2^o` placed in each of `L` slots of width `W`. -/
def offset (W o L : ℕ) : ℕ := 2 ^ o * repunit W L

/-- Selects the `q` slots at positions `j*n`. -/
def blockMask (W n q : ℕ) : ℕ := (2 ^ W - 1) * repunit (W * n) q

/-- The bits `a .. W-1` of each of `L` slots. -/
def highMask (W a L : ℕ) : ℕ := ((2 ^ (W - a) - 1) <<< a) * repunit W L

/-- Range and digit bound of a small operand: every digit is `< 2^(o+1)`. -/
def boundCheck (W o L E : ℕ) : Bool :=
  Nat.blt E (2 ^ (W * L)) && Nat.beq (E &&& highMask W (o + 1) L) 0

/-- One row-block product check. `xE`: offset-`ox` encoded reversed row (`n` slots);
`GE`: offset-`(W-1)` encoded block operand (`q` fibers of `n` slots); `zE`: offset-`(W-1)`
encoded candidate (`q` slots). -/
def rowBlockCheck (W ox n q xE GE zE : ℕ) : Bool :=
  let P : ℤ := ((xE : ℤ) - (offset W ox n : ℤ)) * ((GE : ℤ) - (offset W (W - 1) (q * n) : ℤ))
  let N1 : ℕ := (P + (offset W (W - 1) ((q + 1) * n) : ℤ)).toNat
  let msk : ℕ := blockMask W n q
  Nat.blt GE (2 ^ (W * (q * n))) && Nat.blt zE (2 ^ (W * q)) &&
    Nat.beq ((N1 >>> (W * (n - 1))) &&& msk) ((zE * repunit (W * (n - 1)) q) &&& msk)

/-- Many small operands against one block operand. -/
def rowBlockCheckAll (W ox n q GE : ℕ) : List (ℕ × ℕ) → Bool
  | [] => true
  | p :: rest => rowBlockCheck W ox n q p.1 GE p.2 && rowBlockCheckAll W ox n q GE rest

/-- `acc + ∑ᵢ aᵢ Fᵢ` (left fold over two lists). -/
def axpyFold : List ℤ → List ℤ → ℤ → ℤ
  | a :: as, F :: Fs, acc => axpyFold as Fs (acc + a * F)
  | _, _, acc => acc

/-- Linear-combination check: `outE` (offset `W-1`, `L` slots, in range) is the packed
`∑ᵢ aᵢ Fᵢ` of the packed fibers `Fs` (offset `W-1`, `L` slots). One big-integer
multiply-add per term covers all `L` slots. -/
def axpyCheck (W L : ℕ) (as : List ℤ) (Fs : List ℕ) (outE : ℕ) : Bool :=
  Nat.blt outE (2 ^ (W * L)) &&
    decide (axpyFold as (Fs.map (fun F : ℕ => (F : ℤ) - (offset W (W - 1) L : ℤ))) 0 =
      (outE : ℤ) - (offset W (W - 1) L : ℤ))

/-- `axpyFold` through the list recursor directly (kernel reduction: one iota step per term). -/
noncomputable def axpyFoldR (as : List ℤ) : List ℤ → ℤ → ℤ :=
  @List.rec ℤ (fun _ => List ℤ → ℤ → ℤ) (fun _ acc => acc)
    (fun a _ ih Fs acc => @List.casesOn ℤ (fun _ => ℤ) Fs acc (fun F Fs' => ih Fs' (acc + a * F))) as

/-- `axpyCheck` evaluated through `axpyFoldR`. -/
noncomputable def axpyCheckR (W L : ℕ) (as : List ℤ) (Fs : List ℕ) (outE : ℕ) : Bool :=
  Nat.blt outE (2 ^ (W * L)) &&
    decide (axpyFoldR as (Fs.map (fun F : ℕ => (F : ℤ) - (offset W (W - 1) L : ℤ))) 0 =
      (outE : ℤ) - (offset W (W - 1) L : ℤ))

theorem axpyFoldR_eq : ∀ (as Fs : List ℤ) (acc : ℤ), axpyFoldR as Fs acc = axpyFold as Fs acc
  | [], Fs, acc => by cases Fs <;> rfl
  | a :: as, [], acc => rfl
  | a :: as, F :: Fs, acc => by
    show axpyFoldR as Fs (acc + a * F) = axpyFold as Fs (acc + a * F)
    exact axpyFoldR_eq as Fs _

theorem axpyCheckR_eq (W L : ℕ) (as : List ℤ) (Fs : List ℕ) (outE : ℕ) :
    axpyCheckR W L as Fs outE = axpyCheck W L as Fs outE := by
  unfold axpyCheckR axpyCheck
  rw [axpyFoldR_eq]

/-- Signed slot `k` (offset `2^(W-1)`) by shift and mask, for kernel evaluation. -/
def extractInt (W E k : ℕ) : ℤ :=
  Int.ofNat ((E >>> (W * k)) &&& (2 ^ W - 1)) - Int.ofNat (2 ^ (W - 1))

theorem extractInt_eq (W E k : ℕ) : extractInt W E k = ent W (W - 1) E k := by
  unfold extractInt ent dig
  rw [Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]
  simp only [Int.ofNat_eq_coe, Nat.cast_pow, Nat.cast_ofNat]

/-- Contiguous concatenation of packed fibers of `L` slots: fiber `j` occupies slots
`j*L .. j*L + L - 1`. -/
def concatFibers (W L : ℕ) : List ℕ → ℕ
  | [] => 0
  | f :: fs => f + (concatFibers W L fs <<< (W * L))

/-! ### Elementary digit arithmetic -/

theorem digit_isolate (B k lo d hi : ℕ) (hB : 0 < B) (hlo : lo < B ^ k) (hd : d < B) :
    (lo + d * B ^ k + B ^ (k + 1) * hi) / B ^ k % B = d := by
  have hBk : 0 < B ^ k := pow_pos hB k
  have h1 : lo + d * B ^ k + B ^ (k + 1) * hi = lo + B ^ k * (d + B * hi) := by
    rw [pow_succ]; ring
  rw [h1, Nat.add_mul_div_left _ _ hBk, Nat.div_eq_of_lt hlo, zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]

theorem sum_digits_lt (B : ℕ) (f : ℕ → ℕ) (hf : ∀ s, f s < B) :
    ∀ k : ℕ, ∑ s ∈ Finset.range k, f s * B ^ s < B ^ k
  | 0 => by simp
  | k + 1 => by
    have ih := sum_digits_lt B f hf k
    rw [Finset.sum_range_succ, pow_succ]
    calc ∑ s ∈ Finset.range k, f s * B ^ s + f k * B ^ k
        < B ^ k + f k * B ^ k := Nat.add_lt_add_right ih _
      _ = (f k + 1) * B ^ k := by ring
      _ ≤ B * B ^ k := Nat.mul_le_mul_right _ (hf k)
      _ = B ^ k * B := mul_comm _ _

theorem sum_digit (B L : ℕ) (f : ℕ → ℕ) (hB : 0 < B) (hf : ∀ s, f s < B) (k : ℕ) (hk : k < L) :
    (∑ s ∈ Finset.range L, f s * B ^ s) / B ^ k % B = f k := by
  have hlo := sum_digits_lt B f hf k
  have hL : L = (k + 1) + (L - (k + 1)) := by omega
  have hsplit : ∑ s ∈ Finset.range L, f s * B ^ s =
      (∑ s ∈ Finset.range k, f s * B ^ s) + f k * B ^ k +
        B ^ (k + 1) * ∑ t ∈ Finset.range (L - (k + 1)), f (k + 1 + t) * B ^ t := by
    conv_lhs => rw [hL]
    rw [Finset.sum_range_add, Finset.sum_range_succ, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    rw [pow_add]
    ring
  rw [hsplit]
  exact digit_isolate B k _ _ _ hB hlo (hf k)

theorem digit_expansion (B : ℕ) (hB : 0 < B) (L : ℕ) :
    ∀ E : ℕ, E < B ^ L → E = ∑ k ∈ Finset.range L, E / B ^ k % B * B ^ k := by
  induction L with
  | zero =>
    intro E hE
    have h0 : E = 0 := by simpa using hE
    simp [h0]
  | succ L ih =>
    intro E hE
    have hq : E / B < B ^ L := by
      rw [Nat.div_lt_iff_lt_mul hB, ← pow_succ]
      exact hE
    rw [Finset.sum_range_succ']
    have hsum : ∑ k ∈ Finset.range L, E / B ^ (k + 1) % B * B ^ (k + 1)
        = B * ∑ k ∈ Finset.range L, E / B / B ^ k % B * B ^ k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [pow_succ', ← Nat.div_div_eq_div_mul]
      ring
    rw [hsum, ← ih (E / B) hq]
    simp only [pow_zero, Nat.div_one, mul_one]
    exact (Nat.div_add_mod E B).symm

theorem digit_expansion_pow (W L E : ℕ) (hE : E < 2 ^ (W * L)) :
    E = ∑ k ∈ Finset.range L, E / 2 ^ (W * k) % 2 ^ W * 2 ^ (W * k) := by
  have h := digit_expansion (2 ^ W) (by positivity) L E (by rwa [← pow_mul])
  simpa only [← pow_mul] using h

theorem repunit_eq (W L : ℕ) (hW : 1 ≤ W) :
    repunit W L = ∑ s ∈ Finset.range L, 2 ^ (W * s) := by
  unfold repunit
  have h2 : 2 ≤ 2 ^ W := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hW
  have hs : ∑ s ∈ Finset.range L, 2 ^ (W * s) = ∑ s ∈ Finset.range L, (2 ^ W) ^ s := by
    apply Finset.sum_congr rfl
    intro s _
    rw [pow_mul]
  rw [hs, Nat.geomSum_eq h2 L, ← pow_mul]

/-- Signed reconstruction: an encoded natural is the packed sum of its entries. -/
theorem ent_expansion (W o L E : ℕ) (hW : 1 ≤ W) (hE : E < 2 ^ (W * L)) :
    (E : ℤ) - (offset W o L : ℤ) = ∑ k ∈ Finset.range L, ent W o E k * 2 ^ (W * k) := by
  have hx := digit_expansion_pow W L E hE
  have hr := repunit_eq W L hW
  unfold offset ent dig
  rw [hr]
  conv_lhs => rw [hx]
  rw [Nat.cast_mul, Nat.cast_sum, Nat.cast_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  first | (push_cast; ring) | push_cast

/-! ### Repetition and spreading digits -/

theorem geom_lt (c N : ℕ) (hN : N < c) :
    ∀ j : ℕ, N * ∑ l ∈ Finset.range j, c ^ l < c ^ j
  | 0 => by simp
  | j + 1 => by
    have ih := geom_lt c N hN j
    rw [Finset.sum_range_succ, mul_add, pow_succ]
    calc N * ∑ l ∈ Finset.range j, c ^ l + N * c ^ j
        < c ^ j + N * c ^ j := Nat.add_lt_add_right ih _
      _ = (N + 1) * c ^ j := by ring
      _ ≤ c * c ^ j := Nat.mul_le_mul_right _ hN
      _ = c ^ j * c := mul_comm _ _

theorem geom_split (c q j : ℕ) (hj : j < q) :
    ∑ l ∈ Finset.range q, c ^ l =
      ∑ l ∈ Finset.range j, c ^ l + c ^ j +
        c ^ (j + 1) * ∑ t ∈ Finset.range (q - (j + 1)), c ^ t := by
  have hq : q = (j + 1) + (q - (j + 1)) := by omega
  conv_lhs => rw [hq]
  rw [Finset.sum_range_add, Finset.sum_range_succ, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- Repetition: `N * ∑_{l<q} (B^n)^l` has digit `N % B` at every position `j*n`. -/
theorem repeat_digit (B n q N j : ℕ) (hB : 0 < B) (hn : 1 ≤ n) (hN : N < B ^ n) (hj : j < q) :
    (N * ∑ l ∈ Finset.range q, (B ^ n) ^ l) / B ^ (j * n) % B = N % B := by
  have e1 : (B ^ n) ^ j = B ^ (j * n) := by rw [← pow_mul, mul_comm]
  have e3 : (B ^ n) ^ (j + 1) = B ^ (j * n + 1) * B ^ (n - 1) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := ⟨n - 1, by omega⟩
    rw [show r + 1 - 1 = r by omega]
    ring
  have hmid : N * (B ^ n) ^ j = 0 + N % B * B ^ (j * n) + B ^ (j * n + 1) * (N / B) := by
    rw [e1, pow_succ]
    have := Nat.mod_add_div N B
    calc N * B ^ (j * n) = (N % B + B * (N / B)) * B ^ (j * n) := by rw [this]
      _ = _ := by ring
  have htot : N * ∑ l ∈ Finset.range q, (B ^ n) ^ l =
      N * ∑ l ∈ Finset.range j, (B ^ n) ^ l + N % B * B ^ (j * n) +
        B ^ (j * n + 1) * (N / B + N * B ^ (n - 1) *
          ∑ t ∈ Finset.range (q - (j + 1)), (B ^ n) ^ t) := by
    rw [geom_split (B ^ n) q j hj, mul_add, mul_add, hmid, e3]
    ring
  have hlo : N * ∑ l ∈ Finset.range j, (B ^ n) ^ l < B ^ (j * n) := by
    rw [← e1]
    exact geom_lt (B ^ n) N hN j
  rw [htot]
  exact digit_isolate B (j * n) _ _ _ hB hlo (Nat.mod_lt _ hB)

/-- Spreading: `N * ∑_{l<q} (B^m)^l` has digit `j` of `N` at position `j*(m+1)` when
`N < B^q` and `q ≤ m`. -/
theorem spread_digit (B m q N j : ℕ) (hB : 0 < B) (hqm : q ≤ m) (hN : N < B ^ q) (hj : j < q) :
    (N * ∑ l ∈ Finset.range q, (B ^ m) ^ l) / B ^ (j * (m + 1)) % B = N / B ^ j % B := by
  have hNc : N < B ^ m := lt_of_lt_of_le hN (Nat.pow_le_pow_right hB hqm)
  have e1 : B ^ j * (B ^ m) ^ j = B ^ (j * (m + 1)) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  have e2 : B ^ (j + 1) * (B ^ m) ^ j = B ^ (j * (m + 1) + 1) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  have e3 : (B ^ m) ^ (j + 1) = B ^ (j * (m + 1) + 1) * B ^ (m - 1 - j) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    obtain ⟨r, hr⟩ : ∃ r, m = j + 1 + r := ⟨m - (j + 1), by omega⟩
    subst hr
    rw [show j + 1 + r - 1 - j = r by omega]
    ring
  have hN1 : N = N % B ^ j + B ^ j * (N / B ^ j % B) + B ^ (j + 1) * (N / B ^ (j + 1)) := by
    have h1 := (Nat.mod_add_div N (B ^ j)).symm
    have h2 := (Nat.mod_add_div (N / B ^ j) B).symm
    rw [Nat.div_div_eq_div_mul, ← pow_succ] at h2
    calc N = N % B ^ j + B ^ j * (N / B ^ j) := h1
      _ = N % B ^ j + B ^ j * (N / B ^ j % B + B * (N / B ^ (j + 1))) := by rw [← h2]
      _ = _ := by ring
  have hmid : N * (B ^ m) ^ j = N % B ^ j * (B ^ m) ^ j + N / B ^ j % B * B ^ (j * (m + 1)) +
      B ^ (j * (m + 1) + 1) * (N / B ^ (j + 1)) := by
    rw [← e1, ← e2]
    calc N * (B ^ m) ^ j
        = (N % B ^ j + B ^ j * (N / B ^ j % B) + B ^ (j + 1) * (N / B ^ (j + 1))) * (B ^ m) ^ j := by
          rw [← hN1]
      _ = _ := by ring
  have htot : N * ∑ l ∈ Finset.range q, (B ^ m) ^ l =
      (N * ∑ l ∈ Finset.range j, (B ^ m) ^ l + N % B ^ j * (B ^ m) ^ j) +
        N / B ^ j % B * B ^ (j * (m + 1)) +
        B ^ (j * (m + 1) + 1) * (N / B ^ (j + 1) + N * B ^ (m - 1 - j) *
          ∑ t ∈ Finset.range (q - (j + 1)), (B ^ m) ^ t) := by
    rw [geom_split (B ^ m) q j hj, mul_add, mul_add, hmid, e3]
    ring
  have hlo : N * ∑ l ∈ Finset.range j, (B ^ m) ^ l + N % B ^ j * (B ^ m) ^ j < B ^ (j * (m + 1)) := by
    have g := geom_lt (B ^ m) N hNc j
    have hlo' : N % B ^ j < B ^ j := Nat.mod_lt _ (pow_pos hB j)
    rw [← e1]
    calc N * ∑ l ∈ Finset.range j, (B ^ m) ^ l + N % B ^ j * (B ^ m) ^ j
        < (B ^ m) ^ j + N % B ^ j * (B ^ m) ^ j := Nat.add_lt_add_right g _
      _ = (N % B ^ j + 1) * (B ^ m) ^ j := by ring
      _ ≤ B ^ j * (B ^ m) ^ j := Nat.mul_le_mul_right _ hlo'
  rw [htot]
  exact digit_isolate B (j * (m + 1)) _ _ _ hB hlo (Nat.mod_lt _ hB)

/-! ### Digits of the masks, shifts and offsets -/

theorem dig_shift (W x s k : ℕ) : dig W (x >>> (W * s)) k = dig W x (k + s) := by
  unfold dig
  rw [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← pow_add,
    show W * s + W * k = W * (k + s) by ring]

theorem dig_land_of_full (W x msk k : ℕ) (hm : dig W msk k = 2 ^ W - 1) :
    dig W (x &&& msk) k = dig W x k := by
  unfold dig at hm ⊢
  exact (certificatePackedMaskedDigit x msk (x &&& msk) (W * k) W rfl hm).symm

theorem dig_land (W x y k : ℕ) : dig W (x &&& y) k = dig W x k &&& dig W y k := by
  unfold dig
  rw [Nat.and_div_two_pow, Nat.and_mod_two_pow]

theorem repunit_eq_pow (W n L : ℕ) (hW : 1 ≤ W) (hn : 1 ≤ n) :
    repunit (W * n) L = ∑ l ∈ Finset.range L, ((2 ^ W) ^ n) ^ l := by
  rw [repunit_eq (W * n) L (Nat.mul_pos (by omega) (by omega))]
  apply Finset.sum_congr rfl
  intro l _
  rw [← pow_mul, ← pow_mul, mul_assoc]

theorem blockMask_dig (W n q j : ℕ) (hW : 1 ≤ W) (hn : 1 ≤ n) (hj : j < q) :
    dig W (blockMask W n q) (j * n) = 2 ^ W - 1 := by
  have hB : 0 < 2 ^ W := by positivity
  have hlt1 : 2 ^ W - 1 < 2 ^ W := Nat.sub_lt hB (by norm_num)
  have hlt : 2 ^ W - 1 < (2 ^ W) ^ n :=
    calc 2 ^ W - 1 < 2 ^ W := hlt1
      _ = (2 ^ W) ^ 1 := (pow_one _).symm
      _ ≤ (2 ^ W) ^ n := Nat.pow_le_pow_right hB hn
  have h := repeat_digit (2 ^ W) n q (2 ^ W - 1) j hB hn hlt hj
  rw [Nat.mod_eq_of_lt hlt1] at h
  unfold blockMask dig
  rw [repunit_eq_pow W n q hW hn, pow_mul]
  exact h

end X2
end ThreeCopyQutritWerner
