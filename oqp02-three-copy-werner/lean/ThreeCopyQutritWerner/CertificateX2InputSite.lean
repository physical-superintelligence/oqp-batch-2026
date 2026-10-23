module

public import ThreeCopyQutritWerner.CertificateX2InputDig

@[expose] public section


/-!
# Input stage: site contractions of packed columns

A packed natural `E` with `L = A·(m·B)` slots holds a tensor indexed by `(a, y, b)`, slot
`(a m + y) B + b`. The site contraction with an integer matrix `g = gp - gn` (`gp, gn ≥ 0`),
`(a, x, b) ↦ ∑_y g x y · E(a, y, b)`, is computed with `m` masks and `2m` multiplications:
`siteSel y E` (the slots of site index `y`, moved to site `0`) times the polynomial
`∑_x g x y · 2^(W B x)` places `g x y · E(a, y, b)` at slot `(a, x, b)`; the offsets are corrected by
the packed row sums `siteRS`. `siteApply` returns the result as an offset-encoded natural, and
`siteApply_spec` proves that its slots are the contraction whenever the true values fit in `W - 1`
bits. Applied to the three sites of an image column this gives `GJ = (G ⊗ G ⊗ G) J` column by
column (two masks and multiplications per unit instead of one operation per entry).
-/

open scoped BigOperators

namespace ThreeCopyQutritWerner
namespace X2

/-- `∑_{i<m} f i` by primitive recursion (kernel evaluation: one step per term). -/
noncomputable def natSum (m : ℕ) (f : ℕ → ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => acc + f i) m

theorem natSum_eq (m : ℕ) (f : ℕ → ℕ) : natSum m f = ∑ i ∈ Finset.range m, f i := by
  induction m with
  | zero => rfl
  | succ m ih =>
    show natSum m f + f m = _
    rw [ih, Finset.sum_range_succ]

/-- `∑_{x<m} h x · 2^(W B x)`. -/
noncomputable def sitePoly (W B m : ℕ) (h : ℕ → ℕ) : ℕ := natSum m (fun x => h x * 2 ^ (W * (B * x)))

/-- `∑_y siteSel y E · ∑_x g x y 2^(W B x)`. -/
noncomputable def siteSum (W A m B : ℕ) (g : ℕ → ℕ → ℕ) (E : ℕ) : ℕ :=
  natSum m (fun y => siteSel W A m B y E * sitePoly W B m (fun x => g x y))

/-- The packed natural with value `r x` at every slot `(a, x, b)`. -/
noncomputable def siteRS (W A m B : ℕ) (r : ℕ → ℕ) : ℕ :=
  sitePoly W B m r * repunit W B * repunit (W * (m * B)) A

/-- Row sums `∑_y g x y`. -/
noncomputable def rowSum (m : ℕ) (g : ℕ → ℕ → ℕ) (x : ℕ) : ℕ := natSum m (fun y => g x y)

/-- The site contraction with `gp - gn`, offset-encoded (`W`-bit slots, offset `2^(W-1)`). -/
noncomputable def siteApply (W A m B : ℕ) (gp gn : ℕ → ℕ → ℕ) (E : ℕ) : ℕ :=
  (siteSum W A m B gp E + offset W (W - 1) (A * (m * B)) + 2 ^ (W - 1) * siteRS W A m B (rowSum m gn)) -
    (siteSum W A m B gn E + 2 ^ (W - 1) * siteRS W A m B (rowSum m gp))

/-- The value of the site contraction at slot `(a, x, b)`. -/
def siteVal (W m B : ℕ) (gp gn : ℕ → ℕ → ℕ) (E a x b : ℕ) : ℤ :=
  ∑ y ∈ Finset.range m, ((gp x y : ℤ) - gn x y) * ent W (W - 1) E ((a * m + y) * B + b)

/-! ### Index arithmetic -/

theorem site_idx_lt (A m B a x b : ℕ) (ha : a < A) (hx : x < m) (hb : b < B) :
    (a * m + x) * B + b < A * (m * B) := by
  have h1 : (a * m + x) * B + b < (a * m + x + 1) * B := by nlinarith
  have h2 : a * m + x + 1 ≤ A * m := by nlinarith
  calc (a * m + x) * B + b < (a * m + x + 1) * B := h1
    _ ≤ (A * m) * B := Nat.mul_le_mul_right B h2
    _ = A * (m * B) := by ring

theorem site_idx_div (m B a x b : ℕ) (hb : b < B) :
    ((a * m + x) * B + b) / B = a * m + x := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega : 0 < B), Nat.div_eq_of_lt hb, zero_add]

theorem site_idx_site (m B a x b : ℕ) (hx : x < m) (hb : b < B) :
    ((a * m + x) * B + b) / B % m = x := by
  rw [site_idx_div m B a x b hb, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]

theorem site_idx_mod (m B a x b : ℕ) (hb : b < B) : ((a * m + x) * B + b) % B = b := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]

theorem site_idx_outer (m B a x b : ℕ) (hx : x < m) (hb : b < B) : ((a * m + x) * B + b) / (m * B) = a := by
  have e : (a * m + x) * B + b = (x * B + b) + a * (m * B) := by ring
  have hmB : 0 < m * B := Nat.mul_pos (by omega) (by omega)
  have hlt : x * B + b < m * B := by nlinarith
  rw [e, Nat.add_mul_div_right _ _ hmB, Nat.div_eq_of_lt hlt, zero_add]

theorem site_mod_self (m t y : ℕ) (ht : t < m) (hy : y < m) : (t + y) % m = y ↔ t = 0 := by
  constructor
  · intro h
    by_cases hlt : t + y < m
    · rw [Nat.mod_eq_of_lt hlt] at h
      omega
    · have h2 : (t + y) % m = t + y - m := by
        rw [Nat.mod_eq_sub_mod (show m ≤ t + y by omega), Nat.mod_eq_of_lt (show t + y - m < m by omega)]
      omega
  · intro h
    subst h
    rw [zero_add, Nat.mod_eq_of_lt hy]

/-! ### The selected slots as a double sum -/

theorem siteSel_lt (W A m B y E : ℕ) (hE : E < 2 ^ (W * (A * (m * B)))) :
    siteSel W A m B y E < 2 ^ (W * (A * (m * B))) :=
  lt_of_le_of_lt (le_trans (by unfold siteSel; rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _)
    Nat.and_le_left) hE

theorem siteSel_sum (W A m B y E : ℕ) (hW : 1 ≤ W) (hB : 1 ≤ B) (hy : y < m)
    (hE : E < 2 ^ (W * (A * (m * B)))) :
    siteSel W A m B y E = ∑ a ∈ Finset.range A, ∑ b ∈ Finset.range B,
      dig W E ((a * m + y) * B + b) * 2 ^ (W * (a * (m * B) + b)) := by
  have hx : siteSel W A m B y E = ∑ k ∈ Finset.range (A * (m * B)),
      dig W (siteSel W A m B y E) k * 2 ^ (W * k) :=
    digit_expansion_pow W (A * (m * B)) _ (siteSel_lt W A m B y E hE)
  rw [hx, sum_range_site]
  apply Finset.sum_congr rfl
  intro a ha
  have ha' := Finset.mem_range.mp ha
  rw [Finset.sum_eq_single 0]
  · apply Finset.sum_congr rfl
    intro b hb
    have hb' := Finset.mem_range.mp hb
    rw [siteSel_dig W A m B y E _ hW hB hy]
    have e1 : (a * m + 0) * B + b + B * y = (a * m + y) * B + b := by ring
    have hc : (a * m + 0) * B + b + B * y < A * (m * B) ∧ ((a * m + 0) * B + b + B * y) / B % m = y := by
      rw [e1]
      exact ⟨site_idx_lt A m B a y b ha' hy hb', site_idx_site m B a y b hy hb'⟩
    rw [if_pos hc, e1]
    congr 2
    ring
  · intro t ht ht0
    have ht' := Finset.mem_range.mp ht
    apply Finset.sum_eq_zero
    intro b hb
    have hb' := Finset.mem_range.mp hb
    rw [siteSel_dig W A m B y E _ hW hB hy]
    have e1 : (a * m + t) * B + b + B * y = (a * m + (t + y)) * B + b := by ring
    have hc : ¬ ((a * m + t) * B + b + B * y < A * (m * B) ∧ ((a * m + t) * B + b + B * y) / B % m = y) := by
      rintro ⟨_, h2⟩
      rw [e1, site_idx_div m B a (t + y) b hb', Nat.add_comm, Nat.add_mul_mod_self_right] at h2
      exact ht0 ((site_mod_self m t y ht' hy).mp h2)
    rw [if_neg hc, zero_mul]
  · intro h0
    exact absurd (Finset.mem_range.mpr (by omega)) h0

/-! ### The pieces as triple sums over `(a, x, b)` -/

theorem siteSum_eq (W A m B : ℕ) (g : ℕ → ℕ → ℕ) (E : ℕ) (hW : 1 ≤ W) (hB : 1 ≤ B)
    (hE : E < 2 ^ (W * (A * (m * B)))) :
    siteSum W A m B g E = ∑ a ∈ Finset.range A, ∑ x ∈ Finset.range m, ∑ b ∈ Finset.range B,
      (∑ y ∈ Finset.range m, g x y * dig W E ((a * m + y) * B + b)) * 2 ^ (W * ((a * m + x) * B + b)) := by
  unfold siteSum sitePoly
  rw [natSum_eq]
  have h1 : ∀ y ∈ Finset.range m, siteSel W A m B y E * natSum m (fun x => g x y * 2 ^ (W * (B * x))) =
      ∑ a ∈ Finset.range A, ∑ x ∈ Finset.range m, ∑ b ∈ Finset.range B,
        g x y * dig W E ((a * m + y) * B + b) * 2 ^ (W * ((a * m + x) * B + b)) := by
    intro y hy
    rw [siteSel_sum W A m B y E hW hB (Finset.mem_range.mp hy) hE, natSum_eq, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro b _
    rw [show W * ((a * m + x) * B + b) = W * (a * (m * B) + b) + W * (B * x) by ring, pow_add]
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_mul]

theorem siteRS_eq (W A m B : ℕ) (r : ℕ → ℕ) (hW : 1 ≤ W) (hB : 1 ≤ B) (hm : 1 ≤ m) :
    siteRS W A m B r = ∑ a ∈ Finset.range A, ∑ x ∈ Finset.range m, ∑ b ∈ Finset.range B,
      r x * 2 ^ (W * ((a * m + x) * B + b)) := by
  have hWmB : 1 ≤ W * (m * B) := Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega))
  calc siteRS W A m B r
      = (∑ x ∈ Finset.range m, r x * 2 ^ (W * (B * x))) * (∑ b ∈ Finset.range B, 2 ^ (W * b)) *
          (∑ a ∈ Finset.range A, 2 ^ (W * (m * B) * a)) := by
        unfold siteRS sitePoly
        rw [natSum_eq, repunit_eq W B hW, repunit_eq (W * (m * B)) A hWmB]
    _ = ∑ a ∈ Finset.range A, (∑ x ∈ Finset.range m, r x * 2 ^ (W * (B * x))) *
          (∑ b ∈ Finset.range B, 2 ^ (W * b)) * 2 ^ (W * (m * B) * a) := by rw [Finset.mul_sum]
    _ = _ := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro b _
        rw [show W * ((a * m + x) * B + b) = W * (m * B) * a + (W * (B * x) + W * b) by ring, pow_add,
          pow_add]
        ring

theorem offset_site_eq (W A m B o : ℕ) (hW : 1 ≤ W) :
    offset W o (A * (m * B)) = ∑ a ∈ Finset.range A, ∑ x ∈ Finset.range m, ∑ b ∈ Finset.range B,
      2 ^ o * 2 ^ (W * ((a * m + x) * B + b)) := by
  unfold offset
  rw [repunit_eq W _ hW, Finset.mul_sum, sum_range_site]

/-! ### Linear algebra of triple sums over `(a, x, b)` -/

/-- `∑_{a,x,b} c a x b · 2^(W((a m + x) B + b))` over `a < A`, `x < m`, `b < B`. -/
def siteF (W A m B : ℕ) (c : ℕ → ℕ → ℕ → ℤ) : ℤ :=
  ∑ a ∈ Finset.range A, ∑ x ∈ Finset.range m, ∑ b ∈ Finset.range B, c a x b * 2 ^ (W * ((a * m + x) * B + b))

theorem siteF_add (W A m B : ℕ) (c d : ℕ → ℕ → ℕ → ℤ) :
    siteF W A m B c + siteF W A m B d = siteF W A m B (fun a x b => c a x b + d a x b) := by
  unfold siteF
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem siteF_sub (W A m B : ℕ) (c d : ℕ → ℕ → ℕ → ℤ) :
    siteF W A m B c - siteF W A m B d = siteF W A m B (fun a x b => c a x b - d a x b) := by
  unfold siteF
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem siteF_smul (W A m B : ℕ) (k : ℤ) (c : ℕ → ℕ → ℕ → ℤ) :
    k * siteF W A m B c = siteF W A m B (fun a x b => k * c a x b) := by
  unfold siteF
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem siteF_congr (W A m B : ℕ) (c d : ℕ → ℕ → ℕ → ℤ)
    (h : ∀ a < A, ∀ x < m, ∀ b < B, c a x b = d a x b) : siteF W A m B c = siteF W A m B d := by
  unfold siteF
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro b hb
  rw [h a (Finset.mem_range.mp ha) x (Finset.mem_range.mp hx) b (Finset.mem_range.mp hb)]

theorem siteF_slots (W A m B : ℕ) (f : ℕ → ℤ) :
    siteF W A m B (fun a x b => f ((a * m + x) * B + b)) =
      ∑ k ∈ Finset.range (A * (m * B)), f k * 2 ^ (W * k) := by
  unfold siteF
  rw [sum_range_site (fun k => f k * 2 ^ (W * k)) A m B]

theorem siteSum_cast (W A m B : ℕ) (g : ℕ → ℕ → ℕ) (E : ℕ) (hW : 1 ≤ W) (hB : 1 ≤ B)
    (hE : E < 2 ^ (W * (A * (m * B)))) :
    (siteSum W A m B g E : ℤ) = siteF W A m B (fun a x b =>
      ∑ y ∈ Finset.range m, (g x y : ℤ) * (dig W E ((a * m + y) * B + b) : ℤ)) := by
  rw [siteSum_eq W A m B g E hW hB hE]
  unfold siteF
  push_cast
  rfl

theorem siteRS_cast (W A m B : ℕ) (g : ℕ → ℕ → ℕ) (hW : 1 ≤ W) (hB : 1 ≤ B) (hm : 1 ≤ m) :
    (siteRS W A m B (rowSum m g) : ℤ) = siteF W A m B (fun _ x _ => ∑ y ∈ Finset.range m, (g x y : ℤ)) := by
  rw [siteRS_eq W A m B _ hW hB hm]
  unfold siteF rowSum
  simp only [natSum_eq]
  push_cast
  rfl

theorem offset_cast (W A m B : ℕ) (hW : 1 ≤ W) :
    (offset W (W - 1) (A * (m * B)) : ℤ) = siteF W A m B (fun _ _ _ => 2 ^ (W - 1)) := by
  rw [offset_site_eq W A m B (W - 1) hW]
  unfold siteF
  push_cast
  rfl

/-! ### Soundness of the site contraction -/

theorem siteApply_spec (W A m B : ℕ) (gp gn : ℕ → ℕ → ℕ) (E : ℕ) (hW : 2 ≤ W) (hB : 1 ≤ B) (hm : 1 ≤ m)
    (hE : E < 2 ^ (W * (A * (m * B))))
    (hv : ∀ a < A, ∀ x < m, ∀ b < B, -(2 ^ (W - 1) : ℤ) ≤ siteVal W m B gp gn E a x b ∧
      siteVal W m B gp gn E a x b < 2 ^ (W - 1)) :
    siteApply W A m B gp gn E < 2 ^ (W * (A * (m * B))) ∧
      ∀ a < A, ∀ x < m, ∀ b < B,
        ent W (W - 1) (siteApply W A m B gp gn E) ((a * m + x) * B + b) = siteVal W m B gp gn E a x b := by
  have hW1 : 1 ≤ W := by omega
  have hmB : 0 < m * B := Nat.mul_pos (by omega) (by omega)
  -- the true values, indexed by slot
  let v : ℕ → ℤ := fun k => siteVal W m B gp gn E (k / (m * B)) (k / B % m) (k % B)
  have hvk : ∀ a < A, ∀ x < m, ∀ b < B, v ((a * m + x) * B + b) = siteVal W m B gp gn E a x b := by
    intro a _ x hx b hb
    show siteVal W m B gp gn E (((a * m + x) * B + b) / (m * B)) (((a * m + x) * B + b) / B % m)
      (((a * m + x) * B + b) % B) = _
    rw [site_idx_outer m B a x b hx hb, site_idx_site m B a x b hx hb, site_idx_mod m B a x b hb]
  have hvb : ∀ k < A * (m * B), -(2 ^ (W - 1) : ℤ) ≤ v k ∧ v k < 2 ^ (W - 1) := by
    intro k hk
    exact hv _ ((Nat.div_lt_iff_lt_mul hmB).mpr hk) _ (Nat.mod_lt _ (by omega)) _ (Nat.mod_lt _ (by omega))
  -- siteApply = P - Q with P - Q = Σ_k (v k + 2^(W-1)) 2^(W k)
  have key : ((siteSum W A m B gp E + offset W (W - 1) (A * (m * B)) +
        2 ^ (W - 1) * siteRS W A m B (rowSum m gn) : ℕ) : ℤ) -
      ((siteSum W A m B gn E + 2 ^ (W - 1) * siteRS W A m B (rowSum m gp) : ℕ) : ℤ) =
      ∑ k ∈ Finset.range (A * (m * B)), (v k + 2 ^ (W - 1)) * 2 ^ (W * k) := by
    push_cast
    rw [siteSum_cast W A m B gp E hW1 hB hE, siteSum_cast W A m B gn E hW1 hB hE, offset_cast W A m B hW1,
      siteRS_cast W A m B gn hW1 hB hm, siteRS_cast W A m B gp hW1 hB hm, siteF_smul, siteF_smul,
      siteF_add, siteF_add, siteF_add, siteF_sub]
    rw [show (∑ k ∈ Finset.range (A * (m * B)), (v k + 2 ^ (W - 1)) * 2 ^ (W * k)) =
      siteF W A m B (fun a x b => v ((a * m + x) * B + b) + 2 ^ (W - 1)) from
        (siteF_slots W A m B (fun k => v k + 2 ^ (W - 1))).symm]
    apply siteF_congr
    intro a ha x hx b hb
    show _ = v ((a * m + x) * B + b) + 2 ^ (W - 1)
    rw [hvk a ha x hx b hb]
    unfold siteVal ent
    have e : ∑ y ∈ Finset.range m, ((gp x y : ℤ) - gn x y) *
          ((dig W E ((a * m + y) * B + b) : ℤ) - 2 ^ (W - 1)) =
        (∑ y ∈ Finset.range m, (gp x y : ℤ) * dig W E ((a * m + y) * B + b)) -
          (∑ y ∈ Finset.range m, (gn x y : ℤ) * dig W E ((a * m + y) * B + b)) -
          2 ^ (W - 1) * (∑ y ∈ Finset.range m, (gp x y : ℤ)) +
          2 ^ (W - 1) * (∑ y ∈ Finset.range m, (gn x y : ℤ)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro y _
      ring
    rw [e]
    ring
  have hsum : ∑ k ∈ Finset.range (A * (m * B)), (v k + 2 ^ (W - 1)) * 2 ^ (W * k) =
      (∑ k ∈ Finset.range (A * (m * B)), v k * 2 ^ (W * k)) + (offset W (W - 1) (A * (m * B)) : ℤ) := by
    rw [offset, repunit_eq W _ hW1]
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hbal := balanced_sum_cast W (A * (m * B)) hW1 v hvb
  have hPQ := key.trans (hsum.trans hbal)
  have hle : siteSum W A m B gn E + 2 ^ (W - 1) * siteRS W A m B (rowSum m gp) ≤
      siteSum W A m B gp E + offset W (W - 1) (A * (m * B)) + 2 ^ (W - 1) * siteRS W A m B (rowSum m gn) := by
    have h0 : (0 : ℤ) ≤ ((siteSum W A m B gp E + offset W (W - 1) (A * (m * B)) +
          2 ^ (W - 1) * siteRS W A m B (rowSum m gn) : ℕ) : ℤ) -
        ((siteSum W A m B gn E + 2 ^ (W - 1) * siteRS W A m B (rowSum m gp) : ℕ) : ℤ) := by
      rw [hPQ]
      positivity
    have h1 := sub_nonneg.mp h0
    exact_mod_cast h1
  have happ : siteApply W A m B gp gn E = ∑ k ∈ Finset.range (A * (m * B)),
      (if k < A * (m * B) then (v k + 2 ^ (W - 1)).toNat else 0) * (2 ^ W) ^ k := by
    have h1 : ((siteApply W A m B gp gn E : ℕ) : ℤ) = ((∑ k ∈ Finset.range (A * (m * B)),
        (if k < A * (m * B) then (v k + 2 ^ (W - 1)).toNat else 0) * (2 ^ W) ^ k : ℕ) : ℤ) := by
      unfold siteApply
      rw [Nat.cast_sub hle]
      exact hPQ
    exact_mod_cast h1
  have hf : ∀ s, (if s < A * (m * B) then (v s + 2 ^ (W - 1)).toNat else 0) < 2 ^ W := by
    intro s
    split_ifs with hs
    · exact (toNat_digit_lt W hW1 (v s) (hvb s hs)).1
    · exact Nat.two_pow_pos W
  constructor
  · rw [happ, pow_mul]
    exact sum_digits_lt (2 ^ W) _ hf _
  · intro a ha x hx b hb
    have hk := site_idx_lt A m B a x b ha hx hb
    rw [← hvk a ha x hx b hb, happ]
    unfold ent dig
    rw [pow_mul, sum_digit (2 ^ W) (A * (m * B)) _ (Nat.two_pow_pos W) hf _ hk, if_pos hk,
      (toNat_digit_lt W hW1 _ (hvb _ hk)).2]
    ring

end X2
end ThreeCopyQutritWerner
