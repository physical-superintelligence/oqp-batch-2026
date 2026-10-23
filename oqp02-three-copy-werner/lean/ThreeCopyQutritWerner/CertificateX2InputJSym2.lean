module

public import ThreeCopyQutritWerner.CertificateX2InputJSym

@[expose] public section


/-!
# Input stage: stabilizer invariance of the input blocks of degree-2 keys

A degree-2 key has three equal types; its input block is `V N Vᵀ + (1/3) W N Wᵀ` with `V = GJ` and
`W = x2Partner V`. For the certificate's 11 degree-2 images (checked by the kernel, `x2JColOK2`):
`J` is symmetric under the swap of sites 0, 1 and its three cyclic rotations sum to zero. Then
`V` has the same laws (`x2GJ_swap01`, `x2GJ_cyc`), and under the swap of sites 0, 1
`(V, W) ↦ (V, -W)`, under the swap of sites 1, 2 `(V, W) ↦ ((W - V)/2, (3V + W)/2)`; both keep
`V N Vᵀ + (1/3) W N Wᵀ` for every `N`. With `x2Lookup_stab_of_swaps`: invariance under all six site
permutations (`x2InputBlock_inv_deg2_of_ok`).
-/

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner
namespace X2

/-! ### Kernel check: the cyclic rotations of a cube column sum to zero -/

/-- `d(x,y,z) + d(y,z,x) + d(z,x,y) = 3 · 2^10` for all `x, y, z < m` (digits of an `m × m × m` column). -/
def jcyc (col m : ℕ) : Bool :=
  (List.range m).all fun x => (List.range m).all fun y => (List.range m).all fun z =>
    dig 11 (runOf 11 (m * m) (x * (m * m)) col) (y * m + z) +
      dig 11 (runOf 11 (m * m) (y * (m * m)) col) (z * m + x) +
      dig 11 (runOf 11 (m * m) (z * (m * m)) col) (x * m + y) == 3072

theorem jcyc_sound (col m : ℕ) (h : jcyc col m = true) (x y z : ℕ) (hx : x < m) (hy : y < m) (hz : z < m) :
    dig 11 col ((x * m + y) * m + z) + dig 11 col ((y * m + z) * m + x) +
      dig 11 col ((z * m + x) * m + y) = 3072 := by
  unfold jcyc at h
  have h1 := List.all_eq_true.mp h x (List.mem_range.mpr hx)
  have h2 := List.all_eq_true.mp h1 y (List.mem_range.mpr hy)
  have h3 := List.all_eq_true.mp h2 z (List.mem_range.mpr hz)
  have he := beq_iff_eq.mp h3
  rw [dig_slab2 col m m x y z hy hz, dig_slab2 col m m y z x hz hx, dig_slab2 col m m z x y hx hy] at he
  exact he

theorem ent_cyc_of_dig (col i j l : ℕ) (h : dig 11 col i + dig 11 col j + dig 11 col l = 3072) :
    ent 11 10 col i + ent 11 10 col j + ent 11 10 col l = 0 := by
  unfold ent
  have h' : ((dig 11 col i : ℕ) : ℤ) + ((dig 11 col j : ℕ) : ℤ) + ((dig 11 col l : ℕ) : ℤ) = 3072 := by
    exact_mod_cast h
  have h2 : (2 : ℤ) ^ 10 = 1024 := by norm_num
  rw [h2]
  linarith

/-- Checks on column `c` of a degree-2 key: symmetric under the swap of sites 0, 1, cyclic sum zero. -/
noncomputable def x2JColOK2 (s : Fin 3) (k : x2Key s) (c : ℕ) : Bool :=
  jsw01S (x2JCols (x2KeyGlobal s k) c) (x2KeyMult s k 0) (x2KeyMult s k 2) &&
    jcyc (x2JCols (x2KeyGlobal s k) c) (x2KeyMult s k 0)

noncomputable def x2JKeyOK2 (s : Fin 3) (k : x2Key s) : Bool :=
  (List.range (x2KeySize s k)).all (x2JColOK2 s k)

noncomputable def x2JColRangeOK2 (s : Fin 3) (k : x2Key s) (c0 n : ℕ) : Bool :=
  (List.range' c0 n).all (x2JColOK2 s k)

theorem x2JColRangeOK2_mem (s : Fin 3) (k : x2Key s) (c0 n c : ℕ) (h : x2JColRangeOK2 s k c0 n = true)
    (h1 : c0 ≤ c) (h2 : c < c0 + n) : x2JColOK2 s k c = true :=
  List.all_eq_true.mp h c (List.mem_range'_1.mpr ⟨h1, h2⟩)

theorem x2JKeyOK2_of_cols (s : Fin 3) (k : x2Key s)
    (h : ∀ c, c < x2KeySize s k → x2JColOK2 s k c = true) : x2JKeyOK2 s k = true :=
  List.all_eq_true.mpr (fun c hc => h c (List.mem_range.mp hc))

/-! ### Laws of the image, of `V = GJ` and of `W = x2Partner V` -/

section deg2

variable (s : Fin 3) (k : x2Key s) (h01 : x2KeyTypes s k 0 = x2KeyTypes s k 1)
  (h12 : x2KeyTypes s k 1 = x2KeyTypes s k 2)

include h01 in
theorem x2KeyMult_eq01 : x2KeyMult s k 0 = x2KeyMult s k 1 := by
  show x2Mult s (x2KeyTypes s k 0) = x2Mult s (x2KeyTypes s k 1)
  rw [h01]

include h12 in
theorem x2KeyMult_eq12 : x2KeyMult s k 1 = x2KeyMult s k 2 := by
  show x2Mult s (x2KeyTypes s k 1) = x2Mult s (x2KeyTypes s k 2)
  rw [h12]

include h01 h12 in
/-- The kernel check gives the cyclic law of the concrete image. -/
theorem x2Image_cyc (hcols : ∀ c, c < x2KeySize s k → x2JColOK2 s k c = true) (y0 y1 y2 : ℕ)
    (d : x2Col s k) :
    x2Get3 ((x2DataConcrete.image s k).map (Int.cast : ℤ → ℚ)) y0 y1 y2 d +
      x2Get3 ((x2DataConcrete.image s k).map (Int.cast : ℤ → ℚ)) y1 y2 y0 d +
      x2Get3 ((x2DataConcrete.image s k).map (Int.cast : ℤ → ℚ)) y2 y0 y1 d = 0 := by
  have e1 := x2KeyMult_eq01 s k h01
  have e2 := x2KeyMult_eq12 s k h12
  rw [x2Get3_image_concrete, x2Get3_image_concrete, x2Get3_image_concrete, ← e2, ← e1]
  by_cases hy : y0 < x2KeyMult s k 0 ∧ y1 < x2KeyMult s k 0 ∧ y2 < x2KeyMult s k 0
  · rw [if_pos hy, if_pos ⟨hy.2.1, hy.2.2, hy.1⟩, if_pos ⟨hy.2.2, hy.1, hy.2.1⟩]
    have hc := hcols d d.isLt
    unfold x2JColOK2 at hc
    rw [Bool.and_eq_true] at hc
    rw [← e2, ← e1] at hc
    have h3 := ent_cyc_of_dig _ _ _ _ (jcyc_sound _ _ hc.2 y0 y1 y2 hy.1 hy.2.1 hy.2.2)
    exact_mod_cast h3
  · rw [if_neg hy, if_neg (fun h' => hy ⟨h'.2.2, h'.1, h'.2.1⟩),
      if_neg (fun h' => hy ⟨h'.2.1, h'.2.2, h'.1⟩), add_zero, add_zero]

include h01 in
/-- The kernel check gives the symmetry of the concrete image under the swap of sites 0, 1. -/
theorem x2Image_swap01_deg2 (hcols : ∀ c, c < x2KeySize s k → x2JColOK2 s k c = true)
    (y0 y1 y2 : ℕ) (d : x2Col s k) :
    x2Get3 ((x2DataConcrete.image s k).map (Int.cast : ℤ → ℚ)) y1 y0 y2 d =
      ((1 : ℤ) : ℚ) * x2Get3 ((x2DataConcrete.image s k).map (Int.cast : ℤ → ℚ)) y0 y1 y2 d := by
  refine x2Image_swap01 s k 1 (x2KeyMult_eq01 s k h01) ?_ y0 y1 y2 d
  intro y0 y1 y2 c h0 h1 h2 hc
  have hc' := hcols c hc
  unfold x2JColOK2 at hc'
  rw [Bool.and_eq_true] at hc'
  exact ent_eq_of_dig_eq _ _ _ (jsw01S_sound _ _ _ hc'.1 y0 y1 y2 h0 h1 h2)

end deg2

/-- Rotating the three summation indices of a cube sum. -/
theorem sum3_rot (n : ℕ) (f : ℕ → ℕ → ℕ → ℚ) :
    ∑ x ∈ Finset.range n, ∑ y ∈ Finset.range n, ∑ z ∈ Finset.range n, f y z x =
      ∑ x ∈ Finset.range n, ∑ y ∈ Finset.range n, ∑ z ∈ Finset.range n, f x y z := by
  calc ∑ x ∈ Finset.range n, ∑ y ∈ Finset.range n, ∑ z ∈ Finset.range n, f y z x
      = ∑ y ∈ Finset.range n, ∑ x ∈ Finset.range n, ∑ z ∈ Finset.range n, f y z x := Finset.sum_comm
    _ = ∑ y ∈ Finset.range n, ∑ z ∈ Finset.range n, ∑ x ∈ Finset.range n, f y z x :=
        Finset.sum_congr rfl (fun y _ => Finset.sum_comm)

/-- The cyclic law passes through `G ⊗ G ⊗ G` (equal metrics at the three sites). -/
theorem sum3_cyc (n : ℕ) (g : ℕ → ℕ → ℤ) (Jf : ℕ → ℕ → ℕ → ℚ)
    (hJ : ∀ y0 y1 y2, Jf y0 y1 y2 + Jf y1 y2 y0 + Jf y2 y0 y1 = 0) (a0 a1 a2 : ℕ) :
    (∑ y0 ∈ Finset.range n, ∑ y1 ∈ Finset.range n, ∑ y2 ∈ Finset.range n,
        ((g a0 y0 * (g a1 y1 * g a2 y2) : ℤ) : ℚ) * Jf y0 y1 y2) +
      (∑ y0 ∈ Finset.range n, ∑ y1 ∈ Finset.range n, ∑ y2 ∈ Finset.range n,
        ((g a1 y0 * (g a2 y1 * g a0 y2) : ℤ) : ℚ) * Jf y0 y1 y2) +
      (∑ y0 ∈ Finset.range n, ∑ y1 ∈ Finset.range n, ∑ y2 ∈ Finset.range n,
        ((g a2 y0 * (g a0 y1 * g a1 y2) : ℤ) : ℚ) * Jf y0 y1 y2) = 0 := by
  have e2 : (∑ y0 ∈ Finset.range n, ∑ y1 ∈ Finset.range n, ∑ y2 ∈ Finset.range n,
        ((g a1 y0 * (g a2 y1 * g a0 y2) : ℤ) : ℚ) * Jf y0 y1 y2) =
      ∑ x ∈ Finset.range n, ∑ y ∈ Finset.range n, ∑ z ∈ Finset.range n,
        ((g a1 y * (g a2 z * g a0 x) : ℤ) : ℚ) * Jf y z x :=
    (sum3_rot n (fun x y z => ((g a1 x * (g a2 y * g a0 z) : ℤ) : ℚ) * Jf x y z)).symm
  have e3 : (∑ y0 ∈ Finset.range n, ∑ y1 ∈ Finset.range n, ∑ y2 ∈ Finset.range n,
        ((g a2 y0 * (g a0 y1 * g a1 y2) : ℤ) : ℚ) * Jf y0 y1 y2) =
      ∑ x ∈ Finset.range n, ∑ y ∈ Finset.range n, ∑ z ∈ Finset.range n,
        ((g a2 z * (g a0 x * g a1 y) : ℤ) : ℚ) * Jf z x y :=
    sum3_rot n (fun x y z => ((g a2 z * (g a0 x * g a1 y) : ℤ) : ℚ) * Jf z x y)
  rw [e2, e3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro x _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro y _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro z _
  have h := hJ x y z
  push_cast
  linear_combination ((g a0 x : ℚ) * ((g a1 y : ℚ) * (g a2 z : ℚ))) * h

/-- `GJ` of a key with three equal types, as a cube sum with one metric. -/
theorem x2GJ_get3_eq (D : X2Data) (s : Fin 3) (k : x2Key s) (h01 : x2KeyTypes s k 0 = x2KeyTypes s k 1)
    (h12 : x2KeyTypes s k 1 = x2KeyTypes s k 2) (a0 a1 a2 : ℕ) (d : x2Col s k) :
    x2Get3 (x2GJ D s k) a0 a1 a2 d =
      ∑ y0 ∈ Finset.range (x2KeyMult s k 0), ∑ y1 ∈ Finset.range (x2KeyMult s k 0),
        ∑ y2 ∈ Finset.range (x2KeyMult s k 0),
          ((x2gl s (x2KeyTypes s k 0) a0 y0 * (x2gl s (x2KeyTypes s k 0) a1 y1 *
              x2gl s (x2KeyTypes s k 0) a2 y2) : ℤ) : ℚ) *
            (fun y0 y1 y2 => x2Get3 ((D.image s k).map (Int.cast : ℤ → ℚ)) y0 y1 y2 d) y0 y1 y2 := by
  have e1 := x2KeyMult_eq01 s k h01
  have e2 := x2KeyMult_eq12 s k h12
  have g1 : ∀ i j : ℕ, x2gl s (x2KeyTypes s k 1) i j = x2gl s (x2KeyTypes s k 0) i j := by
    intro i j
    rw [h01]
  have g2 : ∀ i j : ℕ, x2gl s (x2KeyTypes s k 2) i j = x2gl s (x2KeyTypes s k 0) i j := by
    intro i j
    rw [← h12, h01]
  rw [x2GJ_get3]
  refine Finset.sum_congr rfl (fun y0 _ => ?_)
  refine Finset.sum_congr (by rw [e1]) (fun y1 _ => ?_)
  refine Finset.sum_congr (by rw [← e2, e1]) (fun y2 _ => ?_)
  rw [g1 a1 y1, g2 a2 y2]

theorem x2GJ_cyc (D : X2Data) (s : Fin 3) (k : x2Key s) (h01 : x2KeyTypes s k 0 = x2KeyTypes s k 1)
    (h12 : x2KeyTypes s k 1 = x2KeyTypes s k 2)
    (hJ : ∀ (y0 y1 y2 : ℕ) (d : x2Col s k),
      x2Get3 ((D.image s k).map (Int.cast : ℤ → ℚ)) y0 y1 y2 d +
        x2Get3 ((D.image s k).map (Int.cast : ℤ → ℚ)) y1 y2 y0 d +
        x2Get3 ((D.image s k).map (Int.cast : ℤ → ℚ)) y2 y0 y1 d = 0)
    (a0 a1 a2 : ℕ) (d : x2Col s k) :
    x2Get3 (x2GJ D s k) a0 a1 a2 d + x2Get3 (x2GJ D s k) a1 a2 a0 d + x2Get3 (x2GJ D s k) a2 a0 a1 d = 0 := by
  rw [x2GJ_get3_eq D s k h01 h12, x2GJ_get3_eq D s k h01 h12, x2GJ_get3_eq D s k h01 h12]
  exact sum3_cyc (x2KeyMult s k 0) (x2gl s (x2KeyTypes s k 0))
    (fun y0 y1 y2 => x2Get3 ((D.image s k).map (Int.cast : ℤ → ℚ)) y0 y1 y2 d)
    (fun y0 y1 y2 => hJ y0 y1 y2 d) a0 a1 a2

/-- The partner of a cube matrix at natural coordinates. -/
theorem x2Get3_partner {p q r : ℕ} {ι : Type*} (V : Matrix (Fin p × Fin q × Fin r) ι ℚ) (hpq : p = q)
    (hqr : q = r) (a0 a1 a2 : ℕ) (c : ι) :
    x2Get3 (x2Partner V) a0 a1 a2 c = x2Get3 V a2 a0 a1 c - x2Get3 V a1 a2 a0 c := by
  by_cases h : a0 < p ∧ a1 < q ∧ a2 < r
  · show (if h : a0 < p ∧ a1 < q ∧ a2 < r then x2Partner V (⟨a0, h.1⟩, ⟨a1, h.2.1⟩, ⟨a2, h.2.2⟩) c else 0) = _
    rw [dif_pos h]
    rfl
  · have h1 : ¬ (a2 < p ∧ a0 < q ∧ a1 < r) := by
      intro h'
      apply h
      subst hpq
      subst hqr
      omega
    have h2 : ¬ (a1 < p ∧ a2 < q ∧ a0 < r) := by
      intro h'
      apply h
      subst hpq
      subst hqr
      omega
    unfold x2Get3
    rw [dif_neg h, dif_neg h1, dif_neg h2, sub_zero]

/-! ### Invariance of `V N Vᵀ + (1/3) W N Wᵀ` -/

theorem x2Lookup_add_smul {p q r : ℕ} (A B : Matrix (Fin p × Fin q × Fin r) (Fin p × Fin q × Fin r) ℚ)
    (t : ℚ) (a b : Fin 3 → ℕ) : x2Lookup (A + t • B) a b = x2Lookup A a b + t * x2Lookup B a b := by
  unfold x2Lookup
  split_ifs
  · rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  · ring

/-- Lookup of the degree-2 block form through the lookups of `V` and `W`. -/
theorem x2Lookup_pair {p q r : ℕ} {κ : Type*} [Fintype κ] (V W : Matrix (Fin p × Fin q × Fin r) κ ℚ)
    (M : Matrix κ κ ℚ) (a b : Fin 3 → ℕ) :
    x2Lookup (V * M * Vᵀ + (1 / 3 : ℚ) • (W * M * Wᵀ)) a b =
      ∑ c, ∑ c', (x2Get3 V (a 0) (a 1) (a 2) c * M c c' * x2Get3 V (b 0) (b 1) (b 2) c' +
        (1 / 3 : ℚ) * (x2Get3 W (a 0) (a 1) (a 2) c * M c c' * x2Get3 W (b 0) (b 1) (b 2) c')) := by
  rw [x2Lookup_add_smul, x2Lookup_conj, x2Lookup_conj, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]

/-- If under `π` the pair `(V, W)` transforms by `(V, W) ↦ (αV + βW, γV + δW)` with
`α² + γ²/3 = 1`, `αβ + γδ/3 = 0`, `β² + δ²/3 = 1/3`, the degree-2 block form is invariant. -/
theorem x2Lookup_pair_inv {p q r : ℕ} {κ : Type*} [Fintype κ] (V W : Matrix (Fin p × Fin q × Fin r) κ ℚ)
    (M : Matrix κ κ ℚ) (π : Fin 3 → Fin 3) (α β γ δ : ℚ) (h1 : α * α + γ * γ / 3 = 1)
    (h2 : α * β + γ * δ / 3 = 0) (h3 : β * β + δ * δ / 3 = 1 / 3)
    (hV : ∀ (a : Fin 3 → ℕ) (c : κ), x2Get3 V (a (π 0)) (a (π 1)) (a (π 2)) c =
      α * x2Get3 V (a 0) (a 1) (a 2) c + β * x2Get3 W (a 0) (a 1) (a 2) c)
    (hW : ∀ (a : Fin 3 → ℕ) (c : κ), x2Get3 W (a (π 0)) (a (π 1)) (a (π 2)) c =
      γ * x2Get3 V (a 0) (a 1) (a 2) c + δ * x2Get3 W (a 0) (a 1) (a 2) c)
    (a b : Fin 3 → ℕ) :
    x2Lookup (V * M * Vᵀ + (1 / 3 : ℚ) • (W * M * Wᵀ)) (a ∘ π) (b ∘ π) =
      x2Lookup (V * M * Vᵀ + (1 / 3 : ℚ) • (W * M * Wᵀ)) a b := by
  rw [x2Lookup_pair, x2Lookup_pair]
  simp only [Function.comp_apply, hV, hW]
  refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun c' _ => ?_))
  linear_combination
    (x2Get3 V (a 0) (a 1) (a 2) c * M c c' * x2Get3 V (b 0) (b 1) (b 2) c') * h1 +
    (x2Get3 V (a 0) (a 1) (a 2) c * M c c' * x2Get3 W (b 0) (b 1) (b 2) c' +
      x2Get3 W (a 0) (a 1) (a 2) c * M c c' * x2Get3 V (b 0) (b 1) (b 2) c') * h2 +
    (x2Get3 W (a 0) (a 1) (a 2) c * M c c' * x2Get3 W (b 0) (b 1) (b 2) c') * h3

/-! ### Degree-2 keys -/

theorem x2InputBlock_deg2 (D : X2Data) (s : Fin 3) (N : X2Blocks s) (k : x2Key s) (hdeg : x2KeyDegree s k = 2) :
    x2InputBlock D s N k = x2GJ D s k * N k * (x2GJ D s k)ᵀ +
      (1 / 3 : ℚ) • (x2Partner (x2GJ D s k) * N k * (x2Partner (x2GJ D s k))ᵀ) := by
  unfold x2InputBlock x2GJ
  simp only [if_pos hdeg]

/-- For a degree-2 key (three equal types) whose columns pass `x2JColOK2`, the input block is
invariant under all six site permutations, for every source `N`. -/
theorem x2InputBlock_inv_deg2_of_ok (s : Fin 3) (N : X2Blocks s) (k : x2Key s) (hok : x2JKeyOK2 s k = true)
    (hdeg : x2KeyDegree s k = 2) (h01 : x2KeyTypes s k 0 = x2KeyTypes s k 1)
    (h12 : x2KeyTypes s k 1 = x2KeyTypes s k 2) (p : Fin 6)
    (hp : x2KeyTypes s k ∘ x2Perm3 p = x2KeyTypes s k) (a b : Fin 3 → ℕ) :
    x2Lookup (x2InputBlock x2DataConcrete s N k) (a ∘ x2Perm3 p) (b ∘ x2Perm3 p) =
      x2Lookup (x2InputBlock x2DataConcrete s N k) a b := by
  have hcols : ∀ c, c < x2KeySize s k → x2JColOK2 s k c = true :=
    fun c hc => List.all_eq_true.mp hok c (List.mem_range.mpr hc)
  have hsort : x2Sorted (x2KeyTypes s k) := by
    unfold x2Sorted
    exact ⟨le_of_eq h01, le_of_eq h12⟩
  have e1 := x2KeyMult_eq01 s k h01
  have e2 := x2KeyMult_eq12 s k h12
  -- laws of V = GJ
  have V01 : ∀ (a0 a1 a2 : ℕ) (c : x2Col s k), x2Get3 (x2GJ x2DataConcrete s k) a1 a0 a2 c =
      x2Get3 (x2GJ x2DataConcrete s k) a0 a1 a2 c := by
    intro a0 a1 a2 c
    have := x2GJ_swap01 x2DataConcrete s k ((1 : ℤ) : ℚ) h01 (x2Image_swap01_deg2 s k h01 hcols) a0 a1 a2 c
    rw [this, Int.cast_one, one_mul]
  have Vcyc : ∀ (a0 a1 a2 : ℕ) (c : x2Col s k), x2Get3 (x2GJ x2DataConcrete s k) a0 a1 a2 c +
      x2Get3 (x2GJ x2DataConcrete s k) a1 a2 a0 c + x2Get3 (x2GJ x2DataConcrete s k) a2 a0 a1 c = 0 :=
    x2GJ_cyc x2DataConcrete s k h01 h12 (x2Image_cyc s k h01 h12 hcols)
  have Wdef : ∀ (a0 a1 a2 : ℕ) (c : x2Col s k), x2Get3 (x2Partner (x2GJ x2DataConcrete s k)) a0 a1 a2 c =
      x2Get3 (x2GJ x2DataConcrete s k) a2 a0 a1 c - x2Get3 (x2GJ x2DataConcrete s k) a1 a2 a0 c :=
    x2Get3_partner _ e1 e2
  rw [x2InputBlock_deg2 x2DataConcrete s N k hdeg]
  refine x2Lookup_stab_of_swaps _ (x2KeyTypes s k) hsort ?_ ?_ p hp a b
  · intro _ a b
    refine x2Lookup_pair_inv _ _ _ (x2Perm3 2) 1 0 0 (-1) (by norm_num) (by norm_num) (by norm_num) ?_ ?_ a b
    · intro a' c
      show x2Get3 (x2GJ x2DataConcrete s k) (a' 1) (a' 0) (a' 2) c =
        1 * x2Get3 (x2GJ x2DataConcrete s k) (a' 0) (a' 1) (a' 2) c +
          0 * x2Get3 (x2Partner (x2GJ x2DataConcrete s k)) (a' 0) (a' 1) (a' 2) c
      rw [V01]
      ring
    · intro a' c
      show x2Get3 (x2Partner (x2GJ x2DataConcrete s k)) (a' 1) (a' 0) (a' 2) c =
        0 * x2Get3 (x2GJ x2DataConcrete s k) (a' 0) (a' 1) (a' 2) c +
          -1 * x2Get3 (x2Partner (x2GJ x2DataConcrete s k)) (a' 0) (a' 1) (a' 2) c
      rw [Wdef, Wdef, V01 (a' 1) (a' 2) (a' 0), V01 (a' 2) (a' 0) (a' 1)]
      ring
  · intro _ a b
    refine x2Lookup_pair_inv _ _ _ (x2Perm3 1) (-1 / 2) (1 / 2) (3 / 2) (1 / 2) (by norm_num) (by norm_num)
      (by norm_num) ?_ ?_ a b
    · intro a' c
      show x2Get3 (x2GJ x2DataConcrete s k) (a' 0) (a' 2) (a' 1) c =
        (-1 / 2) * x2Get3 (x2GJ x2DataConcrete s k) (a' 0) (a' 1) (a' 2) c +
          (1 / 2) * x2Get3 (x2Partner (x2GJ x2DataConcrete s k)) (a' 0) (a' 1) (a' 2) c
      rw [Wdef, V01 (a' 2) (a' 0) (a' 1)]
      have hc := Vcyc (a' 0) (a' 1) (a' 2) c
      linarith
    · intro a' c
      show x2Get3 (x2Partner (x2GJ x2DataConcrete s k)) (a' 0) (a' 2) (a' 1) c =
        (3 / 2) * x2Get3 (x2GJ x2DataConcrete s k) (a' 0) (a' 1) (a' 2) c +
          (1 / 2) * x2Get3 (x2Partner (x2GJ x2DataConcrete s k)) (a' 0) (a' 1) (a' 2) c
      rw [Wdef, Wdef, V01 (a' 0) (a' 1) (a' 2), V01 (a' 1) (a' 2) (a' 0)]
      have hc := Vcyc (a' 0) (a' 1) (a' 2) c
      linarith

end X2
end ThreeCopyQutritWerner
