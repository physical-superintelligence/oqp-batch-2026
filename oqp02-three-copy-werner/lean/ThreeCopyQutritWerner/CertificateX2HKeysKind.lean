module

public import ThreeCopyQutritWerner.CertificateX2Data
public import ThreeCopyQutritWerner.CertificateX2BridgeImages
public import ThreeCopyQutritWerner.CertificateX2SitesCore
public import ThreeCopyQutritWerner.CertificateDescendantSourceSizes
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section


/-!
# Kind projectors and the standard swap fix the h images

Frame-coordinate mirrors of the bridge's `x2FrameCoords`, `x2SlotPermFrame`, `x2KindProjFrame`
(CertificateX2BridgeKeyFacts; same bodies, with `certificateDescendantFrames2SourceSize` for
`certificatePhysicalFrameSystem0.size`), and the image of an h key in frame coordinates for the
concrete data (`x2hImage b i c = J_b[i, c]`, a frame index being the row-major ambient index).

`x2h_slotPerm_mul`: a slot permutation permutes the rows. `x2hKindFix`, `x2hStdSwap`: the two
per-key facts, from one kernel check over all 122 h keys (`x2hKindCheck`).
-/

set_option maxRecDepth 100000

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner.X2Sites

open X2

/-- Sizes of the h frame types. -/
abbrev hsz (t : Fin 7) : ℕ := certificateDescendantFrames2SourceSize t

/-- Frame index type of an h type triple. -/
abbrev HIdx (τ : Fin 7 × Fin 7 × Fin 7) := Fin (hsz τ.1 * (hsz τ.2.1 * hsz τ.2.2))

/-- Natural coordinates of a frame index (mirror of `x2FrameCoords`). -/
def x2hCoords (τ : Fin 7 × Fin 7 × Fin 7) (i : HIdx τ) : Fin 3 → ℕ :=
  ![((finProdFinEquiv.symm i).1 : ℕ), ((finProdFinEquiv.symm (finProdFinEquiv.symm i).2).1 : ℕ),
    ((finProdFinEquiv.symm (finProdFinEquiv.symm i).2).2 : ℕ)]

/-- Slot permutation in frame coordinates (mirror of `x2SlotPermFrame`). -/
noncomputable def x2hSlotPerm (τ : Fin 7 × Fin 7 × Fin 7) (p : Fin 6) : Matrix (HIdx τ) (HIdx τ) ℂ :=
  Matrix.of fun i j => if x2hCoords τ j = x2hCoords τ i ∘ x2Perm3 p then 1 else 0

/-- Kind projector in frame coordinates (mirror of `x2KindProjFrame`). -/
noncomputable def x2hKindProj (τ : Fin 7 × Fin 7 × Fin 7) (kind : ℕ) : Matrix (HIdx τ) (HIdx τ) ℂ :=
  let avg := (1 / 6 : ℂ) • ∑ p, x2hSlotPerm τ p
  let alt := (1 / 6 : ℂ) • ∑ p, ((x2Perm3Sign p : ℚ) : ℂ) • x2hSlotPerm τ p
  if τ.1 = τ.2.1 ∧ τ.2.1 = τ.2.2 then
    (if kind = 0 then avg else if kind = 1 then alt else 1 - avg - alt)
  else if τ.1 = τ.2.1 then
    (1 / 2 : ℂ) • (1 + (if kind = 0 then (1 : ℂ) else -1) • x2hSlotPerm τ x2Swap01Idx)
  else if τ.2.1 = τ.2.2 then
    (1 / 2 : ℂ) • (1 + (if kind = 0 then (1 : ℂ) else -1) • x2hSlotPerm τ x2Swap12Idx)
  else 1

/-! ## Coordinates of frame indices -/

theorem x2hCoords_apply (τ : Fin 7 × Fin 7 × Fin 7) (i : HIdx τ) :
    x2hCoords τ i = ![(i : ℕ) / (hsz τ.2.1 * hsz τ.2.2), (i : ℕ) % (hsz τ.2.1 * hsz τ.2.2) / hsz τ.2.2,
      (i : ℕ) % (hsz τ.2.1 * hsz τ.2.2) % hsz τ.2.2] := by
  unfold x2hCoords
  simp only [finProdFinEquiv_symm_apply, Fin.coe_divNat, Fin.coe_modNat]

/-- Frame index of natural coordinates. -/
def hidxN (τ : Fin 7 × Fin 7 × Fin 7) (v : Fin 3 → ℕ) : ℕ :=
  v 0 * (hsz τ.2.1 * hsz τ.2.2) + (v 1 * hsz τ.2.2 + v 2)

theorem hidxN_lt (τ : Fin 7 × Fin 7 × Fin 7) (v : Fin 3 → ℕ) (h0 : v 0 < hsz τ.1)
    (h1 : v 1 < hsz τ.2.1) (h2 : v 2 < hsz τ.2.2) :
    hidxN τ v < hsz τ.1 * (hsz τ.2.1 * hsz τ.2.2) := by
  unfold hidxN
  have hb : v 1 * hsz τ.2.2 + v 2 < hsz τ.2.1 * hsz τ.2.2 := by
    calc v 1 * hsz τ.2.2 + v 2 < v 1 * hsz τ.2.2 + hsz τ.2.2 := by omega
      _ = (v 1 + 1) * hsz τ.2.2 := by ring
      _ ≤ hsz τ.2.1 * hsz τ.2.2 := Nat.mul_le_mul_right _ h1
  calc v 0 * (hsz τ.2.1 * hsz τ.2.2) + (v 1 * hsz τ.2.2 + v 2)
      < v 0 * (hsz τ.2.1 * hsz τ.2.2) + hsz τ.2.1 * hsz τ.2.2 := by omega
    _ = (v 0 + 1) * (hsz τ.2.1 * hsz τ.2.2) := by ring
    _ ≤ hsz τ.1 * (hsz τ.2.1 * hsz τ.2.2) := Nat.mul_le_mul_right _ h0

theorem x2hCoords_hidx (τ : Fin 7 × Fin 7 × Fin 7) (v : Fin 3 → ℕ) (h0 : v 0 < hsz τ.1)
    (h1 : v 1 < hsz τ.2.1) (h2 : v 2 < hsz τ.2.2) :
    x2hCoords τ ⟨hidxN τ v, hidxN_lt τ v h0 h1 h2⟩ = v := by
  rw [x2hCoords_apply]
  have hb : v 1 * hsz τ.2.2 + v 2 < hsz τ.2.1 * hsz τ.2.2 := by
    calc v 1 * hsz τ.2.2 + v 2 < v 1 * hsz τ.2.2 + hsz τ.2.2 := by omega
      _ = (v 1 + 1) * hsz τ.2.2 := by ring
      _ ≤ hsz τ.2.1 * hsz τ.2.2 := Nat.mul_le_mul_right _ h1
  have hpos : 0 < hsz τ.2.1 * hsz τ.2.2 := lt_of_le_of_lt (Nat.zero_le _) hb
  have hpos2 : 0 < hsz τ.2.2 := lt_of_le_of_lt (Nat.zero_le _) h2
  have e1 : hidxN τ v / (hsz τ.2.1 * hsz τ.2.2) = v 0 := by
    unfold hidxN
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hb, Nat.zero_add]
  have e2 : hidxN τ v % (hsz τ.2.1 * hsz τ.2.2) = v 1 * hsz τ.2.2 + v 2 := by
    unfold hidxN
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
  have e3 : (v 1 * hsz τ.2.2 + v 2) / hsz τ.2.2 = v 1 := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos2, Nat.div_eq_of_lt h2, Nat.zero_add]
  have e4 : (v 1 * hsz τ.2.2 + v 2) % hsz τ.2.2 = v 2 := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h2]
  funext k
  fin_cases k <;> simp [e1, e2, e3, e4]

theorem x2hCoords_injective (τ : Fin 7 × Fin 7 × Fin 7) : Function.Injective (x2hCoords τ) := by
  intro i j h
  have h0 := congrFun h 0
  have h12 := congrFun h 1
  have h22 := congrFun h 2
  unfold x2hCoords at h0 h12 h22
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at h0 h12 h22
  have hs : (finProdFinEquiv.symm i).2 = (finProdFinEquiv.symm j).2 := by
    apply finProdFinEquiv.symm.injective
    exact Prod.ext (Fin.ext h12) (Fin.ext h22)
  apply finProdFinEquiv.symm.injective
  exact Prod.ext (Fin.ext h0) hs

/-- A slot permutation moves rows: row `i` of `P M` is row `hidx (coords i ∘ p)` of `M`. -/
theorem x2h_slotPerm_mul {κ : Type*} (τ : Fin 7 × Fin 7 × Fin 7) (p : Fin 6) (M : Matrix (HIdx τ) κ ℂ)
    (i : HIdx τ) (c : κ) (h0 : (x2hCoords τ i ∘ x2Perm3 p) 0 < hsz τ.1)
    (h1 : (x2hCoords τ i ∘ x2Perm3 p) 1 < hsz τ.2.1) (h2 : (x2hCoords τ i ∘ x2Perm3 p) 2 < hsz τ.2.2) :
    (x2hSlotPerm τ p * M) i c =
      M ⟨hidxN τ (x2hCoords τ i ∘ x2Perm3 p), hidxN_lt τ _ h0 h1 h2⟩ c := by
  rw [Matrix.mul_apply]
  simp only [x2hSlotPerm, Matrix.of_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single ⟨hidxN τ (x2hCoords τ i ∘ x2Perm3 p), hidxN_lt τ _ h0 h1 h2⟩]
  · rw [if_pos (x2hCoords_hidx τ _ h0 h1 h2)]
  · intro j _ hj
    rw [if_neg]
    intro hc
    apply hj
    apply x2hCoords_injective τ
    rw [hc, x2hCoords_hidx τ _ h0 h1 h2]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ## Two-level slot reads -/

/-- A slot of width `W` inside a slab of `a` slots is the slot `a k + j` of the whole number. -/
theorem ext_ext (T W a k j : ℕ) (hj : j < a) : ext (ext T (W * a) k) W j = ext T W (a * k + j) := by
  have hsplit : W * a = W * j + W * (a - j) := by
    rw [← Nat.mul_add]
    congr 1
    omega
  have hdvd : 2 ^ W ∣ 2 ^ (W * (a - j)) := by
    apply Nat.pow_dvd_pow
    have : 1 ≤ a - j := by omega
    calc W = W * 1 := (Nat.mul_one W).symm
      _ ≤ W * (a - j) := Nat.mul_le_mul_left W this
  have key : ∀ x : ℕ, x % 2 ^ (W * a) / 2 ^ (W * j) % 2 ^ W = x / 2 ^ (W * j) % 2 ^ W := by
    intro x
    rw [hsplit, pow_add, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ hdvd]
  rw [ext_eq, ext_eq, ext_eq]
  simp only [← pow_mul]
  rw [key, Nat.div_div_eq_div_mul, ← pow_add]
  congr 3
  ring

/-! ## The h keys in frame coordinates (mirrors of `x2KeyTau`, `x2ImageFrame` for the concrete data) -/

theorem x2h_keyTypes_lt7 : ∀ b : x2Key 0, ∀ i : Fin 3, (x2KeyTypes 0 b i : ℕ) < 7 := by
  decide +kernel

/-- The h type triple of an h key (mirror of `x2KeyTau`). -/
def x2hTau (b : x2Key 0) : Fin 7 × Fin 7 × Fin 7 :=
  (⟨x2KeyTypes 0 b 0, x2h_keyTypes_lt7 b 0⟩, ⟨x2KeyTypes 0 b 1, x2h_keyTypes_lt7 b 1⟩,
    ⟨x2KeyTypes 0 b 2, x2h_keyTypes_lt7 b 2⟩)

/-- The image of an h key in frame coordinates: entry `(i, c)` is `J_b[i, c]`. -/
noncomputable def x2hImage (b : x2Key 0) : Matrix (HIdx (x2hTau b)) (x2Col 0 b) ℂ :=
  Matrix.of fun i c => ((X2.x2JEntry (x2KeyGlobal 0 b) i c : ℤ) : ℂ)

/-! ## Kernel-side entries and permuted indices -/

/-- `J_g[i, c]` read in two levels (slab of `S` slots, then the slot). -/
noncomputable def jEntry2 (g S i c : ℕ) : ℤ :=
  (ext (ext (X2.x2JCols g c) (Nat.mul 11 S) (i / S)) 11 (i % S) : ℤ) - 2 ^ 10

theorem jEntry2_eq (g S i c : ℕ) (hS : 0 < S) : jEntry2 g S i c = X2.x2JEntry g i c := by
  unfold jEntry2 X2.x2JEntry X2.ent X2.dig
  rw [Nat.mul_eq, ext_ext _ 11 S (i / S) (i % S) (Nat.mod_lt _ hS), Nat.div_add_mod, ext_eq, pow_mul]

/-- Natural coordinates of a frame index (kernel form). -/
def coordsN (m1 m2 i : ℕ) : Fin 3 → ℕ := ![i / (m1 * m2), i % (m1 * m2) / m2, i % (m1 * m2) % m2]

/-- Frame index of permuted coordinates (kernel form). -/
def pidxN (m1 m2 i : ℕ) (p : Fin 6) : ℕ :=
  (coordsN m1 m2 i ∘ x2Perm3 p) 0 * (m1 * m2) +
    ((coordsN m1 m2 i ∘ x2Perm3 p) 1 * m2 + (coordsN m1 m2 i ∘ x2Perm3 p) 2)

/-- All `(i, c)` with `i < n`, `c < r` satisfy `f`. -/
def allIC (n r : ℕ) (f : ℕ → ℕ → Bool) : Bool :=
  (List.range n).all fun i => (List.range r).all fun c => f i c

theorem allIC_spec (n r : ℕ) (f : ℕ → ℕ → Bool) (h : allIC n r f = true) (i c : ℕ) (hi : i < n)
    (hc : c < r) : f i c = true := by
  unfold allIC at h
  exact List.all_eq_true.mp (List.all_eq_true.mp h i (List.mem_range.mpr hi)) c (List.mem_range.mpr hc)

/-- The per-key kernel check of the kind projector and of the standard swap. -/
noncomputable def kindCheck (b : x2Key 0) : Bool :=
  let τ := x2hTau b
  let m1 := hsz τ.2.1
  let m2 := hsz τ.2.2
  let n := hsz τ.1 * (m1 * m2)
  let r := x2KeySize 0 b
  let g := (x2KeyGlobal 0 b : ℕ)
  let e := fun i c => jEntry2 g (m1 * m2) i c
  let kd := x2KeyKind 0 b
  (if τ.1 = τ.2.1 ∧ τ.2.1 = τ.2.2 then
    (if kd = 0 then allIC n r (fun i c => (List.finRange 6).all fun p => e (pidxN m1 m2 i p) c == e i c)
     else if kd = 1 then allIC n r (fun i c => (List.finRange 6).all fun p =>
        e (pidxN m1 m2 i p) c == (if x2Perm3Sign p = 1 then e i c else -e i c))
     else allIC n r (fun i c => e (pidxN m1 m2 i 0) c + e (pidxN m1 m2 i 3) c + e (pidxN m1 m2 i 4) c == 0))
  else if τ.1 = τ.2.1 then
    allIC n r (fun i c => e (pidxN m1 m2 i x2Swap01Idx) c == (if kd = 0 then e i c else -e i c))
  else if τ.2.1 = τ.2.2 then
    allIC n r (fun i c => e (pidxN m1 m2 i x2Swap12Idx) c == (if kd = 0 then e i c else -e i c))
  else true) &&
  (if x2KeyDegree 0 b = 2 then decide (τ.1 = τ.2.1) && allIC n r (fun i c => e (pidxN m1 m2 i x2Swap01Idx) c == e i c)
    else true)

theorem hsz_pos (τ : Fin 7 × Fin 7 × Fin 7) (i : HIdx τ) : 0 < hsz τ.2.1 * hsz τ.2.2 := by
  have h : 0 < hsz τ.1 * (hsz τ.2.1 * hsz τ.2.2) := lt_of_le_of_lt (Nat.zero_le _) i.isLt
  rcases Nat.eq_zero_or_pos (hsz τ.2.1 * hsz τ.2.2) with h0 | h0
  · rw [h0, Nat.mul_zero] at h
    exact absurd h (lt_irrefl 0)
  · exact h0

theorem x2hImage_apply (b : x2Key 0) (i : HIdx (x2hTau b)) (c : x2Col 0 b) :
    x2hImage b i c = ((jEntry2 (x2KeyGlobal 0 b) (hsz (x2hTau b).2.1 * hsz (x2hTau b).2.2) i c : ℤ) : ℂ) := by
  simp only [x2hImage, Matrix.of_apply]
  rw [jEntry2_eq _ _ _ _ (hsz_pos _ i)]

end ThreeCopyQutritWerner.X2Sites
