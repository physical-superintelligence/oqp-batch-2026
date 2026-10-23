module

public import ThreeCopyQutritWerner.CertificateX2ReducedChecks

@[expose] public section


/-!
# The parity form of the reduced transfer

Unit coordinates `(t, a, b)` of a sector (`X2U s`, 513 of them) and the certificate's parity coordinates
(`X2P = Fin 282 ⊕ Fin 231`) are related by the selection `N` (`x2Select`) and the expansion `Ni`
(`x2Expand`). The main theorem `x2RawH_eq_unitTransfer` identifies the reduced transfer of
`CertificateX2Reduced` (parity tensors `S`, `A`, contraction with `Rs ⊕ Ra`, reading `x2RawH`)
with the plain three-site transfer `Q_s ⊗ Q_s ⊗ Q_s` of the source Q-form tensor in unit
coordinates, `Q_s = Ni₀ (Rs ⊕ Ra) N_s` (`x2Qu`), for symmetric source blocks.

The two properties of the source tensor that make the parity storage exact are proved here from
the definitions: evenness under the simultaneous transpose of all three sites (symmetric blocks),
and S3 covariance (the averaged arrangement lookup of `x2FullTensor`).
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

set_option maxRecDepth 100000

namespace ThreeCopyQutritWerner

/-! ## Labels -/

/-- An S-label decodes back to the sorted pair. -/
theorem x2_sIdx_label : ∀ s : Fin 3, ∀ t : Fin 8, ∀ a b : Fin (x2Mult s t),
    x2SLabel s (x2SIdx s t a b) = (t, min (a : ℕ) b, max (a : ℕ) b) := by
  decide +kernel

/-- An A-label of an off-diagonal pair decodes back to the sorted pair. -/
theorem x2_aIdx_label : ∀ s : Fin 3, ∀ t : Fin 8, ∀ a b : Fin (x2Mult s t), (a : ℕ) ≠ b →
    x2ALabel s (x2AIdx s t a b) = (t, min (a : ℕ) b, max (a : ℕ) b) := by
  decide +kernel

theorem x2SIdx_swap (s : Fin 3) (t : Fin 8) (a b : ℕ) : x2SIdx s t b a = x2SIdx s t a b := by
  simp only [x2SIdx, min_comm b a, max_comm b a]

theorem x2AIdx_swap (s : Fin 3) (t : Fin 8) (a b : ℕ) : x2AIdx s t b a = x2AIdx s t a b := by
  simp only [x2AIdx, min_comm b a, max_comm b a]

theorem x2Sgn_swap (a b : ℕ) : x2Sgn b a = -x2Sgn a b := by
  rcases lt_trichotomy a b with h | rfl | h
  · simp [x2Sgn, h, not_lt.mpr h.le]
  · simp [x2Sgn]
  · simp [x2Sgn, h, not_lt.mpr h.le]

theorem x2Sgn_self (a : ℕ) : x2Sgn a a = 0 := by
  simp [x2Sgn]

/-! ## Unit and parity coordinates -/

/-- Local Q-form unit coordinates `(t, a, b)` of sector `s`. -/
abbrev X2U (s : Fin 3) := Σ t : Fin 8, Fin (x2Mult s t) × Fin (x2Mult s t)

/-- The certificate's parity coordinates: 282 symmetric and 231 antisymmetric labels. -/
abbrev X2P := Fin 282 ⊕ Fin 231

/-- Selection `N` (units to parity): `S = (x_ab + x_ba) / 2` (`x_aa` on the diagonal),
`A = (x_ab - x_ba) / 2`. -/
def x2Select (s : Fin 3) : Matrix X2P (X2U s) ℚ := fun p u =>
  match p with
  | Sum.inl l => if x2SIdx s u.1 u.2.1 u.2.2 = l then
      (if (u.2.1 : ℕ) = u.2.2 then 1 else 1 / 2) else 0
  | Sum.inr l => if x2AIdx s u.1 u.2.1 u.2.2 = l then x2Sgn u.2.1 u.2.2 / 2 else 0

/-- Expansion `Ni` (parity to units): `x_ab = S + sgn · A`. -/
def x2Expand (s : Fin 3) : Matrix (X2U s) X2P ℚ := fun u p =>
  match p with
  | Sum.inl l => if x2SIdx s u.1 u.2.1 u.2.2 = l then 1 else 0
  | Sum.inr l => if x2AIdx s u.1 u.2.1 u.2.2 = l then x2Sgn u.2.1 u.2.2 else 0

/-- The block diagonal parity transfer `Rs ⊕ Ra`. -/
def x2ParityTransfer (D : X2Data) (s : Fin 3) : Matrix X2P X2P ℚ :=
  Matrix.fromBlocks (D.transS s) 0 0 (D.transA s)

/-- The transfer in unit coordinates, `Q_s = Ni₀ (Rs ⊕ Ra) N_s`. -/
def x2Qu (D : X2Data) (s : Fin 3) : Matrix (X2U 0) (X2U s) ℚ :=
  x2Expand 0 * x2ParityTransfer D s * x2Select s

/-- The source three-site Q-form tensor in unit coordinates. -/
def x2Fm (D : X2Data) (s : Fin 3) (N : X2Blocks s) (v₀ v₁ v₂ : X2U s) : ℚ :=
  x2FullTensor D s N ![v₀.1, v₁.1, v₂.1] ![(v₀.2.1 : ℕ), v₁.2.1, v₂.2.1]
    ![(v₀.2.2 : ℕ), v₁.2.2, v₂.2.2]

/-- The source tensor as a vector on unit triples. -/
def x2FmVec (D : X2Data) (s : Fin 3) (N : X2Blocks s) : X2U s × X2U s × X2U s → ℚ :=
  fun v => x2Fm D s N v.1 v.2.1 v.2.2

/-- Parity components of the source tensor. -/
def x2Phi (D : X2Data) (s : Fin 3) (N : X2Blocks s) : X2P × X2P × X2P → ℚ :=
  (x2Select s ⊗ₖ (x2Select s ⊗ₖ x2Select s)) *ᵥ x2FmVec D s N

/-- Transferred parity components. -/
def x2Psi (D : X2Data) (s : Fin 3) (N : X2Blocks s) : X2P × X2P × X2P → ℚ :=
  (x2ParityTransfer D s ⊗ₖ (x2ParityTransfer D s ⊗ₖ x2ParityTransfer D s)) *ᵥ x2Phi D s N

/-! ## Three-fold Kronecker products -/

theorem x2_kron3_mulVec {α β : Type*} [Fintype β] (M : Matrix α β ℚ) (f : β × β × β → ℚ)
    (a : α × α × α) :
    ((M ⊗ₖ (M ⊗ₖ M)) *ᵥ f) a =
      ∑ b₀, ∑ b₁, ∑ b₂, M a.1 b₀ * M a.2.1 b₁ * M a.2.2 b₂ * f (b₀, b₁, b₂) := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kroneckerMap_apply]
  apply Finset.sum_congr rfl
  intro b₀ _
  apply Finset.sum_congr rfl
  intro b₁ _
  apply Finset.sum_congr rfl
  intro b₂ _
  ring

theorem x2_kron3_mul {α β γ : Type*} [Fintype β] [DecidableEq β]
    (A : Matrix α β ℚ) (B : Matrix β γ ℚ) :
    (A * B) ⊗ₖ ((A * B) ⊗ₖ (A * B)) = (A ⊗ₖ (A ⊗ₖ A)) * (B ⊗ₖ (B ⊗ₖ B)) := by
  rw [Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul]

/-- Swap the first two sites of a triple. -/
def x2Swap01 (α : Type*) : α × α × α ≃ α × α × α where
  toFun v := (v.2.1, v.1, v.2.2)
  invFun v := (v.2.1, v.1, v.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Move the last site of a triple to the front: `(v₀, v₁, v₂) ↦ (v₂, v₀, v₁)`. -/
def x2Cyc (α : Type*) : α × α × α ≃ α × α × α where
  toFun v := (v.2.2, v.1, v.2.1)
  invFun v := (v.2.1, v.2.2, v.1)
  left_inv _ := rfl
  right_inv _ := rfl

theorem x2_kron3_apply_swap01 {α β : Type*} (M : Matrix α β ℚ) (a : α × α × α) (b : β × β × β) :
    (M ⊗ₖ (M ⊗ₖ M)) (x2Swap01 α a) (x2Swap01 β b) = (M ⊗ₖ (M ⊗ₖ M)) a b := by
  simp only [x2Swap01, Equiv.coe_fn_mk, Matrix.kroneckerMap_apply]
  ring

theorem x2_kron3_apply_cyc {α β : Type*} (M : Matrix α β ℚ) (a : α × α × α) (b : β × β × β) :
    (M ⊗ₖ (M ⊗ₖ M)) (x2Cyc α a) (x2Cyc β b) = (M ⊗ₖ (M ⊗ₖ M)) a b := by
  simp only [x2Cyc, Equiv.coe_fn_mk, Matrix.kroneckerMap_apply]
  ring

/-- A Kronecker cube applied to a vector invariant under a site permutation `e`. -/
theorem x2_kron3_mulVec_perm {α β : Type*} [Fintype β] (M : Matrix α β ℚ) (f : β × β × β → ℚ)
    (eα : α × α × α ≃ α × α × α) (eβ : β × β × β ≃ β × β × β)
    (hM : ∀ a b, (M ⊗ₖ (M ⊗ₖ M)) (eα a) (eβ b) = (M ⊗ₖ (M ⊗ₖ M)) a b)
    (hf : ∀ b, f (eβ b) = f b) (a : α × α × α) :
    ((M ⊗ₖ (M ⊗ₖ M)) *ᵥ f) (eα a) = ((M ⊗ₖ (M ⊗ₖ M)) *ᵥ f) a := by
  simp only [Matrix.mulVec, dotProduct]
  rw [← Equiv.sum_comp eβ]
  apply Finset.sum_congr rfl
  intro b _
  rw [hM, hf]

/-! ## Local collapse of the selection -/

/-- Total lookup of a function on unit coordinates at natural coordinates (zero outside). -/
def x2GetU (s : Fin 3) (g : X2U s → ℚ) (t : Fin 8) (a b : ℕ) : ℚ :=
  if h : a < x2Mult s t ∧ b < x2Mult s t then g ⟨t, (⟨a, h.1⟩, ⟨b, h.2⟩)⟩ else 0

theorem x2GetU_mk (s : Fin 3) (g : X2U s → ℚ) (t : Fin 8) (a b : ℕ)
    (ha : a < x2Mult s t) (hb : b < x2Mult s t) :
    x2GetU s g t a b = g ⟨t, (⟨a, ha⟩, ⟨b, hb⟩)⟩ := by
  rw [x2GetU, dif_pos ⟨ha, hb⟩]

theorem x2SelS_congr (f f' : ℕ → ℕ → ℚ) (a b : ℕ)
    (h : ∀ x y, (x = a ∨ x = b) → (y = a ∨ y = b) → f x y = f' x y) :
    x2SelS f a b = x2SelS f' a b := by
  unfold x2SelS
  rw [h a a (Or.inl rfl) (Or.inl rfl), h a b (Or.inl rfl) (Or.inr rfl),
    h b a (Or.inr rfl) (Or.inl rfl)]

theorem x2SelA_congr (f f' : ℕ → ℕ → ℚ) (a b : ℕ)
    (h : ∀ x y, (x = a ∨ x = b) → (y = a ∨ y = b) → f x y = f' x y) :
    x2SelA f a b = x2SelA f' a b := by
  unfold x2SelA
  rw [h a b (Or.inl rfl) (Or.inr rfl), h b a (Or.inr rfl) (Or.inl rfl)]

/-- Symmetric selection collapses to the two orientations of the label's pair. -/
theorem x2_sum_select_inl (s : Fin 3) (l : Fin 282) (g : X2U s → ℚ) :
    ∑ v : X2U s, x2Select s (Sum.inl l) v * g v =
      x2SelS (x2GetU s g (x2SLabel s l).1) (x2SLabel s l).2.1 (x2SLabel s l).2.2 := by
  have hv := x2_sLabel_valid s l
  rcases hl : x2SLabel s l with ⟨t, a₀, b₀⟩
  rw [hl] at hv
  obtain ⟨hidx, hab, hbm⟩ := hv
  dsimp only at hidx hab hbm ⊢
  have ham : a₀ < x2Mult s t := lt_of_le_of_lt hab hbm
  have hfib : ∀ (t' : Fin 8) (p : Fin (x2Mult s t') × Fin (x2Mult s t')),
      x2SIdx s t' p.1 p.2 = l → t' = t ∧ min (p.1 : ℕ) p.2 = a₀ ∧ max (p.1 : ℕ) p.2 = b₀ := by
    intro t' p h
    have h2 := x2_sIdx_label s t' p.1 p.2
    rw [h, hl] at h2
    simp only [Prod.mk.injEq] at h2
    exact ⟨h2.1.symm, h2.2.1.symm, h2.2.2.symm⟩
  rw [Fintype.sum_sigma, Finset.sum_eq_single t]
  · have hpair : ∀ p : Fin (x2Mult s t) × Fin (x2Mult s t), x2SIdx s t p.1 p.2 = l →
        p = (⟨a₀, ham⟩, ⟨b₀, hbm⟩) ∨ p = (⟨b₀, hbm⟩, ⟨a₀, ham⟩) := by
      intro p h
      obtain ⟨-, hmin, hmax⟩ := hfib t p h
      rcases le_total (p.1 : ℕ) p.2 with hle | hle
      · left
        rw [min_eq_left hle] at hmin
        rw [max_eq_right hle] at hmax
        exact Prod.ext (Fin.ext hmin) (Fin.ext hmax)
      · right
        rw [min_eq_right hle] at hmin
        rw [max_eq_left hle] at hmax
        exact Prod.ext (Fin.ext hmax) (Fin.ext hmin)
    rcases eq_or_lt_of_le hab with heq | hlt
    · -- diagonal label
      subst heq
      rw [Finset.sum_eq_single (⟨a₀, ham⟩, ⟨a₀, ham⟩)]
      · simp [x2Select, hidx, x2SelS, x2GetU_mk s g t a₀ a₀ ham ham]
      · intro p _ hp
        have h0 : x2SIdx s t p.1 p.2 ≠ l := by
          intro h
          rcases hpair p h with h' | h' <;> exact hp h'
        simp only [x2Select, if_neg h0, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · -- off-diagonal label
      have hne : a₀ ≠ b₀ := Nat.ne_of_lt hlt
      have hAB : ((⟨a₀, ham⟩, ⟨b₀, hbm⟩) : Fin (x2Mult s t) × Fin (x2Mult s t)) ≠
          (⟨b₀, hbm⟩, ⟨a₀, ham⟩) := by
        intro h
        exact hne (congrArg (fun p => (p.1 : ℕ)) h)
      rw [Fintype.sum_eq_add _ _ hAB]
      · have hBA : x2SIdx s t b₀ a₀ = l := by rw [x2SIdx_swap]; exact hidx
        simp [x2Select, hidx, hBA, hne, Ne.symm hne, x2SelS, x2GetU_mk s g t a₀ b₀ ham hbm,
          x2GetU_mk s g t b₀ a₀ hbm ham] <;> ring
      · intro p hp
        have h0 : x2SIdx s t p.1 p.2 ≠ l := by
          intro h
          rcases hpair p h with h' | h'
          · exact hp.1 h'
          · exact hp.2 h'
        simp only [x2Select, if_neg h0, zero_mul]
  · intro t' _ ht'
    apply Finset.sum_eq_zero
    intro p _
    have h0 : x2SIdx s t' p.1 p.2 ≠ l := fun h => ht' (hfib t' p h).1
    simp only [x2Select, if_neg h0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Antisymmetric selection collapses to the two orientations of the label's pair. -/
theorem x2_sum_select_inr (s : Fin 3) (l : Fin 231) (g : X2U s → ℚ) :
    ∑ v : X2U s, x2Select s (Sum.inr l) v * g v =
      x2SelA (x2GetU s g (x2ALabel s l).1) (x2ALabel s l).2.1 (x2ALabel s l).2.2 := by
  have hv := x2_aLabel_valid s l
  rcases hl : x2ALabel s l with ⟨t, a₀, b₀⟩
  rw [hl] at hv
  obtain ⟨hidx, hab, hbm⟩ := hv
  dsimp only at hidx hab hbm ⊢
  have ham : a₀ < x2Mult s t := lt_trans hab hbm
  have hfib : ∀ (t' : Fin 8) (p : Fin (x2Mult s t') × Fin (x2Mult s t')), (p.1 : ℕ) ≠ p.2 →
      x2AIdx s t' p.1 p.2 = l → t' = t ∧ min (p.1 : ℕ) p.2 = a₀ ∧ max (p.1 : ℕ) p.2 = b₀ := by
    intro t' p hne h
    have h2 := x2_aIdx_label s t' p.1 p.2 hne
    rw [h, hl] at h2
    simp only [Prod.mk.injEq] at h2
    exact ⟨h2.1.symm, h2.2.1.symm, h2.2.2.symm⟩
  have hzero : ∀ (t' : Fin 8) (p : Fin (x2Mult s t') × Fin (x2Mult s t')),
      ¬ (t' = t ∧ min (p.1 : ℕ) p.2 = a₀ ∧ max (p.1 : ℕ) p.2 = b₀) →
      x2Select s (Sum.inr l) ⟨t', p⟩ = 0 := by
    intro t' p hp
    by_cases hne : (p.1 : ℕ) = p.2
    · show (if x2AIdx s t' p.1 p.2 = l then x2Sgn p.1 p.2 / 2 else 0) = 0
      rw [hne, x2Sgn_self]
      simp
    · show (if x2AIdx s t' p.1 p.2 = l then x2Sgn p.1 p.2 / 2 else 0) = 0
      rw [if_neg (fun h => hp (hfib t' p hne h))]
  rw [Fintype.sum_sigma, Finset.sum_eq_single t]
  · have hne : a₀ ≠ b₀ := Nat.ne_of_lt hab
    have hAB : ((⟨a₀, ham⟩, ⟨b₀, hbm⟩) : Fin (x2Mult s t) × Fin (x2Mult s t)) ≠
        (⟨b₀, hbm⟩, ⟨a₀, ham⟩) := by
      intro h
      exact hne (congrArg (fun p => (p.1 : ℕ)) h)
    rw [Fintype.sum_eq_add _ _ hAB]
    · have hBA : x2AIdx s t b₀ a₀ = l := by rw [x2AIdx_swap]; exact hidx
      have h1 : x2Sgn a₀ b₀ = 1 := by simp [x2Sgn, hab]
      have h2 : x2Sgn b₀ a₀ = -1 := by rw [x2Sgn_swap, h1]
      simp [x2Select, hidx, hBA, h1, h2, x2SelA, x2GetU_mk s g t a₀ b₀ ham hbm,
        x2GetU_mk s g t b₀ a₀ hbm ham] <;> ring
    · intro p hp
      rw [hzero t p, zero_mul]
      rintro ⟨-, hmin, hmax⟩
      rcases le_total (p.1 : ℕ) p.2 with hle | hle
      · rw [min_eq_left hle] at hmin
        rw [max_eq_right hle] at hmax
        exact hp.1 (Prod.ext (Fin.ext hmin) (Fin.ext hmax))
      · rw [min_eq_right hle] at hmin
        rw [max_eq_left hle] at hmax
        exact hp.2 (Prod.ext (Fin.ext hmax) (Fin.ext hmin))
  · intro t' _ ht'
    apply Finset.sum_eq_zero
    intro p _
    rw [hzero t' p (fun h => ht' h.1), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ## Evenness and S3 covariance of the source tensor -/

/-- Transpose of a unit coordinate. -/
def x2Bar (s : Fin 3) : X2U s ≃ X2U s where
  toFun u := ⟨u.1, (u.2.2, u.2.1)⟩
  invFun u := ⟨u.1, (u.2.2, u.2.1)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem x2Select_bar_inl (s : Fin 3) (l : Fin 282) (u : X2U s) :
    x2Select s (Sum.inl l) (x2Bar s u) = x2Select s (Sum.inl l) u := by
  show (if x2SIdx s u.1 u.2.2 u.2.1 = l then (if (u.2.2 : ℕ) = u.2.1 then 1 else 1 / 2) else 0) =
    (if x2SIdx s u.1 u.2.1 u.2.2 = l then (if (u.2.1 : ℕ) = u.2.2 then 1 else 1 / 2) else 0)
  rw [x2SIdx_swap s u.1 (u.2.1 : ℕ) (u.2.2 : ℕ)]
  by_cases h : (u.2.1 : ℕ) = u.2.2
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem x2Select_bar_inr (s : Fin 3) (l : Fin 231) (u : X2U s) :
    x2Select s (Sum.inr l) (x2Bar s u) = -x2Select s (Sum.inr l) u := by
  show (if x2AIdx s u.1 u.2.2 u.2.1 = l then x2Sgn u.2.2 u.2.1 / 2 else 0) =
    -(if x2AIdx s u.1 u.2.1 u.2.2 = l then x2Sgn u.2.1 u.2.2 / 2 else 0)
  rw [x2AIdx_swap s u.1 (u.2.1 : ℕ) (u.2.2 : ℕ), x2Sgn_swap (u.2.1 : ℕ) (u.2.2 : ℕ)]
  split_ifs <;> ring

theorem x2Lookup_comm {p q r : ℕ}
    (M : Matrix (Fin p × Fin q × Fin r) (Fin p × Fin q × Fin r) ℚ) (hM : Mᵀ = M)
    (a b : Fin 3 → ℕ) : x2Lookup M b a = x2Lookup M a b := by
  unfold x2Lookup
  by_cases h : (a 0 < p ∧ a 1 < q ∧ a 2 < r) ∧ (b 0 < p ∧ b 1 < q ∧ b 2 < r)
  · rw [dif_pos ⟨h.2, h.1⟩, dif_pos h]
    exact congrFun (congrFun hM _) _
  · rw [dif_neg (fun h' => h ⟨h'.2, h'.1⟩), dif_neg h]

theorem x2Partner_transpose_mul {p q r : ℕ} {ι : Type*} [Fintype ι]
    (V : Matrix (Fin p × Fin q × Fin r) ι ℚ) (N : Matrix ι ι ℚ) (hN : Nᵀ = N) :
    (x2Partner V * N * (x2Partner V)ᵀ)ᵀ = x2Partner V * N * (x2Partner V)ᵀ := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hN,
    Matrix.mul_assoc]

theorem x2InputBlock_transpose (D : X2Data) (s : Fin 3) (N : X2Blocks s)
    (hN : ∀ k, (N k)ᵀ = N k) (k : x2Key s) :
    (x2InputBlock D s N k)ᵀ = x2InputBlock D s N k := by
  unfold x2InputBlock
  simp only
  rw [Matrix.transpose_add]
  congr 1
  · rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hN k,
      Matrix.mul_assoc]
  · split_ifs
    · rw [Matrix.transpose_smul, x2Partner_transpose_mul _ _ (hN k)]
    · exact Matrix.transpose_zero

/-- Evenness: transposing all three sites at once does not change the source tensor. -/
theorem x2FullTensor_swap (D : X2Data) (s : Fin 3) (N : X2Blocks s)
    (hN : ∀ k, (N k)ᵀ = N k) (t : Fin 3 → Fin 8) (a b : Fin 3 → ℕ) :
    x2FullTensor D s N t b a = x2FullTensor D s N t a b := by
  unfold x2FullTensor
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro p _
  split_ifs
  · rw [x2Lookup_comm _ (x2InputBlock_transpose D s N hN k)]
  · rfl

theorem x2Fm_bar (D : X2Data) (s : Fin 3) (N : X2Blocks s) (hN : ∀ k, (N k)ᵀ = N k)
    (v₀ v₁ v₂ : X2U s) :
    x2Fm D s N (x2Bar s v₀) (x2Bar s v₁) (x2Bar s v₂) = x2Fm D s N v₀ v₁ v₂ := by
  simp only [x2Fm, x2Bar, Equiv.coe_fn_mk]
  exact x2FullTensor_swap D s N hN _ _ _

/-- Composition table of the six site permutations. -/
def x2Perm3Mul : Fin 6 → Fin 6 → Fin 6 :=
  ![![0, 1, 2, 3, 4, 5], ![1, 0, 4, 5, 2, 3], ![2, 3, 0, 1, 5, 4],
    ![3, 2, 5, 4, 0, 1], ![4, 5, 1, 0, 3, 2], ![5, 4, 3, 2, 1, 0]]

theorem x2_perm3Mul_spec : ∀ q p : Fin 6,
    x2Perm3 (x2Perm3Mul q p) = x2Perm3 q ∘ x2Perm3 p := by
  decide +kernel

theorem x2_perm3Mul_bijective : ∀ q : Fin 6, Function.Bijective (x2Perm3Mul q) := by
  decide +kernel

theorem x2ArrangeCount_perm (q : Fin 6) (t τ : Fin 3 → Fin 8) :
    x2ArrangeCount (t ∘ x2Perm3 q) τ = x2ArrangeCount t τ := by
  unfold x2ArrangeCount
  rw [Finset.card_filter, Finset.card_filter]
  conv_rhs => rw [← (Equiv.ofBijective _ (x2_perm3Mul_bijective q)).sum_comp]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Equiv.ofBijective_apply, x2_perm3Mul_spec]
  rfl

/-- S3 covariance: permuting the sites of the arrangement and of the unit coordinates together
does not change the source tensor. -/
theorem x2FullTensor_perm (D : X2Data) (s : Fin 3) (N : X2Blocks s) (q : Fin 6)
    (t : Fin 3 → Fin 8) (a b : Fin 3 → ℕ) :
    x2FullTensor D s N (t ∘ x2Perm3 q) (a ∘ x2Perm3 q) (b ∘ x2Perm3 q) =
      x2FullTensor D s N t a b := by
  unfold x2FullTensor
  apply Finset.sum_congr rfl
  intro k _
  conv_rhs => rw [← (Equiv.ofBijective _ (x2_perm3Mul_bijective q)).sum_comp]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Equiv.ofBijective_apply, x2_perm3Mul_spec, x2ArrangeCount_perm]
  rfl

theorem x2Fm_swap01 (D : X2Data) (s : Fin 3) (N : X2Blocks s) (v₀ v₁ v₂ : X2U s) :
    x2Fm D s N v₁ v₀ v₂ = x2Fm D s N v₀ v₁ v₂ := by
  have h := x2FullTensor_perm D s N 2 ![v₀.1, v₁.1, v₂.1] ![(v₀.2.1 : ℕ), v₁.2.1, v₂.2.1]
    ![(v₀.2.2 : ℕ), v₁.2.2, v₂.2.2]
  have e1 : (![v₀.1, v₁.1, v₂.1] ∘ x2Perm3 2) = ![v₁.1, v₀.1, v₂.1] := by
    funext i; fin_cases i <;> rfl
  have e2 : (![(v₀.2.1 : ℕ), v₁.2.1, v₂.2.1] ∘ x2Perm3 2) = ![(v₁.2.1 : ℕ), v₀.2.1, v₂.2.1] := by
    funext i; fin_cases i <;> rfl
  have e3 : (![(v₀.2.2 : ℕ), v₁.2.2, v₂.2.2] ∘ x2Perm3 2) = ![(v₁.2.2 : ℕ), v₀.2.2, v₂.2.2] := by
    funext i; fin_cases i <;> rfl
  rw [e1, e2, e3] at h
  exact h

theorem x2Fm_cyc (D : X2Data) (s : Fin 3) (N : X2Blocks s) (v₀ v₁ v₂ : X2U s) :
    x2Fm D s N v₂ v₀ v₁ = x2Fm D s N v₀ v₁ v₂ := by
  have h := x2FullTensor_perm D s N 4 ![v₀.1, v₁.1, v₂.1] ![(v₀.2.1 : ℕ), v₁.2.1, v₂.2.1]
    ![(v₀.2.2 : ℕ), v₁.2.2, v₂.2.2]
  have e1 : (![v₀.1, v₁.1, v₂.1] ∘ x2Perm3 4) = ![v₂.1, v₀.1, v₁.1] := by
    funext i; fin_cases i <;> rfl
  have e2 : (![(v₀.2.1 : ℕ), v₁.2.1, v₂.2.1] ∘ x2Perm3 4) = ![(v₂.2.1 : ℕ), v₀.2.1, v₁.2.1] := by
    funext i; fin_cases i <;> rfl
  have e3 : (![(v₀.2.2 : ℕ), v₁.2.2, v₂.2.2] ∘ x2Perm3 4) = ![(v₂.2.2 : ℕ), v₀.2.2, v₁.2.2] := by
    funext i; fin_cases i <;> rfl
  rw [e1, e2, e3] at h
  exact h

/-! ## Parity components -/

theorem x2Phi_swap01 (D : X2Data) (s : Fin 3) (N : X2Blocks s) (q : X2P × X2P × X2P) :
    x2Phi D s N (x2Swap01 X2P q) = x2Phi D s N q := by
  unfold x2Phi
  apply x2_kron3_mulVec_perm _ _ (x2Swap01 X2P) (x2Swap01 (X2U s))
    (x2_kron3_apply_swap01 _)
  intro v
  simp only [x2FmVec, x2Swap01, Equiv.coe_fn_mk]
  exact x2Fm_swap01 D s N v.1 v.2.1 v.2.2

theorem x2Phi_cyc (D : X2Data) (s : Fin 3) (N : X2Blocks s) (q : X2P × X2P × X2P) :
    x2Phi D s N (x2Cyc X2P q) = x2Phi D s N q := by
  unfold x2Phi
  apply x2_kron3_mulVec_perm _ _ (x2Cyc X2P) (x2Cyc (X2U s)) (x2_kron3_apply_cyc _)
  intro v
  simp only [x2FmVec, x2Cyc, Equiv.coe_fn_mk]
  exact x2Fm_cyc D s N v.1 v.2.1 v.2.2

/-- Transpose of all three unit coordinates. -/
def x2BarT (s : Fin 3) : X2U s × X2U s × X2U s ≃ X2U s × X2U s × X2U s where
  toFun v := (x2Bar s v.1, x2Bar s v.2.1, x2Bar s v.2.2)
  invFun v := (x2Bar s v.1, x2Bar s v.2.1, x2Bar s v.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Sign of a parity coordinate under transpose. -/
def x2ParitySign : X2P → ℚ
  | Sum.inl _ => 1
  | Sum.inr _ => -1

theorem x2Select_bar (s : Fin 3) (p : X2P) (u : X2U s) :
    x2Select s p (x2Bar s u) = x2ParitySign p * x2Select s p u := by
  cases p with
  | inl l => rw [x2Select_bar_inl]; simp [x2ParitySign]
  | inr l => rw [x2Select_bar_inr]; simp [x2ParitySign]

/-- The parity components change by the product of the three parity signs under transpose,
hence vanish for an odd number of antisymmetric sites. -/
theorem x2Phi_sign (D : X2Data) (s : Fin 3) (N : X2Blocks s) (hN : ∀ k, (N k)ᵀ = N k)
    (q : X2P × X2P × X2P) :
    x2Phi D s N q =
      x2ParitySign q.1 * x2ParitySign q.2.1 * x2ParitySign q.2.2 * x2Phi D s N q := by
  unfold x2Phi
  simp only [Matrix.mulVec, dotProduct]
  conv_lhs => rw [← Equiv.sum_comp (x2BarT s)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  show (x2Select s ⊗ₖ (x2Select s ⊗ₖ x2Select s)) q (x2Bar s v.1, x2Bar s v.2.1, x2Bar s v.2.2) *
      x2FmVec D s N (x2Bar s v.1, x2Bar s v.2.1, x2Bar s v.2.2) = _
  simp only [Matrix.kroneckerMap_apply, x2Select_bar, x2FmVec, x2Fm_bar D s N hN]
  ring

theorem x2Phi_odd (D : X2Data) (s : Fin 3) (N : X2Blocks s) (hN : ∀ k, (N k)ᵀ = N k)
    (q : X2P × X2P × X2P)
    (hq : x2ParitySign q.1 * x2ParitySign q.2.1 * x2ParitySign q.2.2 = -1) :
    x2Phi D s N q = 0 := by
  have h := x2Phi_sign D s N hN q
  rw [hq] at h
  linarith

/-- The all-symmetric parity component is the stored tensor `S`. -/
theorem x2Phi_sss (D : X2Data) (s : Fin 3) (N : X2Blocks s) (l₀ l₁ l₂ : Fin 282) :
    x2Phi D s N (Sum.inl l₀, Sum.inl l₁, Sum.inl l₂) = x2EmbedS D s N l₀ l₁ l₂ := by
  rw [x2Phi, x2_kron3_mulVec]
  simp only [x2FmVec]
  have hv₀ := x2_sLabel_valid s l₀
  have hv₁ := x2_sLabel_valid s l₁
  have hv₂ := x2_sLabel_valid s l₂
  -- collapse site 2, then site 1, then site 0
  have step2 : ∀ v₀ v₁ : X2U s,
      ∑ v₂ : X2U s, x2Select s (Sum.inl l₀) v₀ * x2Select s (Sum.inl l₁) v₁ *
          x2Select s (Sum.inl l₂) v₂ * x2Fm D s N v₀ v₁ v₂ =
        x2Select s (Sum.inl l₀) v₀ * x2Select s (Sum.inl l₁) v₁ *
          x2SelS (x2GetU s (x2Fm D s N v₀ v₁) (x2SLabel s l₂).1)
            (x2SLabel s l₂).2.1 (x2SLabel s l₂).2.2 := by
    intro v₀ v₁
    rw [← x2_sum_select_inl, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v₂ _
    ring
  simp only [step2]
  have step1 : ∀ v₀ : X2U s,
      ∑ v₁ : X2U s, x2Select s (Sum.inl l₀) v₀ * x2Select s (Sum.inl l₁) v₁ *
          x2SelS (x2GetU s (x2Fm D s N v₀ v₁) (x2SLabel s l₂).1)
            (x2SLabel s l₂).2.1 (x2SLabel s l₂).2.2 =
        x2Select s (Sum.inl l₀) v₀ *
          x2SelS (x2GetU s (fun v₁ => x2SelS (x2GetU s (x2Fm D s N v₀ v₁) (x2SLabel s l₂).1)
            (x2SLabel s l₂).2.1 (x2SLabel s l₂).2.2) (x2SLabel s l₁).1)
            (x2SLabel s l₁).2.1 (x2SLabel s l₁).2.2 := by
    intro v₀
    rw [← x2_sum_select_inl s l₁, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v₁ _
    ring
  simp only [step1]
  rw [x2_sum_select_inl s l₀]
  unfold x2EmbedS
  apply x2SelS_congr
  intro x₀ y₀ hx₀ hy₀
  have hx₀m : x₀ < x2Mult s (x2SLabel s l₀).1 := by
    rcases hx₀ with rfl | rfl
    · exact lt_of_le_of_lt hv₀.2.1 hv₀.2.2
    · exact hv₀.2.2
  have hy₀m : y₀ < x2Mult s (x2SLabel s l₀).1 := by
    rcases hy₀ with rfl | rfl
    · exact lt_of_le_of_lt hv₀.2.1 hv₀.2.2
    · exact hv₀.2.2
  rw [x2GetU_mk s _ _ x₀ y₀ hx₀m hy₀m]
  apply x2SelS_congr
  intro x₁ y₁ hx₁ hy₁
  have hx₁m : x₁ < x2Mult s (x2SLabel s l₁).1 := by
    rcases hx₁ with rfl | rfl
    · exact lt_of_le_of_lt hv₁.2.1 hv₁.2.2
    · exact hv₁.2.2
  have hy₁m : y₁ < x2Mult s (x2SLabel s l₁).1 := by
    rcases hy₁ with rfl | rfl
    · exact lt_of_le_of_lt hv₁.2.1 hv₁.2.2
    · exact hv₁.2.2
  rw [x2GetU_mk s _ _ x₁ y₁ hx₁m hy₁m]
  apply x2SelS_congr
  intro x₂ y₂ hx₂ hy₂
  have hx₂m : x₂ < x2Mult s (x2SLabel s l₂).1 := by
    rcases hx₂ with rfl | rfl
    · exact lt_of_le_of_lt hv₂.2.1 hv₂.2.2
    · exact hv₂.2.2
  have hy₂m : y₂ < x2Mult s (x2SLabel s l₂).1 := by
    rcases hy₂ with rfl | rfl
    · exact lt_of_le_of_lt hv₂.2.1 hv₂.2.2
    · exact hv₂.2.2
  rw [x2GetU_mk s _ _ x₂ y₂ hx₂m hy₂m]
  rfl

/-- The (symmetric, antisymmetric, antisymmetric) component is the stored tensor `A`. -/
theorem x2Phi_saa (D : X2Data) (s : Fin 3) (N : X2Blocks s) (l₀ : Fin 282) (l₁ l₂ : Fin 231) :
    x2Phi D s N (Sum.inl l₀, Sum.inr l₁, Sum.inr l₂) = x2EmbedA D s N l₀ l₁ l₂ := by
  rw [x2Phi, x2_kron3_mulVec]
  simp only [x2FmVec]
  have hv₀ := x2_sLabel_valid s l₀
  have hv₁ := x2_aLabel_valid s l₁
  have hv₂ := x2_aLabel_valid s l₂
  have step2 : ∀ v₀ v₁ : X2U s,
      ∑ v₂ : X2U s, x2Select s (Sum.inl l₀) v₀ * x2Select s (Sum.inr l₁) v₁ *
          x2Select s (Sum.inr l₂) v₂ * x2Fm D s N v₀ v₁ v₂ =
        x2Select s (Sum.inl l₀) v₀ * x2Select s (Sum.inr l₁) v₁ *
          x2SelA (x2GetU s (x2Fm D s N v₀ v₁) (x2ALabel s l₂).1)
            (x2ALabel s l₂).2.1 (x2ALabel s l₂).2.2 := by
    intro v₀ v₁
    rw [← x2_sum_select_inr, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v₂ _
    ring
  simp only [step2]
  have step1 : ∀ v₀ : X2U s,
      ∑ v₁ : X2U s, x2Select s (Sum.inl l₀) v₀ * x2Select s (Sum.inr l₁) v₁ *
          x2SelA (x2GetU s (x2Fm D s N v₀ v₁) (x2ALabel s l₂).1)
            (x2ALabel s l₂).2.1 (x2ALabel s l₂).2.2 =
        x2Select s (Sum.inl l₀) v₀ *
          x2SelA (x2GetU s (fun v₁ => x2SelA (x2GetU s (x2Fm D s N v₀ v₁) (x2ALabel s l₂).1)
            (x2ALabel s l₂).2.1 (x2ALabel s l₂).2.2) (x2ALabel s l₁).1)
            (x2ALabel s l₁).2.1 (x2ALabel s l₁).2.2 := by
    intro v₀
    rw [← x2_sum_select_inr s l₁, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v₁ _
    ring
  simp only [step1]
  rw [x2_sum_select_inl s l₀]
  unfold x2EmbedA
  apply x2SelS_congr
  intro x₀ y₀ hx₀ hy₀
  have hx₀m : x₀ < x2Mult s (x2SLabel s l₀).1 := by
    rcases hx₀ with rfl | rfl
    · exact lt_of_le_of_lt hv₀.2.1 hv₀.2.2
    · exact hv₀.2.2
  have hy₀m : y₀ < x2Mult s (x2SLabel s l₀).1 := by
    rcases hy₀ with rfl | rfl
    · exact lt_of_le_of_lt hv₀.2.1 hv₀.2.2
    · exact hv₀.2.2
  rw [x2GetU_mk s _ _ x₀ y₀ hx₀m hy₀m]
  apply x2SelA_congr
  intro x₁ y₁ hx₁ hy₁
  have hx₁m : x₁ < x2Mult s (x2ALabel s l₁).1 := by
    rcases hx₁ with rfl | rfl
    · exact lt_trans hv₁.2.1 hv₁.2.2
    · exact hv₁.2.2
  have hy₁m : y₁ < x2Mult s (x2ALabel s l₁).1 := by
    rcases hy₁ with rfl | rfl
    · exact lt_trans hv₁.2.1 hv₁.2.2
    · exact hv₁.2.2
  rw [x2GetU_mk s _ _ x₁ y₁ hx₁m hy₁m]
  apply x2SelA_congr
  intro x₂ y₂ hx₂ hy₂
  have hx₂m : x₂ < x2Mult s (x2ALabel s l₂).1 := by
    rcases hx₂ with rfl | rfl
    · exact lt_trans hv₂.2.1 hv₂.2.2
    · exact hv₂.2.2
  have hy₂m : y₂ < x2Mult s (x2ALabel s l₂).1 := by
    rcases hy₂ with rfl | rfl
    · exact lt_trans hv₂.2.1 hv₂.2.2
    · exact hv₂.2.2
  rw [x2GetU_mk s _ _ x₂ y₂ hx₂m hy₂m]
  rfl

theorem x2Phi_asa (D : X2Data) (s : Fin 3) (N : X2Blocks s) (l₀ : Fin 231) (l₁ : Fin 282)
    (l₂ : Fin 231) :
    x2Phi D s N (Sum.inr l₀, Sum.inl l₁, Sum.inr l₂) = x2EmbedA D s N l₁ l₀ l₂ := by
  rw [← x2Phi_saa]
  exact x2Phi_swap01 D s N (Sum.inl l₁, Sum.inr l₀, Sum.inr l₂)

theorem x2Phi_aas (D : X2Data) (s : Fin 3) (N : X2Blocks s) (l₀ l₁ : Fin 231) (l₂ : Fin 282) :
    x2Phi D s N (Sum.inr l₀, Sum.inr l₁, Sum.inl l₂) = x2EmbedA D s N l₂ l₀ l₁ := by
  rw [← x2Phi_saa]
  exact (x2Phi_cyc D s N (Sum.inr l₀, Sum.inr l₁, Sum.inl l₂)).symm

/-! ## Transferred parity components -/

theorem x2ParityTransfer_ll (D : X2Data) (s : Fin 3) (i j : Fin 282) :
    x2ParityTransfer D s (Sum.inl i) (Sum.inl j) = D.transS s i j := rfl

theorem x2ParityTransfer_lr (D : X2Data) (s : Fin 3) (i : Fin 282) (j : Fin 231) :
    x2ParityTransfer D s (Sum.inl i) (Sum.inr j) = 0 := rfl

theorem x2ParityTransfer_rl (D : X2Data) (s : Fin 3) (i : Fin 231) (j : Fin 282) :
    x2ParityTransfer D s (Sum.inr i) (Sum.inl j) = 0 := rfl

theorem x2ParityTransfer_rr (D : X2Data) (s : Fin 3) (i j : Fin 231) :
    x2ParityTransfer D s (Sum.inr i) (Sum.inr j) = D.transA s i j := rfl

/-- Split a triple sum over parity coordinates into its eight parity sectors. -/
theorem x2_sum3_parity (f : X2P → X2P → X2P → ℚ) :
    ∑ q₀ : X2P, ∑ q₁ : X2P, ∑ q₂ : X2P, f q₀ q₁ q₂ =
      ∑ q₀ : X2P, ∑ q₁ : X2P,
        ((∑ j : Fin 282, f q₀ q₁ (Sum.inl j)) + ∑ j : Fin 231, f q₀ q₁ (Sum.inr j)) := by
  apply Finset.sum_congr rfl
  intro q₀ _
  apply Finset.sum_congr rfl
  intro q₁ _
  exact Fintype.sum_sum_type _

theorem x2Psi_sss (D : X2Data) (s : Fin 3) (N : X2Blocks s) (i₀ i₁ i₂ : Fin 282) :
    x2Psi D s N (Sum.inl i₀, Sum.inl i₁, Sum.inl i₂) = x2TransferS D s N i₀ i₁ i₂ := by
  rw [x2Psi, x2_kron3_mulVec]
  simp only [Fintype.sum_sum_type, x2ParityTransfer_ll, x2ParityTransfer_lr, zero_mul, mul_zero,
    Finset.sum_const_zero, add_zero, x2Phi_sss]
  simp only [x2TransferS, x2Axis0, x2Axis1, x2Axis2, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem x2Psi_saa (D : X2Data) (s : Fin 3) (N : X2Blocks s) (i₀ : Fin 282) (i₁ i₂ : Fin 231) :
    x2Psi D s N (Sum.inl i₀, Sum.inr i₁, Sum.inr i₂) = x2TransferA D s N i₀ i₁ i₂ := by
  rw [x2Psi, x2_kron3_mulVec]
  simp only [Fintype.sum_sum_type, x2ParityTransfer_ll, x2ParityTransfer_lr, x2ParityTransfer_rl,
    x2ParityTransfer_rr, zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add,
    x2Phi_saa]
  simp only [x2TransferA, x2Axis0, x2Axis1, x2Axis2, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem x2Psi_swap01 (D : X2Data) (s : Fin 3) (N : X2Blocks s) (q : X2P × X2P × X2P) :
    x2Psi D s N (x2Swap01 X2P q) = x2Psi D s N q :=
  x2_kron3_mulVec_perm _ _ _ _ (x2_kron3_apply_swap01 _) (x2Phi_swap01 D s N) q

theorem x2Psi_cyc (D : X2Data) (s : Fin 3) (N : X2Blocks s) (q : X2P × X2P × X2P) :
    x2Psi D s N (x2Cyc X2P q) = x2Psi D s N q :=
  x2_kron3_mulVec_perm _ _ _ _ (x2_kron3_apply_cyc _) (x2Phi_cyc D s N) q

theorem x2Psi_asa (D : X2Data) (s : Fin 3) (N : X2Blocks s) (i₀ : Fin 231) (i₁ : Fin 282)
    (i₂ : Fin 231) :
    x2Psi D s N (Sum.inr i₀, Sum.inl i₁, Sum.inr i₂) = x2TransferA D s N i₁ i₀ i₂ := by
  rw [← x2Psi_swap01 D s N (Sum.inr i₀, Sum.inl i₁, Sum.inr i₂)]
  exact x2Psi_saa D s N i₁ i₀ i₂

theorem x2Psi_aas (D : X2Data) (s : Fin 3) (N : X2Blocks s) (i₀ i₁ : Fin 231) (i₂ : Fin 282) :
    x2Psi D s N (Sum.inr i₀, Sum.inr i₁, Sum.inl i₂) = x2TransferA D s N i₂ i₀ i₁ := by
  rw [← x2Psi_cyc D s N (Sum.inr i₀, Sum.inr i₁, Sum.inl i₂)]
  exact x2Psi_saa D s N i₂ i₀ i₁

/-- Odd transferred components vanish. -/
theorem x2Psi_odd (D : X2Data) (s : Fin 3) (N : X2Blocks s) (hN : ∀ k, (N k)ᵀ = N k)
    (p : X2P × X2P × X2P)
    (hp : x2ParitySign p.1 * x2ParitySign p.2.1 * x2ParitySign p.2.2 = -1) :
    x2Psi D s N p = 0 := by
  rw [x2Psi, x2_kron3_mulVec]
  apply Finset.sum_eq_zero
  intro q₀ _
  apply Finset.sum_eq_zero
  intro q₁ _
  apply Finset.sum_eq_zero
  intro q₂ _
  -- either a transfer factor vanishes (parity changes) or the component is odd
  by_cases hq : x2ParitySign q₀ * x2ParitySign q₁ * x2ParitySign q₂ = -1
  · rw [x2Phi_odd D s N hN (q₀, q₁, q₂) hq, mul_zero]
  · obtain ⟨p₀, p₁, p₂⟩ := p
    dsimp only at hp ⊢
    have key : ∀ (a b : X2P), x2ParitySign a ≠ x2ParitySign b →
        x2ParityTransfer D s a b = 0 := by
      intro a b hab
      cases a <;> cases b <;> simp [x2ParitySign] at hab <;> rfl
    by_cases h0 : x2ParitySign p₀ = x2ParitySign q₀
    · by_cases h1 : x2ParitySign p₁ = x2ParitySign q₁
      · have h2 : x2ParitySign p₂ ≠ x2ParitySign q₂ := by
          intro h2
          apply hq
          rw [← h0, ← h1, ← h2]
          exact hp
        rw [key p₂ q₂ h2, mul_zero, zero_mul]
      · rw [key p₁ q₁ h1, mul_zero, zero_mul, zero_mul]
    · rw [key p₀ q₀ h0, zero_mul, zero_mul, zero_mul]

theorem x2Psi_lla (D : X2Data) (s : Fin 3) (N : X2Blocks s) (hN : ∀ k, (N k)ᵀ = N k)
    (a b : Fin 282) (c : Fin 231) : x2Psi D s N (Sum.inl a, Sum.inl b, Sum.inr c) = 0 :=
  x2Psi_odd D s N hN _ (by norm_num [x2ParitySign])

theorem x2Psi_lal (D : X2Data) (s : Fin 3) (N : X2Blocks s) (hN : ∀ k, (N k)ᵀ = N k)
    (a : Fin 282) (b : Fin 231) (c : Fin 282) :
    x2Psi D s N (Sum.inl a, Sum.inr b, Sum.inl c) = 0 :=
  x2Psi_odd D s N hN _ (by norm_num [x2ParitySign])

theorem x2Psi_all (D : X2Data) (s : Fin 3) (N : X2Blocks s) (hN : ∀ k, (N k)ᵀ = N k)
    (a : Fin 231) (b c : Fin 282) : x2Psi D s N (Sum.inr a, Sum.inl b, Sum.inl c) = 0 :=
  x2Psi_odd D s N hN _ (by norm_num [x2ParitySign])

theorem x2Psi_aaa (D : X2Data) (s : Fin 3) (N : X2Blocks s) (hN : ∀ k, (N k)ᵀ = N k)
    (a b c : Fin 231) : x2Psi D s N (Sum.inr a, Sum.inr b, Sum.inr c) = 0 :=
  x2Psi_odd D s N hN _ (by norm_num [x2ParitySign])

/-! ## Reading the transferred tensor in unit coordinates -/

theorem x2Expand_inl (u : X2U 0) (l : Fin 282) :
    x2Expand 0 u (Sum.inl l) = if x2SIdx 0 u.1 u.2.1 u.2.2 = l then 1 else 0 := rfl

theorem x2Expand_inr (u : X2U 0) (l : Fin 231) :
    x2Expand 0 u (Sum.inr l) = if x2AIdx 0 u.1 u.2.1 u.2.2 = l then x2Sgn u.2.1 u.2.2 else 0 := rfl

/-- One site of the expansion: a sum over parity coordinates collapses to the label of `u`. -/
theorem x2_sum_expand (u : X2U 0) (f : X2P → ℚ) :
    ∑ p : X2P, x2Expand 0 u p * f p =
      f (Sum.inl (x2SIdx 0 u.1 u.2.1 u.2.2)) +
        x2Sgn u.2.1 u.2.2 * f (Sum.inr (x2AIdx 0 u.1 u.2.1 u.2.2)) := by
  rw [Fintype.sum_sum_type]
  simp only [x2Expand_inl, x2Expand_inr, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

theorem x2RawH_eq_unitTransfer_aux (D : X2Data) (s : Fin 3) (N : X2Blocks s)
    (hN : ∀ k, (N k)ᵀ = N k) (b : x2Key 0) (x y : x2Amb 0 b) :
    x2RawH (x2TransferS D s N) (x2TransferA D s N) b x y =
      ((x2Expand 0 ⊗ₖ (x2Expand 0 ⊗ₖ x2Expand 0)) *ᵥ x2Psi D s N)
        (⟨x2KeyTypes 0 b 0, (x.1, y.1)⟩, ⟨x2KeyTypes 0 b 1, (x.2.1, y.2.1)⟩,
          ⟨x2KeyTypes 0 b 2, (x.2.2, y.2.2)⟩) := by
  rw [x2_kron3_mulVec]
  simp only
  -- collapse the three expansion sums (innermost first)
  have inner : ∀ p₀ p₁ : X2P,
      ∑ p₂ : X2P, x2Expand 0 ⟨x2KeyTypes 0 b 0, (x.1, y.1)⟩ p₀ *
          x2Expand 0 ⟨x2KeyTypes 0 b 1, (x.2.1, y.2.1)⟩ p₁ *
          x2Expand 0 ⟨x2KeyTypes 0 b 2, (x.2.2, y.2.2)⟩ p₂ * x2Psi D s N (p₀, p₁, p₂) =
        x2Expand 0 ⟨x2KeyTypes 0 b 0, (x.1, y.1)⟩ p₀ *
          x2Expand 0 ⟨x2KeyTypes 0 b 1, (x.2.1, y.2.1)⟩ p₁ *
          (x2Psi D s N (p₀, p₁, Sum.inl (x2SIdx 0 (x2KeyTypes 0 b 2) x.2.2 y.2.2)) +
            x2Sgn x.2.2 y.2.2 *
              x2Psi D s N (p₀, p₁, Sum.inr (x2AIdx 0 (x2KeyTypes 0 b 2) x.2.2 y.2.2))) := by
    intro p₀ p₁
    have h := x2_sum_expand ⟨x2KeyTypes 0 b 2, (x.2.2, y.2.2)⟩ (fun p₂ => x2Psi D s N (p₀, p₁, p₂))
    simp only at h
    rw [← h, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p₂ _
    ring
  simp only [inner]
  have middle : ∀ p₀ : X2P,
      ∑ p₁ : X2P, x2Expand 0 ⟨x2KeyTypes 0 b 0, (x.1, y.1)⟩ p₀ *
          x2Expand 0 ⟨x2KeyTypes 0 b 1, (x.2.1, y.2.1)⟩ p₁ *
          (x2Psi D s N (p₀, p₁, Sum.inl (x2SIdx 0 (x2KeyTypes 0 b 2) x.2.2 y.2.2)) +
            x2Sgn x.2.2 y.2.2 *
              x2Psi D s N (p₀, p₁, Sum.inr (x2AIdx 0 (x2KeyTypes 0 b 2) x.2.2 y.2.2))) =
        x2Expand 0 ⟨x2KeyTypes 0 b 0, (x.1, y.1)⟩ p₀ *
          ((x2Psi D s N (p₀, Sum.inl (x2SIdx 0 (x2KeyTypes 0 b 1) x.2.1 y.2.1),
              Sum.inl (x2SIdx 0 (x2KeyTypes 0 b 2) x.2.2 y.2.2)) +
            x2Sgn x.2.2 y.2.2 *
              x2Psi D s N (p₀, Sum.inl (x2SIdx 0 (x2KeyTypes 0 b 1) x.2.1 y.2.1),
                Sum.inr (x2AIdx 0 (x2KeyTypes 0 b 2) x.2.2 y.2.2))) +
           x2Sgn x.2.1 y.2.1 *
            (x2Psi D s N (p₀, Sum.inr (x2AIdx 0 (x2KeyTypes 0 b 1) x.2.1 y.2.1),
                Sum.inl (x2SIdx 0 (x2KeyTypes 0 b 2) x.2.2 y.2.2)) +
              x2Sgn x.2.2 y.2.2 *
                x2Psi D s N (p₀, Sum.inr (x2AIdx 0 (x2KeyTypes 0 b 1) x.2.1 y.2.1),
                  Sum.inr (x2AIdx 0 (x2KeyTypes 0 b 2) x.2.2 y.2.2)))) := by
    intro p₀
    have h := x2_sum_expand ⟨x2KeyTypes 0 b 1, (x.2.1, y.2.1)⟩ (fun p₁ =>
      x2Psi D s N (p₀, p₁, Sum.inl (x2SIdx 0 (x2KeyTypes 0 b 2) x.2.2 y.2.2)) +
        x2Sgn x.2.2 y.2.2 *
          x2Psi D s N (p₀, p₁, Sum.inr (x2AIdx 0 (x2KeyTypes 0 b 2) x.2.2 y.2.2)))
    simp only at h
    rw [← h, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p₁ _
    ring
  simp only [middle]
  rw [x2_sum_expand ⟨x2KeyTypes 0 b 0, (x.1, y.1)⟩]
  simp only
  -- odd components vanish; even ones are the transferred tensors
  rw [x2Psi_lla D s N hN, x2Psi_lal D s N hN, x2Psi_all D s N hN, x2Psi_aaa D s N hN,
    x2Psi_sss, x2Psi_saa, x2Psi_asa, x2Psi_aas]
  simp only [x2RawH, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- MAIN: the reduced transfer of `CertificateX2Reduced` is the unit-coordinate transfer
`(Q_s ⊗ Q_s ⊗ Q_s)` of the source tensor, read at the h-block's unit coordinates. -/
theorem x2RawH_eq_unitTransfer (D : X2Data) (s : Fin 3) (N : X2Blocks s)
    (hN : ∀ k, (N k)ᵀ = N k) (b : x2Key 0) (x y : x2Amb 0 b) :
    x2RawH (x2TransferS D s N) (x2TransferA D s N) b x y =
      ((x2Qu D s ⊗ₖ (x2Qu D s ⊗ₖ x2Qu D s)) *ᵥ x2FmVec D s N)
        (⟨x2KeyTypes 0 b 0, (x.1, y.1)⟩, ⟨x2KeyTypes 0 b 1, (x.2.1, y.2.1)⟩,
          ⟨x2KeyTypes 0 b 2, (x.2.2, y.2.2)⟩) := by
  rw [x2RawH_eq_unitTransfer_aux D s N hN, x2Qu, x2_kron3_mul, x2_kron3_mul,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rfl

end ThreeCopyQutritWerner

end
