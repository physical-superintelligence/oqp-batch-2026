module

public import ThreeCopyQutritWerner.CertificateX2BridgeSorted

@[expose] public section


/-!
# T2.1a from the finite facts, the source blocks and the reduced residuals

`x2_qutritEndpointInequality_of_facts`: T2.1a follows from

* `X2SiteFacts D wU1 wU2` (per-site unit, dictionary and target identities),
* `X2KeyFrameFacts D` (per-key image facts in frame coordinates),
* positive semidefinite source blocks `Nm`, `Na`,
* positive semidefinite reduced residual blocks `x2Residual D Nm Na b` for all 122 h keys,
* positivity of the h-side form on the seven triples `(a, a, a)` of three equal types
  (`htriple`; the S3-isotypic parts with the standard split are the one structural piece not
  yet written).

The sorted type triples with at most two equal sites are handled by keyed parts
(`x2_hform_distinct`, `x2_hform_pair01`, `x2_hform_pair12`), the other triples by S3 covariance
(`x2_hres_of_sorted`).
-/

noncomputable section

open scoped BigOperators Matrix Kronecker ComplexOrder

namespace ThreeCopyQutritWerner

/-- The key of a type triple and kind, if any. -/
@[irreducible] def x2KeyOf (τ : Fin 7 × Fin 7 × Fin 7) (k : ℕ) : Option (x2Key 0) :=
  if h : ∃ b : x2Key 0, x2KeyTau b = τ ∧ x2KeyKind 0 b = k then some (Classical.choose h) else none

theorem x2KeyOf_some {τ : Fin 7 × Fin 7 × Fin 7} {k : ℕ} {b : x2Key 0}
    (h : x2KeyOf τ k = some b) : x2KeyTau b = τ ∧ x2KeyKind 0 b = k := by
  unfold x2KeyOf at h
  by_cases hex : ∃ b : x2Key 0, x2KeyTau b = τ ∧ x2KeyKind 0 b = k
  · rw [dif_pos hex] at h
    rw [← Option.some_injective _ h]
    exact Classical.choose_spec hex
  · rw [dif_neg hex] at h
    exact absurd h (by simp)

theorem x2KeyOf_none {τ : Fin 7 × Fin 7 × Fin 7} {k : ℕ} (h : x2KeyOf τ k = none) :
    ∀ b : x2Key 0, x2KeyTau b = τ → x2KeyKind 0 b ≠ k := by
  unfold x2KeyOf at h
  by_cases hex : ∃ b : x2Key 0, x2KeyTau b = τ ∧ x2KeyKind 0 b = k
  · rw [dif_pos hex] at h
    exact absurd h (by simp)
  · intro b hb hk
    exact hex ⟨b, hb, hk⟩

/-- Keys on triples with at most two equal sites have degree one (finite check). -/
theorem x2_keyDegree_one : ∀ b : x2Key 0,
    ¬ ((x2KeyTau b).1 = (x2KeyTau b).2.1 ∧ (x2KeyTau b).2.1 = (x2KeyTau b).2.2) →
      x2KeyDegree 0 b = 1 := by
  decide +kernel

/-- The key facts transported to the image read at an equal type triple. -/
theorem x2_keyFacts_at (D : X2Data) (hK : X2KeyFrameFacts D) (τ : Fin 7 × Fin 7 × Fin 7)
    (b : x2Key 0) (hb : x2KeyTau b = τ) :
    certificateCarrierJointAction0 τ * x2ImageAt D τ b = x2ImageAt D τ b ∧
      x2KindProjFrame τ (x2KeyKind 0 b) * x2ImageAt D τ b = x2ImageAt D τ b ∧
      ((x2ImageAt D τ b)ᴴ * certificateThreeSiteFrameSystem0.metric τ * x2ImageAt D τ b).det ≠ 0 ∧
      (certificateCarrierJointAction0 τ * x2KindProjFrame τ (x2KeyKind 0 b)).trace =
        ((x2KeyDegree 0 b * x2KeySize 0 b : ℕ) : ℂ) := by
  subst hb
  rw [x2ImageAt_key]
  exact ⟨hK.carrier_fix b, hK.kind_fix b, hK.metric_det b, hK.trace_count b⟩

theorem x2KindProjFrame_distinct (a b c : Fin 7) (hab : a ≠ b) (hbc : b ≠ c) (k : ℕ) :
    x2KindProjFrame (a, b, c) k = 1 := by
  unfold x2KindProjFrame
  simp [hab, hbc]

/-- A sorted type triple with at most two equal sites. -/
theorem x2_hform_sorted (D : X2Data) (wU1 : X2U 1 → Equiv.Perm (Fin 6) → ℂ)
    (wU2 : X2U 2 → Equiv.Perm (Fin 6) → ℂ) (hS : X2SiteFacts D wU1 wU2)
    (hK : X2KeyFrameFacts D) (Nm : X2Blocks 1) (Na : X2Blocks 2)
    (hNm : ∀ k, (x2Complex (Nm k)).PosSemidef) (hNa : ∀ k, (x2Complex (Na k)).PosSemidef)
    (hres : ∀ b, (x2Complex (x2Residual D Nm Na b)).PosSemidef)
    (htriple : ∀ a : Fin 7, (x2HForm D Nm Na (a, a, a)).PosSemidef)
    (τ : Fin 7 × Fin 7 × Fin 7) (h01 : τ.1 ≤ τ.2.1) (h12 : τ.2.1 ≤ τ.2.2) :
    (x2HForm D Nm Na τ).PosSemidef := by
  obtain ⟨a, b, c⟩ := τ
  simp only at h01 h12
  by_cases hab : a = b
  · subst hab
    by_cases hac : a = c
    · subst hac
      exact htriple a
    · -- (a, a, c) with a ≠ c
      refine x2_hform_pair01 D hS.target Nm Na hNm hNa a c hac
        (fun k => x2KeyOf (a, a, c) (if k then 1 else 0))
        (fun k b h => (x2KeyOf_some h).1) ?_ ?_ ?_ ?_ hres
      · intro k b h
        exact (x2_keyFacts_at D hK _ b (x2KeyOf_some h).1).1
      · intro k b h
        have hf := (x2_keyFacts_at D hK _ b (x2KeyOf_some h).1).2.1
        rwa [(x2KeyOf_some h).2] at hf
      · intro k b h
        exact (x2_keyFacts_at D hK _ b (x2KeyOf_some h).1).2.2.1
      · intro k
        try dsimp only
        generalize ho : x2KeyOf (a, a, c) (if k then 1 else 0) = o
        cases o with
        | none =>
            have h0 := hK.empty_kinds (a, a, c) le_rfl (le_of_lt (lt_of_le_of_ne h12 hac))
              (if k then 1 else 0) (by cases k <;> simp [x2NumKinds, hac]) (x2KeyOf_none ho)
            rw [h0]
            simp [x2PartSize]
        | some b =>
            obtain ⟨hbτ, hbk⟩ := x2KeyOf_some ho
            have ht := (x2_keyFacts_at D hK _ b hbτ).2.2.2
            rw [hbk] at ht
            rw [ht, x2_keyDegree_one b (by rw [hbτ]; simp [hac]), one_mul]
            rfl
  · by_cases hbc : b = c
    · subst hbc
      -- (a, b, b) with a ≠ b
      refine x2_hform_pair12 D hS.target Nm Na hNm hNa a b hab
        (fun k => x2KeyOf (a, b, b) (if k then 1 else 0))
        (fun k b' h => (x2KeyOf_some h).1) ?_ ?_ ?_ ?_ hres
      · intro k b' h
        exact (x2_keyFacts_at D hK _ b' (x2KeyOf_some h).1).1
      · intro k b' h
        have hf := (x2_keyFacts_at D hK _ b' (x2KeyOf_some h).1).2.1
        rwa [(x2KeyOf_some h).2] at hf
      · intro k b' h
        exact (x2_keyFacts_at D hK _ b' (x2KeyOf_some h).1).2.2.1
      · intro k
        try dsimp only
        generalize ho : x2KeyOf (a, b, b) (if k then 1 else 0) = o
        cases o with
        | none =>
            have h0 := hK.empty_kinds (a, b, b) h01 le_rfl
              (if k then 1 else 0) (by cases k <;> simp [x2NumKinds, hab]) (x2KeyOf_none ho)
            rw [h0]
            simp [x2PartSize]
        | some b' =>
            obtain ⟨hbτ, hbk⟩ := x2KeyOf_some ho
            have ht := (x2_keyFacts_at D hK _ b' hbτ).2.2.2
            rw [hbk] at ht
            rw [ht, x2_keyDegree_one b' (by rw [hbτ]; simp [hab]), one_mul]
            rfl
    · -- three distinct types
      have hP := x2KindProjFrame_distinct a b c hab hbc
      refine x2_hform_distinct D hS.target Nm Na hNm hNa (a, b, c) (x2KeyOf (a, b, c) 0)
        (fun b' h => (x2KeyOf_some h).1) ?_ ?_ ?_ hres
      · intro b' h
        exact (x2_keyFacts_at D hK _ b' (x2KeyOf_some h).1).1
      · intro b' h
        exact (x2_keyFacts_at D hK _ b' (x2KeyOf_some h).1).2.2.1
      · generalize ho : x2KeyOf (a, b, c) 0 = o
        cases o with
        | none =>
            have h0 := hK.empty_kinds (a, b, c) h01 h12 0 (by simp [x2NumKinds, hab, hbc])
              (x2KeyOf_none ho)
            rw [hP, Matrix.mul_one] at h0
            rw [h0]
            simp [x2PartSize]
        | some b' =>
            obtain ⟨hbτ, hbk⟩ := x2KeyOf_some ho
            have ht := (x2_keyFacts_at D hK _ b' hbτ).2.2.2
            rw [hbk, hP, Matrix.mul_one] at ht
            rw [ht, x2_keyDegree_one b' (by rw [hbτ]; simp [hab]), one_mul]
            rfl

/-- MAIN THEOREM OF The bridge: T2.1a from the finite facts, positive source blocks,
positive reduced residuals, and positivity on the seven triples of three equal types. -/
theorem x2_qutritEndpointInequality_of_facts (D : X2Data)
    (wU1 : X2U 1 → Equiv.Perm (Fin 6) → ℂ) (wU2 : X2U 2 → Equiv.Perm (Fin 6) → ℂ)
    (hS : X2SiteFacts D wU1 wU2) (hK : X2KeyFrameFacts D) (Nm : X2Blocks 1) (Na : X2Blocks 2)
    (hNm : ∀ k, (x2Complex (Nm k)).PosSemidef) (hNa : ∀ k, (x2Complex (Na k)).PosSemidef)
    (hres : ∀ b, (x2Complex (x2Residual D Nm Na b)).PosSemidef)
    (htriple : ∀ a : Fin 7, (x2HForm D Nm Na (a, a, a)).PosSemidef) :
    QutritEndpointInequality :=
  x2_qutritEndpointInequality_of_siteFacts D wU1 wU2 hS Nm Na hNm hNa
    (fun τ => x2_hres_of_sorted D Nm Na
      (fun σ h1 h2 => x2_hform_sorted D wU1 wU2 hS hK Nm Na hNm hNa hres htriple σ h1 h2) τ)

end ThreeCopyQutritWerner

end
