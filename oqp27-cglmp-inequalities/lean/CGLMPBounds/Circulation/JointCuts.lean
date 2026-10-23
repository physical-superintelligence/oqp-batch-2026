module

public import CGLMPBounds.Circulation.JointDecomposition
public import CGLMPBounds.Circulation.ScalarCuts
public import CGLMPBounds.Defs.JointCutSpace

@[expose] public section


/-!
# The actual common scalar cut spaces span at equality

On a nonzero joint eigenspace of spectral projections, each PVM has exactly
one eigenvalue one and all other eigenvalues zero. The forbidden products
give the ordered scalar constraints, so the previous cut classification
applies to the original fourth-root matrices.
-/

open Matrix

namespace CGLMPBounds
noncomputable section

/-- A common eigenvector of every outcome of a PVM has one deterministic
outcome. Eigenvalues are derived from the actual projections. -/
theorem IsPVM.joint_eigenvalues_deterministic {r : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] {P : α → Matrix (Fin r) (Fin r) ℂ}
    (hP : IsPVM P) (χ : α → ℂ) {x : EuclideanSpace ℂ (Fin r)} (hx : x ≠ 0)
    (he : ∀ a, (P a).toEuclideanLin x = χ a • x) :
    ∃ a, χ a = 1 ∧ ∀ b, b ≠ a → χ b = 0 := by
  classical
  have hsum : (∑ a, χ a) • x = x := by
    have hs := congrArg (fun M : Matrix (Fin r) (Fin r) ℂ => M.toEuclideanLin x)
      hP.sum_eq_one
    simpa only [map_sum, LinearMap.sum_apply, he, ← Finset.sum_smul,
      Matrix.toEuclideanLin, Matrix.toLpLin_one, LinearMap.id_apply] using hs
  have hex : ∃ a, χ a ≠ 0 := by
    by_contra hn
    push_neg at hn
    have hz : ∑ a, χ a = 0 := Finset.sum_eq_zero (fun a _ => hn a)
    rw [hz, zero_smul] at hsum
    exact hx hsum.symm
  obtain ⟨a, ha⟩ := hex
  have hsq := congrArg (fun M : Matrix (Fin r) (Fin r) ℂ => M.toEuclideanLin x)
    (hP.mul_self a)
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, LinearMap.comp_apply] at hsq
  change (P a).toEuclideanLin ((P a).toEuclideanLin x) = (P a).toEuclideanLin x at hsq
  rw [he a, map_smul, he a, smul_smul] at hsq
  have hscalar : χ a * χ a = χ a := smul_left_injective ℂ hx hsq
  have hfactor : χ a * (χ a - 1) = 0 := by rw [mul_sub, hscalar, mul_one, sub_self]
  have ha1 : χ a = 1 := sub_eq_zero.mp ((_root_.mul_eq_zero.mp hfactor).resolve_left ha)
  refine ⟨a, ha1, ?_⟩
  intro b hba
  have hp := congrArg (fun M : Matrix (Fin r) (Fin r) ℂ => M.toEuclideanLin x)
    (hP.mul_eq_zero (Ne.symm hba))
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, LinearMap.comp_apply,
    map_zero, LinearMap.zero_apply] at hp
  change (P b).toEuclideanLin ((P a).toEuclideanLin x) = 0 at hp
  rw [he a, ha1, one_smul, he b] at hp
  exact (smul_eq_zero.mp hp).resolve_right hx

namespace Circulation
variable {d r : ℕ}

lemma spectral_selected_root_action (V : Mat r) (a : Fin 4)
    (x : EuclideanSpace ℂ (Fin r))
    (ha : (spectral V a).toEuclideanLin x = x)
    (hb : ∀ b, b ≠ a → (spectral V b).toEuclideanLin x = 0) :
    V.toEuclideanLin x = Complex.I ^ a.val • x := by
  rw [← root_spectral V]
  simp only [root, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
  rw [Finset.sum_eq_single a]
  · rw [ha]
  · intro b _ hba
    rw [hb b hba, smul_zero]
  · simp

lemma spectral_selected_labels_allowed [NeZero r] (V : Fin d → Mat r)
    (hunit : ∀ j, (V j)ᴴ * V j = 1) (hfour : ∀ j, V j ^ 4 = 1)
    (hzero : ∀ i j, i < j → forbidden (V i) (V j) = 0)
    (v : Fin d → Fin 4) {x : EuclideanSpace ℂ (Fin r)} (hx : x ≠ 0)
    (he : ∀ j, (spectral (V j) (v j)).toEuclideanLin x = x) :
    ∀ i j, i < j → v j = v i ∨ v j = v i + 3 := by
  intro i j hij
  by_contra hn
  have hcases : v j = v i + 1 ∨ v j = v i + 2 :=
    (show ∀ a b : Fin 4, ¬ (b = a ∨ b = a + 3) → b = a + 1 ∨ b = a + 2 by decide)
      (v i) (v j) hn
  obtain ⟨h1, h2⟩ := forbidden_root_eq_zero_overlaps (spectral (V i)) (spectral (V j))
    (spectral_isPVM (hunit i) (hfour i)) (spectral_isPVM (hunit j) (hfour j))
    (by simpa only [root_spectral] using hzero i j hij)
  have hp : spectral (V i) (v i) * spectral (V j) (v j) = 0 := by
    rcases hcases with hv | hv
    · simpa only [hv] using h1 (v i)
    · simpa only [hv] using h2 (v i)
  have hp' := congrArg (fun M : Mat r => M.toEuclideanLin x) hp
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, LinearMap.comp_apply,
    map_zero, LinearMap.zero_apply] at hp'
  change (spectral (V i) (v i)).toEuclideanLin
    ((spectral (V j) (v j)).toEuclideanLin x) = 0 at hp'
  rw [he j, he i] at hp'
  exact hx hp'

/-- On every nonzero joint projection eigenspace, the original tuple has
one of the literal scalar cut actions. -/
theorem joint_spectral_space_le_cut [NeZero d] [NeZero r] (V : Fin d → Mat r)
    (hunit : ∀ j, (V j)ᴴ * V j = 1) (hfour : ∀ j, V j ^ 4 = 1)
    (hzero : ∀ i j, i < j → forbidden (V i) (V j) = 0)
    (χ : Fin d × Fin 4 → ℂ)
    (hne : (⨅ ia : Fin d × Fin 4,
      Module.End.eigenspace (spectral (V ia.1) ia.2).toEuclideanLin (χ ia)) ≠ ⊥) :
    ∃ a j₀, (⨅ ia : Fin d × Fin 4,
      Module.End.eigenspace (spectral (V ia.1) ia.2).toEuclideanLin (χ ia)) ≤
        fourthRootCutSpace V a j₀ := by
  classical
  let J : Submodule ℂ (EuclideanSpace ℂ (Fin r)) :=
    ⨅ ia : Fin d × Fin 4,
      Module.End.eigenspace (spectral (V ia.1) ia.2).toEuclideanLin (χ ia)
  have hJ : J ≠ ⊥ := hne
  obtain ⟨x, hxJ, hx⟩ := (Submodule.ne_bot_iff J).mp hJ
  have he (j : Fin d) (a : Fin 4) :
      (spectral (V j) a).toEuclideanLin x = χ (j, a) • x :=
    Module.End.mem_eigenspace_iff.mp (((Submodule.mem_iInf _).mp hxJ) (j, a))
  have hsel (j : Fin d) : ∃ a, χ (j, a) = 1 ∧ ∀ b, b ≠ a → χ (j, b) = 0 :=
    (spectral_isPVM (hunit j) (hfour j)).joint_eigenvalues_deterministic
      (fun a => χ (j, a)) hx (he j)
  choose v hv using hsel
  have hvx (j : Fin d) : (spectral (V j) (v j)).toEuclideanLin x = x := by
    rw [he j (v j), (hv j).1, one_smul]
  obtain ⟨a, j₀, hcut⟩ := scalar_labels_are_cut v
    (spectral_selected_labels_allowed V hunit hfour hzero v hx hvx)
  refine ⟨a, j₀, ?_⟩
  intro w hw
  apply (Submodule.mem_iInf _).mpr
  intro j
  apply Module.End.mem_eigenspace_iff.mpr
  have hw' (b : Fin 4) : (spectral (V j) b).toEuclideanLin w = χ (j, b) • w :=
    Module.End.mem_eigenspace_iff.mp (((Submodule.mem_iInf _).mp hw) (j, b))
  have hroot := spectral_selected_root_action (V j) (v j) w
    (by rw [hw' (v j), (hv j).1, one_smul])
    (fun b hb => by rw [hw' b, (hv j).2 b hb, zero_smul])
  simpa only [hcut] using hroot

/-- The original Hilbert space is spanned by the actual scalar cut spaces.
This proves the simultaneous scalar part of E.1 without assuming a basis. -/
theorem fourth_root_cut_spaces_span [NeZero d] [NeZero r] (V : Fin d → Mat r)
    (hunit : ∀ j, (V j)ᴴ * V j = 1) (hfour : ∀ j, V j ^ 4 = 1)
    (hzero : ∀ i j, i < j → forbidden (V i) (V j) = 0) :
    (⨆ a : Fin 4, ⨆ j₀ : Fin d, fourthRootCutSpace V a j₀) = ⊤ := by
  apply top_le_iff.mp
  rw [← fourth_root_joint_eigenspaces_span V hunit hfour hzero]
  apply iSup_le
  intro χ
  by_cases hJ : (⨅ ia : Fin d × Fin 4,
      Module.End.eigenspace (spectral (V ia.1) ia.2).toEuclideanLin (χ ia)) = ⊥
  · rw [hJ]
    exact bot_le
  · obtain ⟨a, j₀, hle⟩ := joint_spectral_space_le_cut V hunit hfour hzero χ hJ
    exact hle.trans (le_iSup_of_le a (le_iSup_of_le j₀ le_rfl))

end Circulation
end
end CGLMPBounds
