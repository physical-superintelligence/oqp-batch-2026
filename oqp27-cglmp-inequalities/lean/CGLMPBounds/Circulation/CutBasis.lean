module

public import CGLMPBounds.Circulation.JointCutZero

@[expose] public section


/-!
# An orthonormal basis on which the original tuple acts by scalar cuts

The orthonormal basis is subordinate to the joint spectral eigenspaces, obtained
from Mathlib's internal orthogonal direct sum construction. Its nonzero vectors
therefore lie in literal cut spaces. No simultaneous eigenbasis is assumed.
-/

namespace CGLMPBounds.Circulation
noncomputable section
open scoped Matrix
variable {d r : ℕ} [NeZero d] [NeZero r]

/-- At zero forbidden mass the original tuple has an actual orthonormal scalar-cut basis. -/
theorem exists_orthonormal_cut_basis (V : Fin d → Mat r)
    (hunit : ∀ j, (V j)ᴴ * V j = 1) (hfour : ∀ j, V j ^ 4 = 1)
    (hzero : scalarForbiddenTotal V = 0) :
    ∃ (b : OrthonormalBasis (Fin r) ℂ (EuclideanSpace ℂ (Fin r)))
      (a : Fin r → Fin 4) (j₀ : Fin r → Fin d),
      ∀ k j, (V j).toEuclideanLin (b k) =
        Complex.I ^ (fourthRootCutLabels (a k) (j₀ k) j).val • b k := by
  classical
  let J : (Fin d × Fin 4 → ℂ) → Submodule ℂ (EuclideanSpace ℂ (Fin r)) :=
    fun χ => ⨅ ia, Module.End.eigenspace (spectral (V ia.1) ia.2).toEuclideanLin (χ ia)
  have hsym (ia : Fin d × Fin 4) : (spectral (V ia.1) ia.2).toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr
      ((spectral_isPVM (hunit ia.1) (hfour ia.1)).isHermitian ia.2)
  have horth : OrthogonalFamily ℂ (fun χ => J χ) (fun χ => (J χ).subtypeₗᵢ) :=
    LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces hsym
  have hforbid := forbidden_zero_of_total_zero V hunit hfour hzero
  have hspan : (⨆ χ, J χ) = ⊤ := fourth_root_joint_eigenspaces_span V hunit hfour hforbid
  have hint : DirectSum.IsInternal J := horth.isInternal_iff.mpr (by
    rw [hspan, Submodule.top_orthogonal_eq_bot])
  let I := {χ : Fin d × Fin 4 → ℂ // J χ ≠ ⊥}
  letI : Fintype I := hint.submodule_iSupIndep.fintypeNeBotOfFiniteDimensional
  let J' : I → Submodule ℂ (EuclideanSpace ℂ (Fin r)) := fun χ => J χ.val
  have horth' : OrthogonalFamily ℂ (fun χ => J' χ) (fun χ => (J' χ).subtypeₗᵢ) := by
    intro i j hij v w
    exact horth (Subtype.val_injective.ne hij) v w
  have hspan' : (⨆ χ : I, J' χ) = ⊤ := by
    apply top_unique
    rw [← hspan]
    apply iSup_le
    intro χ
    by_cases hχ : J χ = ⊥
    · simp only [hχ, bot_le]
    · exact le_iSup J' (⟨χ, hχ⟩ : I)
  have hint' : DirectSum.IsInternal J' := horth'.isInternal_iff.mpr (by
    rw [hspan', Submodule.top_orthogonal_eq_bot])
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ (Fin r)) = r := by simp
  let b := hint'.subordinateOrthonormalBasis hdim horth'
  let χ (k : Fin r) := (hint'.subordinateOrthonormalBasisIndex hdim k horth').val
  have hb (k : Fin r) : b k ∈ J (χ k) :=
    hint'.subordinateOrthonormalBasis_subordinate hdim k horth'
  have hc (k : Fin r) : ∃ a j₀, b k ∈ fourthRootCutSpace V a j₀ := by
    have hne : J (χ k) ≠ ⊥ := by
      intro hbot
      have hz : b k = 0 := by simpa only [hbot, Submodule.mem_bot] using hb k
      have hn := b.orthonormal.1 k
      rw [hz, norm_zero] at hn
      exact zero_ne_one hn
    obtain ⟨a, j₀, hj⟩ := joint_spectral_space_le_cut V hunit hfour hforbid (χ k) hne
    exact ⟨a, j₀, hj (hb k)⟩
  choose a j₀ hcut using hc
  refine ⟨b, a, j₀, ?_⟩
  intro k j
  exact Module.End.mem_eigenspace_iff.mp (((Submodule.mem_iInf _).mp (hcut k)) j)

end
end CGLMPBounds.Circulation
