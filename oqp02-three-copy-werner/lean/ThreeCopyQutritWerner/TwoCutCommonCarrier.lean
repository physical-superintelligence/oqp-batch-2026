module

public import ThreeCopyQutritWerner.TwoCutCarrierPullback

@[expose] public section


/-!
# Unconditional common binary carrier of every qutrit two-site cut zero

Constructed output planes give one missing coordinate at each site. Each
coordinate either also vanishes on input or forces a single local output
direction, already classified as a ket-bra projection tensor. Both branches
give actual common frames, which are restored to the original coordinates.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- The single-output-direction branch has its actual common binary carrier. -/
theorem twoCut_single_output_exists_binary_carrier
    (C : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) (hC : C.rank ≤ 2)
    (hz : cutForm C = 0) (hne : C ≠ 0) (i₀ : Fin 3) (x : Fin 3 → ℂ)
    (hx : x i₀ = 1) (hfactor : ∀ i r q, C (i, r) q = x i * C (i₀, r) q) :
    ∃ J₁ J₂ : Matrix (Fin 3) (Fin 2) ℂ,
      ∃ K : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
      J₁ᴴ * J₁ = 1 ∧ J₂ᴴ * J₂ = 1 ∧
        C = (J₁ ⊗ₖ J₂) * K * (J₁ ⊗ₖ J₂)ᴴ := by
  obtain ⟨u, v, P, hu, hv, hP, hPP, hr, he⟩ :=
    cutForm_zero_single_output_factor C hC hz hne i₀ x hx hfactor
  rw [he]
  exact twoCut_ketBra_tensor_exists_binary_carrier u v P hP hr.le

/-- Every original qutrit two-site cut zero of rank at most two has a
constructed common binary input/output carrier. Zero is included; no endpoint,
alignment, normal form or classification premise is supplied. -/
theorem cutForm_zero_exists_binary_carrier
    (C : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (hC : C.rank ≤ 2) (hz : cutForm C = 0) :
    ∃ J₁ J₂ : Matrix (Fin 3) (Fin 2) ℂ,
      ∃ K : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
      J₁ᴴ * J₁ = 1 ∧ J₂ᴴ * J₂ = 1 ∧
        C = (J₁ ⊗ₖ J₂) * K * (J₁ ⊗ₖ J₂)ᴴ := by
  by_cases hzero : C = 0
  · apply twoCut_aligned_coordinates_exists_binary_carrier C 0 0
    · intro i j q hij
      simp [hzero]
    · intro i j p hij
      simp [hzero]
  obtain ⟨U, V, a, b, hU, hV, hsupport⟩ := cutForm_zero_exists_output_planes C hC hz
  let W := U ⊗ₖ V
  let D := W * C * Wᴴ
  have hW : Wᴴ * W = 1 := kron_isometry U V hU hV
  have hdata := twoCut_local_conj_data U V hU hV C
  have hDr : D.rank ≤ 2 := hdata.1.trans_le hC
  have hDz : cutForm D = 0 := hdata.2.2.trans hz
  have hDne : D ≠ 0 := by
    intro he
    apply hzero
    have hr := twoCut_unitary_conj_recover W C hW
    change Wᴴ * D * W = C at hr
    simpa only [he, Matrix.mul_zero, Matrix.zero_mul] using hr.symm
  have hrow : ∀ i j q, i = a ∨ j = b → D (i, j) q = 0 := by
    intro i j q hij
    have hl : ∀ p, (W * C) (i, j) p = 0 := fun p => hsupport i j p hij
    change (W * C * Wᴴ) (i, j) q = 0
    rw [Matrix.mul_apply]
    simp only [hl, zero_mul, Finset.sum_const_zero]
  have hcarrier : ∃ J₁ J₂ : Matrix (Fin 3) (Fin 2) ℂ,
      ∃ K : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
      J₁ᴴ * J₁ = 1 ∧ J₂ᴴ * J₂ = 1 ∧ D = (J₁ ⊗ₖ J₂) * K * (J₁ ⊗ₖ J₂)ᴴ := by
    rcases cutForm_zero_missing_row_alignment_or_single_output D hDr hDz a
      (fun r q => hrow a r q (Or.inl rfl)) with hfirst | ⟨i₀, x, hx, hfactor⟩
    · have hs := twoCutSwap_data D
      have hSrow : ∀ r q, twoCutSwap D (b, r) q = 0 :=
        fun r q => hrow r b (q.2, q.1) (Or.inr rfl)
      rcases cutForm_zero_missing_row_alignment_or_single_output (twoCutSwap D)
        (hs.1.trans_le hDr) (hs.2.2.trans hDz) b hSrow with hsecond | ⟨i₀, x, hx, hfactor⟩
      · apply twoCut_aligned_coordinates_exists_binary_carrier D a b hrow
        intro i j p hij
        rcases hij with rfl | rfl
        · exact hfirst p j
        · exact hsecond (p.2, p.1) i
      · have hSne : twoCutSwap D ≠ 0 := by
          intro he
          apply hDne
          calc
            D = twoCutSwap (twoCutSwap D) := rfl
            _ = twoCutSwap 0 := congrArg twoCutSwap he
            _ = 0 := rfl
        obtain ⟨J₁, J₂, K, hJ₁, hJ₂, he⟩ :=
          twoCut_single_output_exists_binary_carrier (twoCutSwap D)
            (hs.1.trans_le hDr) (hs.2.2.trans hDz) hSne i₀ x hx hfactor
        exact twoCut_binary_carrier_of_swap D J₁ J₂ K hJ₁ hJ₂ he
    · exact twoCut_single_output_exists_binary_carrier D hDr hDz hDne i₀ x hx hfactor
  obtain ⟨J₁, J₂, K, hJ₁, hJ₂, he⟩ := hcarrier
  exact twoCut_binary_carrier_of_local_conj C U V hU hV J₁ J₂ K hJ₁ hJ₂ he

end ThreeCopyQutritWerner
