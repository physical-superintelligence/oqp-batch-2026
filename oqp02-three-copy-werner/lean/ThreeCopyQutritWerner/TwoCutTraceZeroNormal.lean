module

public import ThreeCopyQutritWerner.TwoCutQutritClassification
public import ThreeCopyQutritWerner.BinaryPartitionNormalize

@[expose] public section


/-!
# Trace-zero qutrit cut normal form and its original three-site tensor

The actual common carrier is constructed from the qutrit cut zero. Trace
zero then gives the exact binary B₂ form in that carrier. An arbitrary
rank-one first factor can be normalized with its full phase absorbed into
the cut factor, producing the family II without extra scale data.
-/

noncomputable section

open scoped Matrix Kronecker ComplexConjugate

namespace ThreeCopyQutritWerner

/-- Every actual normalized trace-zero qutrit cut zero has the literal
embedded B₂ form, with both physical frames constructed internally. -/
theorem qutritCut_trace_zero_normal_form
    (C : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (hr : C.rank ≤ 2) (hq : cutForm C = 0) (hN : frobSq C = 1) (ht : C.trace = 0) :
    ∃ (J₁ J₂ : Matrix (Fin 3) (Fin 2) ℂ)
      (U : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ),
      J₁ᴴ * J₁ = 1 ∧ J₂ᴴ * J₂ = 1 ∧ Uᴴ * U = 1 ∧
        C = (J₁ ⊗ₖ J₂) * binaryB₂ U * (J₁ ⊗ₖ J₂)ᴴ := by
  obtain ⟨J₁, J₂, K, hJ₁, hJ₂, he, hKr, hKn, hKq⟩ :=
    qutritCut_normalized_exists_binary_carrier C hr hq hN
  have hKt : K.trace = 0 := by
    rw [he, trace_conj_isometry _ (kron_isometry J₁ J₂ hJ₁ hJ₂)] at ht
    exact ht
  obtain ⟨U, hU, hK⟩ := binaryCut_trace_zero_normal_form K hKr hKn hKq hKt
  exact ⟨J₁, J₂, U, hJ₁, hJ₂, hU, by simpa only [hK] using he⟩

/-- The original rank and norm normalize an actual ket-bra tensor with a
trace-zero cut zero to family II. No normalization of its supplied factors
or binary-support hypothesis is required. -/
theorem isQutritZeroFamilyMember_of_trace_zero_cut_tensor
    (C : Matrix QutritSites QutritSites ℂ) (hC : C.rank ≤ 2) (hN : frobSq C = 1)
    (u v : Fin 3 → ℂ) (T : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (he : C = ketBra u v ⊗ₖ T) (hq : cutForm T = 0) (ht : T.trace = 0) :
    IsQutritZeroFamilyMember C := by
  obtain ⟨x, y, z, hx, hy, hnorm, hTn⟩ :=
    binaryPartition_normalize_ketBra_tensor u v T (he ▸ hN)
  have hxne : x ≠ 0 := by
    intro h
    simp [h, vecNormSq] at hx
  have hyne : (fun j => conj (y j)) ≠ (0 : Fin 3 → ℂ) := by
    intro h
    have hzero : y = 0 := by
      funext j
      have hj := congrArg conj (congrFun h j)
      simpa using hj
    simp [hzero, vecNormSq] at hy
  have hT : (z • T).rank ≤ 2 := by
    have hr := binaryPartition_rank_one_kronecker_rank x (fun j => conj (y j))
      hxne hyne (z • T)
    change (ketBra x y ⊗ₖ (z • T)).rank = (z • T).rank at hr
    exact hr.symm.trans_le (hnorm ▸ (he ▸ hC))
  have hTq : cutForm (z • T) = 0 := by rw [cutForm_smul, hq, mul_zero]
  have hTt : (z • T).trace = 0 := by rw [Matrix.trace_smul, ht, smul_zero]
  obtain ⟨J₁, J₂, U, hJ₁, hJ₂, hU, hform⟩ :=
    qutritCut_trace_zero_normal_form (z • T) hT hTq hTn hTt
  refine ⟨1, by norm_num, C, by simp, Or.inr (Or.inl ?_)⟩
  refine ⟨x, y, U, J₁, J₂, hx, hy, hU, hJ₁, hJ₂, Or.inl ?_⟩
  rw [he, hnorm, hform]
  rfl

end ThreeCopyQutritWerner
