module

public import ThreeCopyQutritWerner.TwoCutCoordinateCarrier
public import ThreeCopyQutritWerner.TwoCutTransport

@[expose] public section


/-!
# Swapping the two physical sites in the carrier argument

The swap is the literal tuple permutation on both original matrix indices.
It preserves the cut form and transports an actual binary carrier by swapping
its two local embeddings and the two coordinates of the compressed operator.
-/

noncomputable section

open scoped Matrix Kronecker

namespace ThreeCopyQutritWerner

def twoCutSwap {L R : Type*} (C : Matrix (L × R) (L × R) ℂ) :
    Matrix (R × L) (R × L) ℂ :=
  C.submatrix (Equiv.prodComm R L) (Equiv.prodComm R L)

theorem twoCutSwap_involutive {L R : Type*} (C : Matrix (L × R) (L × R) ℂ) :
    twoCutSwap (twoCutSwap C) = C := rfl

/-- All scalar and rank data are those of the actual original swapped matrix. -/
theorem twoCutSwap_data {L R : Type*} [Fintype L] [Fintype R]
    (C : Matrix (L × R) (L × R) ℂ) :
    (twoCutSwap C).rank = C.rank ∧ frobSq (twoCutSwap C) = frobSq C ∧
      cutForm (twoCutSwap C) = cutForm C := by
  have hr : (twoCutSwap C).rank = C.rank :=
    Matrix.rank_submatrix C (Equiv.prodComm R L) (Equiv.prodComm R L)
  have hn : frobSq (twoCutSwap C) = frobSq C :=
    frobSq_submatrix_equiv (Equiv.prodComm R L) C
  have ht : (twoCutSwap C).trace = C.trace :=
    trace_submatrix_equiv' (Equiv.prodComm R L) C
  have hL : ptraceL (twoCutSwap C) = ptraceR C := rfl
  have hR : ptraceR (twoCutSwap C) = ptraceL C := rfl
  refine ⟨hr, hn, ?_⟩
  unfold cutForm
  rw [hn, ht, hL, hR]
  ring

/-- Swapping the physical carrier swaps both original local frames and the
compressed coordinates, with no permutation left implicit. -/
theorem twoCutSwap_binary_embedding
    (J₁ J₂ : Matrix (Fin 3) (Fin 2) ℂ)
    (K : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    twoCutSwap ((J₁ ⊗ₖ J₂) * K * (J₁ ⊗ₖ J₂)ᴴ) =
      (J₂ ⊗ₖ J₁) * twoCutSwap K * (J₂ ⊗ₖ J₁)ᴴ := by
  let e₃ := Equiv.prodComm (Fin 3) (Fin 3)
  let e₂ := Equiv.prodComm (Fin 2) (Fin 2)
  have hW : (J₁ ⊗ₖ J₂).submatrix e₃ e₂ = J₂ ⊗ₖ J₁ := by
    ext p q
    simp only [Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
      e₃, e₂, Equiv.prodComm_apply, Prod.swap]
    ring
  have hH : ((J₁ ⊗ₖ J₂)ᴴ).submatrix e₂ e₃ = (J₂ ⊗ₖ J₁)ᴴ := by
    rw [← Matrix.conjTranspose_submatrix, hW]
  change ((J₁ ⊗ₖ J₂) * K * (J₁ ⊗ₖ J₂)ᴴ).submatrix e₃ e₃ = _
  rw [← Matrix.submatrix_mul_equiv ((J₁ ⊗ₖ J₂) * K) (J₁ ⊗ₖ J₂)ᴴ e₃ e₂ e₃,
    ← Matrix.submatrix_mul_equiv (J₁ ⊗ₖ J₂) K e₃ e₂ e₂, hW, hH]
  rfl

/-- A constructed common carrier of the swapped matrix is an actual common
carrier of the original matrix, in the original site order. -/
theorem twoCut_binary_carrier_of_swap
    (C : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (J₁ J₂ : Matrix (Fin 3) (Fin 2) ℂ)
    (K : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hJ₁ : J₁ᴴ * J₁ = 1) (hJ₂ : J₂ᴴ * J₂ = 1)
    (hC : twoCutSwap C = (J₁ ⊗ₖ J₂) * K * (J₁ ⊗ₖ J₂)ᴴ) :
    ∃ V₁ V₂ : Matrix (Fin 3) (Fin 2) ℂ,
      ∃ B : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
      V₁ᴴ * V₁ = 1 ∧ V₂ᴴ * V₂ = 1 ∧
        C = (V₁ ⊗ₖ V₂) * B * (V₁ ⊗ₖ V₂)ᴴ := by
  refine ⟨J₂, J₁, twoCutSwap K, hJ₂, hJ₁, ?_⟩
  have he := congrArg twoCutSwap hC
  simpa only [twoCutSwap_involutive, twoCutSwap_binary_embedding] using he

end ThreeCopyQutritWerner
