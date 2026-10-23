module

public import ThreeCopyQutritWerner.TwoCutSingleFactor
public import ThreeCopyQutritWerner.QutritThinFrame

@[expose] public section


/-!
# Actual common binary carriers for ket-bra projection tensors

Two arbitrary original qutrit vectors fit one constructed binary frame. A
Hermitian rank-at-most-two second factor fits the same frame on both sides.
Their tensor product therefore has a literal common input/output carrier.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- One constructed binary frame fixes both arbitrary original qutrit vectors. -/
theorem twoCut_pair_exists_binary_frame (u v : Fin 3 → ℂ) :
    ∃ J : Matrix (Fin 3) (Fin 2) ℂ, Jᴴ * J = 1 ∧
      (J * Jᴴ) *ᵥ u = u ∧ (J * Jᴴ) *ᵥ v = v := by
  let A : Matrix (Fin 3) (Fin 2) ℂ := fun i j => ![u i, v i] j
  have hr : A.rank ≤ 2 := by simpa using Matrix.rank_le_card_width A
  obtain ⟨J, hJ, hfix⟩ := qutrit_rank_le_two_exists_binary_frame A hr
  refine ⟨J, hJ, ?_, ?_⟩
  · funext i
    have hi := congrFun (congrFun hfix i) 0
    change (∑ j : Fin 3, (J * Jᴴ) i j * u j) = u i at hi
    exact hi
  · funext i
    have hi := congrFun (congrFun hfix i) 1
    change (∑ j : Fin 3, (J * Jᴴ) i j * v j) = v i at hi
    exact hi

/-- A Hermitian thin matrix has a constructed common binary compression,
because its left support equation also gives the original right support. -/
theorem twoCut_hermitian_exists_binary_carrier (P : Matrix (Fin 3) (Fin 3) ℂ)
    (hP : P.IsHermitian) (hr : P.rank ≤ 2) :
    ∃ J : Matrix (Fin 3) (Fin 2) ℂ, Jᴴ * J = 1 ∧
      P = J * (Jᴴ * P * J) * Jᴴ := by
  obtain ⟨J, hJ, hleft⟩ := qutrit_rank_le_two_exists_binary_frame P hr
  have hright : P * (J * Jᴴ) = P := by
    have h := congrArg Matrix.conjTranspose hleft
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hP.eq, Matrix.mul_assoc] using h
  refine ⟨J, hJ, ?_⟩
  symm
  calc
    J * (Jᴴ * P * J) * Jᴴ = (J * Jᴴ * P) * (J * Jᴴ) := by
      simp only [Matrix.mul_assoc]
    _ = P := by rw [hleft, hright]

/-- A ket-bra tensor a Hermitian thin factor has an actual common binary
carrier, with both input and output embeddings constructed from the original factors. -/
theorem twoCut_ketBra_tensor_exists_binary_carrier
    (u v : Fin 3 → ℂ) (P : Matrix (Fin 3) (Fin 3) ℂ)
    (hP : P.IsHermitian) (hr : P.rank ≤ 2) :
    ∃ J₁ J₂ : Matrix (Fin 3) (Fin 2) ℂ,
      ∃ K : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
      J₁ᴴ * J₁ = 1 ∧ J₂ᴴ * J₂ = 1 ∧
        ketBra u v ⊗ₖ P = (J₁ ⊗ₖ J₂) * K * (J₁ ⊗ₖ J₂)ᴴ := by
  obtain ⟨J₁, hJ₁, hu, hv⟩ := twoCut_pair_exists_binary_frame u v
  obtain ⟨J₂, hJ₂, hP₂⟩ := twoCut_hermitian_exists_binary_carrier P hP hr
  have hA : J₁ * (J₁ᴴ * ketBra u v * J₁) * J₁ᴴ = ketBra u v := by
    calc
      _ = (J₁ * J₁ᴴ) * ketBra u v * (J₁ * J₁ᴴ)ᴴ := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.mul_assoc]
      _ = ketBra u v := by rw [binaryPartition_conj_ketBra, hu, hv]
  refine ⟨J₁, J₂, (J₁ᴴ * ketBra u v * J₁) ⊗ₖ (J₂ᴴ * P * J₂), hJ₁, hJ₂, ?_⟩
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, hA, ← hP₂]

end ThreeCopyQutritWerner
