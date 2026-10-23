module

public import ThreeCopyQutritWerner.SharpQutritCentralExtremes

@[expose] public section


/-!
# The full nine-vector eigenbasis of the physical qutrit diagonal form

The three central vectors come from the actual central Hermitian spectrum.
The remaining six vectors are the literal symmetric and antisymmetric
coordinate pairs, normalized by the real square root of one half.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

/-- The six unnormalized external pair vectors; sign zero is symmetric. -/
def sharpQutritExternalPair (a : Fin 3) (s : Fin 2) (p : Fin 3 × Fin 3) : ℂ :=
  (if p = (sharpQutritWedgeFirst a, sharpQutritWedgeSecond a) then 1 else 0) +
    (if s = 0 then 1 else -1) *
      (if p = (sharpQutritWedgeSecond a, sharpQutritWedgeFirst a) then 1 else 0)

theorem sharpQutritExternalPair_diagonal (a : Fin 3) (s : Fin 2) (i : Fin 3) :
    sharpQutritExternalPair a s (i, i) = 0 := by
  fin_cases a <;> fin_cases s <;> fin_cases i <;>
    norm_num [sharpQutritExternalPair, sharpQutritWedgeFirst, sharpQutritWedgeSecond]

/-- The six literal external vectors have Gram matrix twice the identity. -/
theorem sharpQutritExternalPair_braket (a b : Fin 3) (s t : Fin 2) :
    braket (sharpQutritExternalPair a s) (sharpQutritExternalPair b t) =
      if (a, s) = (b, t) then 2 else 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases s <;> fin_cases t <;>
    norm_num [braket, sharpQutritExternalPair, sharpQutritWedgeFirst,
      sharpQutritWedgeSecond, Fintype.sum_prod_type, Fin.sum_univ_three]

/-- The actual external block weights: the symmetric vector has weight -d_a
and the antisymmetric vector has weight d_a. -/
def sharpQutritExternalWeight (d : Fin 3 → ℝ) (a : Fin 3) (s : Fin 2) : ℝ :=
  if s = 0 then -d a else d a

set_option maxRecDepth 2048 in
/-- Every pair vector is an actual eigenvector of the original encoded
physical matrix, as checked against its literal block action. -/
theorem sharpQutritExternalPair_eigen (d : Fin 3 → ℝ) (a : Fin 3) (s : Fin 2) :
    sharpQutritAntiEncode (Matrix.diagonal (fun i => (d i : ℂ))) *ᵥ
      sharpQutritExternalPair a s =
        (sharpQutritExternalWeight d a s : ℂ) • sharpQutritExternalPair a s := by
  funext p
  rcases p with ⟨i, j⟩
  rw [sharpQutritAntiEncode_diagonal_action]
  fin_cases a <;> fin_cases s <;> fin_cases i <;> fin_cases j <;>
    simp [sharpQutritExternalPair, sharpQutritExternalWeight, sharpQutritWedgeFirst,
      sharpQutritWedgeSecond, sharpQutritMissing, sharpQutritCentralBlock,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul] <;> ring

/-- Place a central vector on the three original physical diagonal coordinates. -/
def sharpQutritDiagonalEmbed (v : Fin 3 → ℂ) (p : Fin 3 × Fin 3) : ℂ :=
  if p.1 = p.2 then v p.1 else 0

theorem sharpQutritDiagonalEmbed_braket (v w : Fin 3 → ℂ) :
    braket (sharpQutritDiagonalEmbed v) (sharpQutritDiagonalEmbed w) = braket v w := by
  simp [braket, sharpQutritDiagonalEmbed, Fintype.sum_prod_type, Fin.sum_univ_three]

theorem sharpQutritDiagonalEmbed_pair_braket (v : Fin 3 → ℂ) (a : Fin 3) (s : Fin 2) :
    braket (sharpQutritDiagonalEmbed v) (sharpQutritExternalPair a s) = 0 := by
  fin_cases a <;> fin_cases s <;>
    simp [braket, sharpQutritDiagonalEmbed, sharpQutritExternalPair,
      sharpQutritWedgeFirst, sharpQutritWedgeSecond, Fintype.sum_prod_type,
      Fin.sum_univ_three]

/-- The actual central block action lifts to the original nine coordinates. -/
theorem sharpQutritDiagonalEmbed_eigen (d : Fin 3 → ℝ) (v : Fin 3 → ℂ) (r : ℝ)
    (hv : sharpQutritCentralBlock (fun i => (d i : ℂ)) *ᵥ v = (r : ℂ) • v) :
    sharpQutritAntiEncode (Matrix.diagonal (fun i => (d i : ℂ))) *ᵥ
      sharpQutritDiagonalEmbed v = (r : ℂ) • sharpQutritDiagonalEmbed v := by
  funext p
  rcases p with ⟨i, j⟩
  rw [sharpQutritAntiEncode_diagonal_action]
  by_cases hij : i = j
  · subst j
    simpa [sharpQutritDiagonalEmbed, Pi.smul_apply, smul_eq_mul] using congrFun hv i
  · simp [sharpQutritDiagonalEmbed, hij, Ne.symm hij, Pi.smul_apply, smul_eq_mul]

/-- The actual permutation taking ordered central labels to the spectral basis. -/
def sharpQutritCentralSpectralIndex (d : Fin 3 → ℝ) : Fin 3 ≃ Fin 3 :=
  Classical.choose (sharpQutritCentralOrdered_reindex d)

theorem sharpQutritCentralSpectralIndex_eigenvalue (d : Fin 3 → ℝ) (a : Fin 3) :
    (sharpQutritCentralBlock_isHermitian d).eigenvalues
      (sharpQutritCentralSpectralIndex d a) = sharpQutritCentralOrdered d a :=
  (Classical.choose_spec (sharpQutritCentralOrdered_reindex d) a).symm

def sharpQutritCentralVector (d : Fin 3 → ℝ) (a : Fin 3) : Fin 3 × Fin 3 → ℂ :=
  sharpQutritDiagonalEmbed
    ((sharpQutritCentralBlock_isHermitian d).eigenvectorBasis (sharpQutritCentralSpectralIndex d a))

theorem sharpQutritCentralVector_braket (d : Fin 3 → ℝ) (a b : Fin 3) :
    braket (sharpQutritCentralVector d a) (sharpQutritCentralVector d b) =
      if a = b then 1 else 0 := by
  unfold sharpQutritCentralVector
  rw [sharpQutritDiagonalEmbed_braket]
  have h := (sharpQutritCentralBlock_isHermitian d).eigenvectorBasis.inner_eq_ite
    (sharpQutritCentralSpectralIndex d a) (sharpQutritCentralSpectralIndex d b)
  simpa [EuclideanSpace.inner_eq_star_dotProduct, braket, dotProduct,
    Complex.star_def, mul_comm, (sharpQutritCentralSpectralIndex d).injective.eq_iff] using h

theorem sharpQutritCentralVector_eigen (d : Fin 3 → ℝ) (a : Fin 3) :
    sharpQutritAntiEncode (Matrix.diagonal (fun i => (d i : ℂ))) *ᵥ
      sharpQutritCentralVector d a =
        (sharpQutritCentralOrdered d a : ℂ) • sharpQutritCentralVector d a := by
  apply sharpQutritDiagonalEmbed_eigen
  rw [← sharpQutritCentralSpectralIndex_eigenvalue d a]
  exact (sharpQutritCentralBlock_isHermitian d).mulVec_eigenvectorBasis
    (sharpQutritCentralSpectralIndex d a)

/-- Three central labels and six external labels comprise all nine coordinates. -/
abbrev SharpQutritDiagonalIndex := Fin 3 ⊕ (Fin 3 × Fin 2)

def sharpQutritDiagonalVector (d : Fin 3 → ℝ) :
    SharpQutritDiagonalIndex → Fin 3 × Fin 3 → ℂ :=
  Sum.elim (sharpQutritCentralVector d)
    (fun p => (Real.sqrt (1 / 2) : ℂ) • sharpQutritExternalPair p.1 p.2)

def sharpQutritDiagonalWeight (d : Fin 3 → ℝ) : SharpQutritDiagonalIndex → ℝ :=
  Sum.elim (sharpQutritCentralOrdered d) (fun p => sharpQutritExternalWeight d p.1 p.2)

/-- All nine explicitly constructed physical eigenvectors are orthonormal. -/
theorem sharpQutritDiagonalVector_braket (d : Fin 3 → ℝ) (a b : SharpQutritDiagonalIndex) :
    braket (sharpQutritDiagonalVector d a) (sharpQutritDiagonalVector d b) =
      if a = b then 1 else 0 := by
  have hs : (Real.sqrt (1 / 2) : ℂ) ^ 2 = 1 / 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num
  rcases a with a | ⟨a, s⟩
  · rcases b with b | ⟨b, t⟩
    · simpa [sharpQutritDiagonalVector] using sharpQutritCentralVector_braket d a b
    · simp only [sharpQutritDiagonalVector, Sum.elim_inl, Sum.elim_inr,
        singular_braket_real_right, sharpQutritCentralVector,
        sharpQutritDiagonalEmbed_pair_braket, mul_zero, reduceCtorEq, if_false]
  · rcases b with b | ⟨b, t⟩
    · have h : braket (sharpQutritCentralVector d b)
          ((Real.sqrt (1 / 2) : ℂ) • sharpQutritExternalPair a s) = 0 := by
        rw [singular_braket_real_right]
        simp [sharpQutritCentralVector, sharpQutritDiagonalEmbed_pair_braket]
      have hc := congrArg (starRingEnd ℂ) h
      simpa [sharpQutritDiagonalVector, conj_braket] using hc
    · simp only [sharpQutritDiagonalVector, Sum.elim_inr,
        singular_braket_real_scale, hs, sharpQutritExternalPair_braket, Sum.inr.injEq]
      split_ifs <;> norm_num

theorem sharpQutritDiagonalVector_eigen (d : Fin 3 → ℝ) (a : SharpQutritDiagonalIndex) :
    sharpQutritAntiEncode (Matrix.diagonal (fun i => (d i : ℂ))) *ᵥ
      sharpQutritDiagonalVector d a =
        (sharpQutritDiagonalWeight d a : ℂ) • sharpQutritDiagonalVector d a := by
  rcases a with a | ⟨a, s⟩
  · exact sharpQutritCentralVector_eigen d a
  · change _ *ᵥ ((Real.sqrt (1 / 2) : ℂ) • sharpQutritExternalPair a s) =
      (sharpQutritExternalWeight d a s : ℂ) •
        ((Real.sqrt (1 / 2) : ℂ) • sharpQutritExternalPair a s)
    rw [Matrix.mulVec_smul, sharpQutritExternalPair_eigen]
    exact smul_comm _ _ _

def sharpQutritDiagonalFrame (d : Fin 3 → ℝ) :
    Matrix (Fin 3 × Fin 3) SharpQutritDiagonalIndex ℂ :=
  fun i j => sharpQutritDiagonalVector d j i

theorem sharpQutritDiagonalFrame_gram (d : Fin 3 → ℝ) :
    (sharpQutritDiagonalFrame d)ᴴ * sharpQutritDiagonalFrame d = 1 := by
  ext i j
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, sharpQutritDiagonalFrame,
    Matrix.one_apply, braket] using sharpQutritDiagonalVector_braket d i j

/-- The nine constructed columns fill the actual nine-dimensional physical space. -/
theorem sharpQutritDiagonalFrame_complete (d : Fin 3 → ℝ) :
    sharpQutritDiagonalFrame d * (sharpQutritDiagonalFrame d)ᴴ = 1 := by
  exact (Matrix.mul_eq_one_comm_of_card_eq SharpQutritDiagonalIndex
    (Fin 3 × Fin 3) ℂ (by
      simp [SharpQutritDiagonalIndex])).mp (sharpQutritDiagonalFrame_gram d)

/-- A full original-coordinate spectral factorization of the encoded matrix,
including all six signed external weights and the actual ordered central weights. -/
theorem sharpQutritDiagonalFrame_factorization (d : Fin 3 → ℝ) :
    sharpQutritAntiEncode (Matrix.diagonal (fun i => (d i : ℂ))) =
      sharpQutritDiagonalFrame d *
        Matrix.diagonal (fun j => (sharpQutritDiagonalWeight d j : ℂ)) *
          (sharpQutritDiagonalFrame d)ᴴ := by
  have hmul : sharpQutritAntiEncode (Matrix.diagonal (fun i => (d i : ℂ))) *
      sharpQutritDiagonalFrame d = sharpQutritDiagonalFrame d *
        Matrix.diagonal (fun j => (sharpQutritDiagonalWeight d j : ℂ)) := by
    ext i j
    have h := congrFun (sharpQutritDiagonalVector_eigen d j) i
    rw [Matrix.mul_diagonal]
    change (sharpQutritAntiEncode (Matrix.diagonal (fun k => (d k : ℂ))) *ᵥ
      sharpQutritDiagonalVector d j) i =
        sharpQutritDiagonalVector d j i * (sharpQutritDiagonalWeight d j : ℂ)
    simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using h
  calc
    _ = sharpQutritAntiEncode (Matrix.diagonal (fun i => (d i : ℂ))) *
        (sharpQutritDiagonalFrame d * (sharpQutritDiagonalFrame d)ᴴ) := by
          rw [sharpQutritDiagonalFrame_complete, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, hmul]

end ThreeCopyQutritWerner
