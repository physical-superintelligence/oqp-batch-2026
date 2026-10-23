module

public import ThreeCopyQutritWerner.CertificateTripleSourceIndexData
public import ThreeCopyQutritWerner.CertificateTensorActions

@[expose] public section


/-!
# Exact site permutations of original joint source coordinates

Both adjacent transpositions use literal row-major finite indices. The same
permutations transport source actions, original Gram matrices and their image
frames; this supplies coordinate transport between ordered local-type triples.
No sorted representative, orbit completeness or numerical image fact is assumed.
-/

noncomputable section

open scoped Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- Exchange the first two sites of a right-associated triple. -/
def certificateTripleSwap12 (a b c : Type*) : (a × b × c) ≃ (b × a × c) where
  toFun x := (x.2.1, x.1, x.2.2)
  invFun x := (x.2.1, x.1, x.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exchange the last two sites of a right-associated triple. -/
def certificateTripleSwap23 (a b c : Type*) : (a × b × c) ≃ (a × c × b) where
  toFun x := (x.1, x.2.2, x.2.1)
  invFun x := (x.1, x.2.2, x.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Unflatten the original right-associated row-major source coordinates. -/

def certificateTripleSourceSwap12 (a b c : ℕ) :
    Fin (a * (b * c)) ≃ Fin (b * (a * c)) :=
  (certificateTripleSourceIndex a b c).trans
    ((certificateTripleSwap12 (Fin a) (Fin b) (Fin c)).trans
      (certificateTripleSourceIndex b a c).symm)

def certificateTripleSourceSwap23 (a b c : ℕ) :
    Fin (a * (b * c)) ≃ Fin (a * (c * b)) :=
  (certificateTripleSourceIndex a b c).trans
    ((certificateTripleSwap23 (Fin a) (Fin b) (Fin c)).trans
      (certificateTripleSourceIndex a c b).symm)

/-- A raw three-factor matrix in exactly the finite coordinates used by the source actions. -/
def certificateTripleSourceMatrix {a b c : ℕ}
    (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin b) (Fin b) ℂ)
    (C : Matrix (Fin c) (Fin c) ℂ) :
    Matrix (Fin (a * (b * c))) (Fin (a * (b * c))) ℂ :=
  (A ⊗ₖ (B ⊗ₖ C)).submatrix (certificateTripleSourceIndex a b c)
    (certificateTripleSourceIndex a b c)

/-- This finite coordinate matrix is the existing original triple source action. -/
theorem certificateTripleSourceAction_eq_matrix
    {n F T : Type*} [Fintype n] [Fintype F] [DecidableEq T]
    (s : CertificatePhysicalFrameSystem n F T)
    (A B C : (t : T) → Matrix (Fin (s.size t)) (Fin (s.size t)) ℂ)
    (t : T × T × T) :
    certificateTripleSourceAction s A B C t =
      certificateTripleSourceMatrix (A t.1) (B t.2.1) (C t.2.2) := rfl

/-- The first adjacent site transposition preserves the literal tensor entries. -/
theorem certificateTripleSourceMatrix_swap12 {a b c : ℕ}
    (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin b) (Fin b) ℂ)
    (C : Matrix (Fin c) (Fin c) ℂ) :
    (certificateTripleSourceMatrix B A C).submatrix
      (certificateTripleSourceSwap12 a b c) (certificateTripleSourceSwap12 a b c) =
        certificateTripleSourceMatrix A B C := by
  ext i j
  simp [certificateTripleSourceMatrix, certificateTripleSourceSwap12,
    certificateTripleSwap12, Matrix.submatrix_apply, Matrix.kroneckerMap_apply]
  <;> ring

/-- The second adjacent site transposition preserves the literal tensor entries. -/
theorem certificateTripleSourceMatrix_swap23 {a b c : ℕ}
    (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin b) (Fin b) ℂ)
    (C : Matrix (Fin c) (Fin c) ℂ) :
    (certificateTripleSourceMatrix A C B).submatrix
      (certificateTripleSourceSwap23 a b c) (certificateTripleSourceSwap23 a b c) =
        certificateTripleSourceMatrix A B C := by
  ext i j
  simp [certificateTripleSourceMatrix, certificateTripleSourceSwap23,
    certificateTripleSwap23, Matrix.submatrix_apply, Matrix.kroneckerMap_apply]
  <;> first | ring1 | (ring_nf <;> simp)

/-- Reindexing an image frame and its ambient metric preserves the original reduced Gram exactly. -/
theorem certificateImageGram_reindex
    {n m k : Type*} [Fintype n] [Fintype m] [Fintype k]
    (e : n ≃ m) (G : Matrix m m ℂ) (J : Matrix m k ℂ) :
    (J.submatrix e id)ᴴ * G.submatrix e e * J.submatrix e id = Jᴴ * G * J := by
  rw [Matrix.conjTranspose_submatrix,
    ← Matrix.submatrix_mul _ _ id e e e.bijective,
    ← Matrix.submatrix_mul _ _ id e id e.bijective]
  rfl

/-- Physical and source tensor factors have the same first-site exchange rule. -/
theorem certificateTripleFrame_swap12
    {n m : Type*} (S : Matrix n m ℂ) :
    (S ⊗ₖ (S ⊗ₖ S)).submatrix (certificateTripleSwap12 n n n)
      (certificateTripleSwap12 m m m) = S ⊗ₖ (S ⊗ₖ S) := by
  ext r c
  simp only [certificateTripleSwap12, Equiv.coe_fn_mk, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply]
  ring

/-- Physical and source tensor factors have the same second-site exchange rule. -/
theorem certificateTripleFrame_swap23
    {n m : Type*} (S : Matrix n m ℂ) :
    (S ⊗ₖ (S ⊗ₖ S)).submatrix (certificateTripleSwap23 n n n)
      (certificateTripleSwap23 m m m) = S ⊗ₖ (S ⊗ₖ S) := by
  ext r c
  simp only [certificateTripleSwap23, Equiv.coe_fn_mk, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply]
  ring

/-- Unflatten every source coordinate while retaining all three descendant labels. -/
def certificateTripleFrameIndex {F T : Type*} (size : T → ℕ) (type : F → T) :
    (Σ f : F × F × F, Fin (size (type f.1) *
      (size (type f.2.1) * size (type f.2.2)))) ≃
        ((Σ f, Fin (size (type f))) × (Σ f, Fin (size (type f))) ×
          (Σ f, Fin (size (type f)))) :=
  (certificateTensorFrameIndex size (fun t : T × T => size t.1 * size t.2)
    type (fun f : F × F => (type f.1, type f.2))).trans
      (Equiv.prodCongr (Equiv.refl _) (certificateTensorFrameIndex size size type type))

def certificateTripleFrameSwap12 {F T : Type*} (size : T → ℕ) (type : F → T) :
    Equiv.Perm (Σ f : F × F × F, Fin (size (type f.1) *
      (size (type f.2.1) * size (type f.2.2)))) :=
  (certificateTripleFrameIndex size type).trans
    ((certificateTripleSwap12 _ _ _).trans (certificateTripleFrameIndex size type).symm)

def certificateTripleFrameSwap23 {F T : Type*} (size : T → ℕ) (type : F → T) :
    Equiv.Perm (Σ f : F × F × F, Fin (size (type f.1) *
      (size (type f.2.1) * size (type f.2.2)))) :=
  (certificateTripleFrameIndex size type).trans
    ((certificateTripleSwap23 _ _ _).trans (certificateTripleFrameIndex size type).symm)

/-- The complete physical triple frame is exactly the reindexed tensor cube of its basis. -/
theorem certificatePhysicalFrameTriple_basis
    {n F T : Type*} [Fintype n] [Fintype F]
    [DecidableEq n] [DecidableEq F] [DecidableEq T]
    (s : CertificatePhysicalFrameSystem n F T) :
    (certificatePhysicalFrameTensor s (certificatePhysicalFrameTensor s s)).basis =
      (s.basis ⊗ₖ (s.basis ⊗ₖ s.basis)).submatrix id
        (certificateTripleFrameIndex s.size s.type) := rfl

/-- Exact simultaneous physical and complete-coordinate permutation at sites 1 and 2. -/
theorem certificatePhysicalFrameTriple_swap12
    {n F T : Type*} [Fintype n] [Fintype F]
    [DecidableEq n] [DecidableEq F] [DecidableEq T]
    (s : CertificatePhysicalFrameSystem n F T) :
    (certificatePhysicalFrameTensor s (certificatePhysicalFrameTensor s s)).basis.submatrix
      (certificateTripleSwap12 n n n) (certificateTripleFrameSwap12 s.size s.type) =
        (certificatePhysicalFrameTensor s (certificatePhysicalFrameTensor s s)).basis := by
  rw [certificatePhysicalFrameTriple_basis]
  ext r c
  simpa [certificateTripleFrameSwap12, Matrix.submatrix_apply] using
    congrFun (congrFun (certificateTripleFrame_swap12 s.basis) r)
      (certificateTripleFrameIndex s.size s.type c)

/-- Exact simultaneous physical and complete-coordinate permutation at sites 2 and 3. -/
theorem certificatePhysicalFrameTriple_swap23
    {n F T : Type*} [Fintype n] [Fintype F]
    [DecidableEq n] [DecidableEq F] [DecidableEq T]
    (s : CertificatePhysicalFrameSystem n F T) :
    (certificatePhysicalFrameTensor s (certificatePhysicalFrameTensor s s)).basis.submatrix
      (certificateTripleSwap23 n n n) (certificateTripleFrameSwap23 s.size s.type) =
        (certificatePhysicalFrameTensor s (certificatePhysicalFrameTensor s s)).basis := by
  rw [certificatePhysicalFrameTriple_basis]
  ext r c
  simpa [certificateTripleFrameSwap23, Matrix.submatrix_apply] using
    congrFun (congrFun (certificateTripleFrame_swap23 s.basis) r)
      (certificateTripleFrameIndex s.size s.type c)

/-- Covariance under a pair of index permutations gives the actual matrix intertwiner. -/
theorem certificate_permutation_intertwines_of_covariance
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (S : Matrix n m ℂ) (er : Equiv.Perm n) (ec : Equiv.Perm m)
    (h : S.submatrix er ec = S) :
    er.permMatrix ℂ * S = S * ec.permMatrix ℂ := by
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext r c
  have he := congrFun (congrFun h r) (ec.symm c)
  simpa only [Matrix.submatrix_apply, Equiv.apply_symm_apply, id_eq] using he

/-- Physical first-site exchange acts by the literal permutation of all descendant/source labels. -/
theorem certificatePhysicalFrameTriple_swap12_action
    {n F T : Type*} [Fintype n] [Fintype F]
    [DecidableEq n] [DecidableEq F] [DecidableEq T]
    (s : CertificatePhysicalFrameSystem n F T) :
    Equiv.Perm.permMatrix ℂ (certificateTripleSwap12 n n n) *
        (certificatePhysicalFrameTensor s (certificatePhysicalFrameTensor s s)).basis =
      (certificatePhysicalFrameTensor s (certificatePhysicalFrameTensor s s)).basis *
        (certificateTripleFrameSwap12 s.size s.type).permMatrix ℂ :=
  certificate_permutation_intertwines_of_covariance _ _ _
    (certificatePhysicalFrameTriple_swap12 s)

/-- Physical second-site exchange acts by the literal permutation of all descendant/source labels. -/
theorem certificatePhysicalFrameTriple_swap23_action
    {n F T : Type*} [Fintype n] [Fintype F]
    [DecidableEq n] [DecidableEq F] [DecidableEq T]
    (s : CertificatePhysicalFrameSystem n F T) :
    Equiv.Perm.permMatrix ℂ (certificateTripleSwap23 n n n) *
        (certificatePhysicalFrameTensor s (certificatePhysicalFrameTensor s s)).basis =
      (certificatePhysicalFrameTensor s (certificatePhysicalFrameTensor s s)).basis *
        (certificateTripleFrameSwap23 s.size s.type).permMatrix ℂ :=
  certificate_permutation_intertwines_of_covariance _ _ _
    (certificatePhysicalFrameTriple_swap23 s)

end ThreeCopyQutritWerner
