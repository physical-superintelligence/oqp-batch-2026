module

public import ThreeCopyQutritWerner.CertificateGlobalDiagramTranspose
public import ThreeCopyQutritWerner.CertificateX2BridgeAssembly
public import ThreeCopyQutritWerner.CertificateX2BridgeParity

@[expose] public section


/-!
# The m and a transfers at operator level

A source Gram is built as a global diagram combination of local "units": per-site diagram
combinations `wU u` (one per unit coordinate `u = (t, a, b)` of the sector) whose original-frame
compression is the matrix unit at `u`. Then

* its Q-form block on every type triple is the source Q-form tensor read on that triple
  (`x2_global_qform_units`), so it is positive semidefinite when the source blocks are
  (`x2_global1_posSemidef`);
* `Γ₃₄` (resp. `Γ₁₂₃₄`) maps it to the sector-0 combination with the same weights
  (`x2_partialTranspose_sector1`, `x2_minorTranspose_sector2`), which acts on the complete
  h frame basis by explicit blocks (`x2_transfer1_acts`, `x2_transfer2_acts`) whose Q-forms,
  under the per-site dictionary `Compression₀ (wU u) = ∑ Q[u', u] E_{u'}`, are the transferred
  tensor `(Q ⊗ Q ⊗ Q) F` read on the triple (`x2_global_qform_dictionary`).

The per-site unit and dictionary identities are finite facts about the certificate's frames,
taken here as hypotheses.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker ComplexOrder

namespace ThreeCopyQutritWerner

/-! ## The physical transposes are involutions -/

theorem x2_partialTranspose_involutive {m n : Type*} (M : Matrix (m × n) (m × n) ℂ) :
    partialTranspose (partialTranspose M) = M := by
  ext x y
  rfl

theorem x2_minorTranspose_involutive {r b c : Type*} (M : Matrix ((r × b) × c) ((r × b) × c) ℂ) :
    minorTranspose (minorTranspose M) = M := by
  ext x y
  rfl

theorem x2_partialTranspose_sector1 {ι : Type*} [Fintype ι] (w : ι → ℂ)
    (w₁ w₂ w₃ : ι → Equiv.Perm (Fin 6) → ℂ) :
    partialTranspose (certificateGlobalDiagramCombination {3, 4, 5} w w₁ w₂ w₃) =
      certificateGlobalDiagramCombination {5} w w₁ w₂ w₃ := by
  rw [← certificateGlobalDiagramCombination_partialTranspose, x2_partialTranspose_involutive]

theorem x2_minorTranspose_sector2 {ι : Type*} [Fintype ι] (w : ι → ℂ)
    (w₁ w₂ w₃ : ι → Equiv.Perm (Fin 6) → ℂ) :
    minorTranspose (certificateGlobalDiagramCombination {1, 2, 3, 4, 5} w w₁ w₂ w₃) =
      certificateGlobalDiagramCombination {5} w w₁ w₂ w₃ := by
  rw [← certificateGlobalDiagramCombination_minorTranspose, x2_minorTranspose_involutive]

/-! ## Actions of the transferred combinations on the complete h basis -/

theorem x2_transfer1_acts {ι : Type*} [Fintype ι] (w : ι → ℂ)
    (w₁ w₂ w₃ : ι → Equiv.Perm (Fin 6) → ℂ) :
    X2Acts certificateThreeSiteFrameSystem0.basis
      (certificateRegroupMatrix
        (partialTranspose (certificateGlobalDiagramCombination {3, 4, 5} w w₁ w₂ w₃)))
      (fun f => ∑ i, w i • certificateTripleSourceAction certificatePhysicalFrameSystem0
        (certificateLocalDecomposition0Action (w₁ i)) (certificateLocalDecomposition0Action (w₂ i))
        (certificateLocalDecomposition0Action (w₃ i)) (certificateThreeSiteFrameSystem0.type f)) := by
  unfold X2Acts
  rw [x2_partialTranspose_sector1]
  exact certificateGlobalDiagramActions0 w w₁ w₂ w₃

theorem x2_transfer2_acts {ι : Type*} [Fintype ι] (w : ι → ℂ)
    (w₁ w₂ w₃ : ι → Equiv.Perm (Fin 6) → ℂ) :
    X2Acts certificateThreeSiteFrameSystem0.basis
      (certificateRegroupMatrix
        (minorTranspose (certificateGlobalDiagramCombination {1, 2, 3, 4, 5} w w₁ w₂ w₃)))
      (fun f => ∑ i, w i • certificateTripleSourceAction certificatePhysicalFrameSystem0
        (certificateLocalDecomposition0Action (w₁ i)) (certificateLocalDecomposition0Action (w₂ i))
        (certificateLocalDecomposition0Action (w₃ i)) (certificateThreeSiteFrameSystem0.type f)) := by
  unfold X2Acts
  rw [x2_minorTranspose_sector2]
  exact certificateGlobalDiagramActions0 w w₁ w₂ w₃

/-! ## Positivity of the source combinations from their Q-form blocks -/

theorem x2_global1_posSemidef {ι : Type*} [Fintype ι] (w : ι → ℂ)
    (w₁ w₂ w₃ : ι → Equiv.Perm (Fin 6) → ℂ)
    (hpsd : ∀ t, (certificateThreeSiteFrameSystem1.metric t *
      ∑ i, w i • certificateTripleSourceAction certificatePhysicalFrameSystem1
        (certificateLocalDecomposition1Action (w₁ i)) (certificateLocalDecomposition1Action (w₂ i))
        (certificateLocalDecomposition1Action (w₃ i)) t).PosSemidef) :
    (certificateGlobalDiagramCombination {3, 4, 5} w w₁ w₂ w₃).PosSemidef := by
  apply x2_posSemidef_of_regroup
  obtain ⟨M, hM, hMS⟩ := certificateThreeSiteFrameSystem1_realize _ hpsd
  exact X2Acts.posSemidef_of_realize certificateThreeSiteFrameSystem1.basis_bijective.2
    (certificateGlobalDiagramActions1 w w₁ w₂ w₃) ⟨M, hM, hMS⟩

theorem x2_global2_posSemidef {ι : Type*} [Fintype ι] (w : ι → ℂ)
    (w₁ w₂ w₃ : ι → Equiv.Perm (Fin 6) → ℂ)
    (hpsd : ∀ t, (certificateThreeSiteFrameSystem2.metric t *
      ∑ i, w i • certificateTripleSourceAction certificatePhysicalFrameSystem2
        (certificateLocalDecomposition2Action (w₁ i)) (certificateLocalDecomposition2Action (w₂ i))
        (certificateLocalDecomposition2Action (w₃ i)) t).PosSemidef) :
    (certificateGlobalDiagramCombination {1, 2, 3, 4, 5} w w₁ w₂ w₃).PosSemidef := by
  apply x2_posSemidef_of_regroup
  obtain ⟨M, hM, hMS⟩ := certificateThreeSiteFrameSystem2_realize _ hpsd
  exact X2Acts.posSemidef_of_realize certificateThreeSiteFrameSystem2.basis_bijective.2
    (certificateGlobalDiagramActions2 w w₁ w₂ w₃) ⟨M, hM, hMS⟩

/-! ## Q-forms of three-site actions -/

theorem x2_tensorSourceGram_mul {T₁ T₂ : Type*} (size₁ : T₁ → ℕ) (size₂ : T₂ → ℕ)
    (G₁ A₁ : (t : T₁) → Matrix (Fin (size₁ t)) (Fin (size₁ t)) ℂ)
    (G₂ A₂ : (t : T₂) → Matrix (Fin (size₂ t)) (Fin (size₂ t)) ℂ) (t : T₁ × T₂) :
    certificateTensorSourceGram size₁ size₂ G₁ G₂ t *
        certificateTensorSourceGram size₁ size₂ A₁ A₂ t =
      certificateTensorSourceGram size₁ size₂ (fun t => G₁ t * A₁ t) (fun t => G₂ t * A₂ t) t := by
  unfold certificateTensorSourceGram
  rw [Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul]

theorem x2_metric_tripleSourceAction {n F T : Type*} [Fintype n] [Fintype F] [DecidableEq n]
    [DecidableEq F] [DecidableEq T] (s : CertificatePhysicalFrameSystem n F T)
    (A B C : (t : T) → Matrix (Fin (s.size t)) (Fin (s.size t)) ℂ) (t : T × T × T) :
    (certificatePhysicalFrameTensor s (certificatePhysicalFrameTensor s s)).metric t *
        certificateTripleSourceAction s A B C t =
      certificateTripleSourceAction s (fun t => s.metric t * A t) (fun t => s.metric t * B t)
        (fun t => s.metric t * C t) t := by
  show certificateTensorSourceGram s.size (fun t : T × T => s.size t.1 * s.size t.2) s.metric
      (certificateTensorSourceGram s.size s.size s.metric s.metric) t *
    certificateTensorSourceGram s.size (fun t : T × T => s.size t.1 * s.size t.2) A
      (certificateTensorSourceGram s.size s.size B C) t = _
  rw [x2_tensorSourceGram_mul]
  unfold certificateTripleSourceAction
  simp only [x2_tensorSourceGram_mul]

/-- Entry formula of the right-associated three-site tensor. -/
theorem x2_tripleSourceAction_apply {n F T : Type*} [Fintype n] [Fintype F] [DecidableEq T]
    (s : CertificatePhysicalFrameSystem n F T)
    (A B C : (t : T) → Matrix (Fin (s.size t)) (Fin (s.size t)) ℂ) (t : T × T × T)
    (i j : Fin (s.size t.1 * (s.size t.2.1 * s.size t.2.2))) :
    certificateTripleSourceAction s A B C t i j =
      A t.1 (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1 *
        (B t.2.1 (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).1
            (finProdFinEquiv.symm (finProdFinEquiv.symm j).2).1 *
          C t.2.2 (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).2
            (finProdFinEquiv.symm (finProdFinEquiv.symm j).2).2) := by
  unfold certificateTripleSourceAction certificateTensorSourceGram
  simp only [Matrix.submatrix_apply, Matrix.kroneckerMap_apply]

/-! ## Units and the collapse of unit sums -/

/-- The matrix unit at unit coordinate `u` on a frame type `t` (natural-number comparison of
the type label `tn t` and the entries). -/
def x2UnitMatrix {T : Type*} (s : Fin 3) (size : T → ℕ) (tn : T → ℕ) (u : X2U s) (t : T) :
    Matrix (Fin (size t)) (Fin (size t)) ℂ :=
  Matrix.of fun i j => if (u.1 : ℕ) = tn t ∧ (u.2.1 : ℕ) = i ∧ (u.2.2 : ℕ) = j then 1 else 0

/-- The unit coordinate of a frame type and two frame indices. -/
def x2UnitAt {T : Type*} (s : Fin 3) (size : T → ℕ) (emb : T → Fin 8)
    (hsz : ∀ t, size t = x2Mult s (emb t)) (t : T) (i j : Fin (size t)) : X2U s :=
  ⟨emb t, (Fin.cast (hsz t) i, Fin.cast (hsz t) j)⟩

theorem x2UnitMatrix_apply_eq {T : Type*} (s : Fin 3) (size : T → ℕ) (emb : T → Fin 8)
    (hsz : ∀ t, size t = x2Mult s (emb t)) (u : X2U s) (t : T) (i j : Fin (size t)) :
    x2UnitMatrix s size (fun t => (emb t : ℕ)) u t i j =
      if u = x2UnitAt s size emb hsz t i j then 1 else 0 := by
  unfold x2UnitMatrix x2UnitAt
  rw [Matrix.of_apply]
  obtain ⟨a, b, c⟩ := u
  dsimp only
  by_cases h : (a : ℕ) = emb t ∧ (b : ℕ) = i ∧ (c : ℕ) = j
  · rw [if_pos h, if_pos]
    obtain ⟨h1, h2, h3⟩ := h
    have ha : a = emb t := Fin.ext h1
    subst ha
    have hb : b = Fin.cast (hsz t) i := Fin.ext h2
    have hc : c = Fin.cast (hsz t) j := Fin.ext h3
    rw [hb, hc]
  · rw [if_neg h, if_neg]
    intro he
    apply h
    have h1 : a = emb t := congrArg Sigma.fst he
    subst h1
    have h23 := eq_of_heq (Sigma.ext_iff.mp he).2
    refine ⟨rfl, ?_, ?_⟩
    · exact congrArg (fun p => Fin.val (Prod.fst p)) h23
    · exact congrArg (fun p => Fin.val (Prod.snd p)) h23

/-- COLLAPSE: a combination of unit triples has, on each type triple, the combination's
coefficient at the unit triple of the entry. -/
theorem x2_tripleUnits_sum {n F T : Type*} [Fintype n] [Fintype F] [DecidableEq T]
    (sys : CertificatePhysicalFrameSystem n F T) (s : Fin 3) (emb : T → Fin 8)
    (hsz : ∀ t, sys.size t = x2Mult s (emb t)) (c : X2U s × X2U s × X2U s → ℂ)
    (t : T × T × T) (i j : Fin (sys.size t.1 * (sys.size t.2.1 * sys.size t.2.2))) :
    (∑ v, c v • certificateTripleSourceAction sys
        (x2UnitMatrix s sys.size (fun t => (emb t : ℕ)) v.1)
        (x2UnitMatrix s sys.size (fun t => (emb t : ℕ)) v.2.1)
        (x2UnitMatrix s sys.size (fun t => (emb t : ℕ)) v.2.2) t) i j =
      c (x2UnitAt s sys.size emb hsz t.1 (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1,
        x2UnitAt s sys.size emb hsz t.2.1 (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).1
          (finProdFinEquiv.symm (finProdFinEquiv.symm j).2).1,
        x2UnitAt s sys.size emb hsz t.2.2 (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).2
          (finProdFinEquiv.symm (finProdFinEquiv.symm j).2).2) := by
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul, x2_tripleSourceAction_apply,
    x2UnitMatrix_apply_eq s sys.size emb hsz]
  rw [Fintype.sum_eq_single (x2UnitAt s sys.size emb hsz t.1 (finProdFinEquiv.symm i).1
      (finProdFinEquiv.symm j).1,
    x2UnitAt s sys.size emb hsz t.2.1 (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).1
      (finProdFinEquiv.symm (finProdFinEquiv.symm j).2).1,
    x2UnitAt s sys.size emb hsz t.2.2 (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).2
      (finProdFinEquiv.symm (finProdFinEquiv.symm j).2).2)]
  · simp
  · intro v hv
    by_cases h0 : v.1 = x2UnitAt s sys.size emb hsz t.1 (finProdFinEquiv.symm i).1
        (finProdFinEquiv.symm j).1
    · by_cases h1 : v.2.1 = x2UnitAt s sys.size emb hsz t.2.1
          (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).1
          (finProdFinEquiv.symm (finProdFinEquiv.symm j).2).1
      · have h2 : ¬ v.2.2 = x2UnitAt s sys.size emb hsz t.2.2
            (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).2
            (finProdFinEquiv.symm (finProdFinEquiv.symm j).2).2 := by
          intro h2
          exact hv (Prod.ext h0 (Prod.ext h1 h2))
        simp only [h2, ite_false, mul_zero]
      · simp only [h1, ite_false, mul_zero, zero_mul]
    · simp only [h0, ite_false, mul_zero, zero_mul]

end ThreeCopyQutritWerner

end
