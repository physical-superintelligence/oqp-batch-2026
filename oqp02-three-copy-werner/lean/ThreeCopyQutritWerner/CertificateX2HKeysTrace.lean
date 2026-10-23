module

public import ThreeCopyQutritWerner.CertificateX2HKeysTraceKeys
public import ThreeCopyQutritWerner.CertificateX2HKeysTrCheck0
public import ThreeCopyQutritWerner.CertificateX2HKeysTrCheck1
public import ThreeCopyQutritWerner.CertificateX2HKeysTrCheck2
public import ThreeCopyQutritWerner.CertificateX2HKeysTrCheck3
public import ThreeCopyQutritWerner.CertificateX2HKeysTrCheck4
public import ThreeCopyQutritWerner.CertificateX2HKeysTrCheck5
public import ThreeCopyQutritWerner.CertificateX2HKeysTrCheck6
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section


/-!
# Traces of the carrier's kind parts (trace_count, standard_split, empty_kinds)

Mirrors with the same bodies as the infrastructure's definitions (the literal carrier data are the copies, CertificateX2HKeysCarrierData*, CertificateX2HKeysCarrierWeights):
`x2hAct` = `certificateCarrierSourceAction0`, `x2hTriple` = `certificateTripleSourceAction
certificatePhysicalFrameSystem0` (the body of `certificateTensorSourceGram`, twice), `x2hCarrier` =
`certificateCarrierJointAction0`; `x2hKindProj`, `x2hSlotPerm` = `x2KindProjFrame`, `x2SlotPermFrame`
(CertificateX2HKeysKind).

Generic part: the trace of a cube `A ⊗ A ⊗ A` against a slot permutation is a product of traces of
powers (`trace_triple_slot` and the shape lemmas), so the trace of a kind part is `x2hGC / 6`
(`cube_kind_trace`), and the carrier's is `x2hSumG / 576` (`carrier_kind_trace`). Main results:
`x2hTraceCount`, `x2hStdSplit`, `x2hEmptyKinds`.
-/

set_option maxRecDepth 100000

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace ThreeCopyQutritWerner.X2Sites

open X2

/-- Per-site matrix families on the h frame types. -/
abbrev HFam := (t : Fin 7) → Matrix (Fin (hsz t)) (Fin (hsz t)) ℂ

/-- Mirror of `certificateCarrierSourceAction0` (same body, literal copies of the data). -/
def x2hAct (p : Fin 120) :
    (t : Fin 7) → Matrix (Fin (certificateDescendantFrames2SourceSize t))
      (Fin (certificateDescendantFrames2SourceSize t)) ℂ := by
  exact
    Fin.cases ((x2hA0 p).map (Int.cast : ℤ → ℂ)) <|
    Fin.cases ((x2hA1 p).map (Int.cast : ℤ → ℂ)) <|
    Fin.cases ((x2hA2 p).map (Int.cast : ℤ → ℂ)) <|
    Fin.cases ((x2hA3 p).map (Int.cast : ℤ → ℂ)) <|
    Fin.cases ((x2hA4 p).map (Int.cast : ℤ → ℂ)) <|
    Fin.cases ((x2hA5 p).map (Int.cast : ℤ → ℂ)) <|
    Fin.cases ((x2hA6 p).map (Int.cast : ℤ → ℂ)) <|
    Fin.rec0

/-- Mirror of `certificateTripleSourceAction certificatePhysicalFrameSystem0`. -/
def x2hTriple (A B C : HFam) (τ : Fin 7 × Fin 7 × Fin 7) : Matrix (HIdx τ) (HIdx τ) ℂ :=
  (A τ.1 ⊗ₖ ((B τ.2.1 ⊗ₖ C τ.2.2).submatrix finProdFinEquiv.symm finProdFinEquiv.symm)).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm

/-- Mirror of `certificateCarrierJointAction0`. -/
def x2hCarrier (t : Fin 7 × Fin 7 × Fin 7) : Matrix (HIdx t) (HIdx t) ℂ :=
  ∑ p : Fin 120, (x2hWeight p : ℂ) • x2hTriple (x2hAct p) (x2hAct p) (x2hAct p) t

/-! ## Coordinates -/

/-- Frame index coordinates as a triple of `Fin`s. -/
def x2hE (τ : Fin 7 × Fin 7 × Fin 7) : HIdx τ ≃ Fin (hsz τ.1) × (Fin (hsz τ.2.1) × Fin (hsz τ.2.2)) :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv.symm)

theorem x2hTriple_apply (A B C : HFam) (τ : Fin 7 × Fin 7 × Fin 7) (i j : HIdx τ) :
    x2hTriple A B C τ i j = A τ.1 (x2hE τ i).1 (x2hE τ j).1 *
      (B τ.2.1 (x2hE τ i).2.1 (x2hE τ j).2.1 * C τ.2.2 (x2hE τ i).2.2 (x2hE τ j).2.2) := rfl

theorem x2hCoords_hE (τ : Fin 7 × Fin 7 × Fin 7) (i : HIdx τ) :
    x2hCoords τ i = ![((x2hE τ i).1 : ℕ), ((x2hE τ i).2.1 : ℕ), ((x2hE τ i).2.2 : ℕ)] := rfl

theorem x2hCoords_symm (τ : Fin 7 × Fin 7 × Fin 7)
    (x : Fin (hsz τ.1) × (Fin (hsz τ.2.1) × Fin (hsz τ.2.2))) :
    x2hCoords τ ((x2hE τ).symm x) = ![(x.1 : ℕ), (x.2.1 : ℕ), (x.2.2 : ℕ)] := by
  rw [x2hCoords_hE, Equiv.apply_symm_apply]

/-! ## Traces of cubes against slot permutations -/

/-- Trace of a triple against a slot permutation whose coordinate action is `f`. -/
theorem trace_triple_slot (A B C : HFam) (τ : Fin 7 × Fin 7 × Fin 7) (q : Fin 6)
    (f : Fin (hsz τ.1) × (Fin (hsz τ.2.1) × Fin (hsz τ.2.2)) →
      Fin (hsz τ.1) × (Fin (hsz τ.2.1) × Fin (hsz τ.2.2)))
    (hf : ∀ x, ![(x.1 : ℕ), (x.2.1 : ℕ), (x.2.2 : ℕ)] ∘ x2Perm3 q =
      ![((f x).1 : ℕ), ((f x).2.1 : ℕ), ((f x).2.2 : ℕ)]) :
    (x2hTriple A B C τ * x2hSlotPerm τ q).trace =
      ∑ x, A τ.1 (f x).1 x.1 * (B τ.2.1 (f x).2.1 x.2.1 * C τ.2.2 (f x).2.2 x.2.2) := by
  unfold Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_apply, x2hSlotPerm, Matrix.of_apply, mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_comm, ← (x2hE τ).symm.sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  have hcond : x2hCoords τ ((x2hE τ).symm (f x)) = x2hCoords τ ((x2hE τ).symm x) ∘ x2Perm3 q := by
    rw [x2hCoords_symm, x2hCoords_symm, hf]
  rw [Finset.sum_eq_single ((x2hE τ).symm (f x))]
  · rw [if_pos hcond, x2hTriple_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  · intro i _ hi
    rw [if_neg]
    intro hc
    apply hi
    apply x2hCoords_injective τ
    rw [hc, hcond]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem trace_submatrix_equiv' {m n : Type*} [Fintype m] [Fintype n] (M : Matrix n n ℂ) (e : m ≃ n) :
    (M.submatrix e e).trace = M.trace :=
  Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem trace_x2hTriple (A B C : HFam) (τ : Fin 7 × Fin 7 × Fin 7) :
    (x2hTriple A B C τ).trace = (A τ.1).trace * ((B τ.2.1).trace * (C τ.2.2).trace) := by
  unfold x2hTriple
  rw [trace_submatrix_equiv', Matrix.trace_kronecker, trace_submatrix_equiv', Matrix.trace_kronecker]

theorem trace_x2hTriple_aaa (A : HFam) (a : Fin 7) :
    (x2hTriple A A A (a, a, a)).trace = (A a).trace * ((A a).trace * (A a).trace) :=
  trace_x2hTriple A A A (a, a, a)

theorem trace_x2hTriple_aac (A : HFam) (a c : Fin 7) :
    (x2hTriple A A A (a, a, c)).trace = (A a).trace * ((A a).trace * (A c).trace) :=
  trace_x2hTriple A A A (a, a, c)

theorem trace_x2hTriple_abb (A : HFam) (a b : Fin 7) :
    (x2hTriple A A A (a, b, b)).trace = (A a).trace * ((A b).trace * (A b).trace) :=
  trace_x2hTriple A A A (a, b, b)

theorem trace_x2hTriple_abc (A : HFam) (a b c : Fin 7) :
    (x2hTriple A A A (a, b, c)).trace = (A a).trace * ((A b).trace * (A c).trace) :=
  trace_x2hTriple A A A (a, b, c)

/-! Traces of powers as iterated sums (deterministic normal forms). -/

theorem tr1_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : A.trace = ∑ i, A i i := rfl

theorem tr2_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : (A * A).trace = ∑ i, ∑ j, A i j * A j i := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]

theorem tr3_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (A * A * A).trace = ∑ i, ∑ k, ∑ j, A i j * A j k * A k i := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.sum_mul]

theorem tr2_tr1 {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin m) (Fin m) ℂ) :
    (A * A).trace * C.trace = ∑ i, ∑ j, ∑ k, A i j * A j i * C k k := by
  rw [tr2_sum, tr1_sum]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]

theorem tr1_tr2 {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin m) (Fin m) ℂ) :
    A.trace * (C * C).trace = ∑ i, ∑ j, ∑ k, A i i * (C j k * C k j) := by
  rw [tr2_sum, tr1_sum]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]

theorem tr1_tr1_tr1 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    A.trace * (A.trace * A.trace) = ∑ i, ∑ j, ∑ k, A i i * (A j j * A k k) := by
  rw [tr1_sum]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]

/-- `(a, a, c)`: the first-two-slot swap. -/
theorem trace_cube_slot01 (A : HFam) (a c : Fin 7) :
    (x2hTriple A A A (a, a, c) * x2hSlotPerm (a, a, c) x2Swap01Idx).trace =
      (A a * A a).trace * (A c).trace := by
  rw [trace_triple_slot A A A (a, a, c) x2Swap01Idx (fun x => (x.2.1, x.1, x.2.2))
    (fun x => by funext k; fin_cases k <;> rfl), tr2_tr1]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  ring

/-- `(a, c, c)`: the last-two-slot swap. -/
theorem trace_cube_slot12 (A : HFam) (a c : Fin 7) :
    (x2hTriple A A A (a, c, c) * x2hSlotPerm (a, c, c) x2Swap12Idx).trace =
      (A a).trace * (A c * A c).trace := by
  rw [trace_triple_slot A A A (a, c, c) x2Swap12Idx (fun x => (x.1, x.2.2, x.2.1))
    (fun x => by funext k; fin_cases k <;> rfl), tr1_tr2]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  ring

/-! Three equal types: the six slot permutations (`x2Perm3` order: id, (12), (01), two 3-cycles, (02)). -/

theorem trace_aaa0 (A : HFam) (a : Fin 7) :
    (x2hTriple A A A (a, a, a) * x2hSlotPerm (a, a, a) 0).trace =
      (A a).trace * ((A a).trace * (A a).trace) := by
  rw [trace_triple_slot A A A (a, a, a) 0 (fun x => x)
    (fun x => by funext k; fin_cases k <;> rfl), tr1_tr1_tr1]
  simp only [Fintype.sum_prod_type]
  all_goals rfl

theorem trace_aaa1 (A : HFam) (a : Fin 7) :
    (x2hTriple A A A (a, a, a) * x2hSlotPerm (a, a, a) 1).trace =
      (A a).trace * (A a * A a).trace := by
  rw [trace_triple_slot A A A (a, a, a) 1 (fun x => (x.1, x.2.2, x.2.1))
    (fun x => by funext k; fin_cases k <;> rfl), tr1_tr2]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  ring

theorem trace_aaa2 (A : HFam) (a : Fin 7) :
    (x2hTriple A A A (a, a, a) * x2hSlotPerm (a, a, a) 2).trace =
      (A a * A a).trace * (A a).trace := by
  rw [trace_triple_slot A A A (a, a, a) 2 (fun x => (x.2.1, x.1, x.2.2))
    (fun x => by funext k; fin_cases k <;> rfl), tr2_tr1]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  ring

theorem trace_aaa3 (A : HFam) (a : Fin 7) :
    (x2hTriple A A A (a, a, a) * x2hSlotPerm (a, a, a) 3).trace = (A a * A a * A a).trace := by
  rw [trace_triple_slot A A A (a, a, a) 3 (fun x => (x.2.1, x.2.2, x.1))
    (fun x => by funext k; fin_cases k <;> rfl), tr3_sum]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  ring

theorem trace_aaa4 (A : HFam) (a : Fin 7) :
    (x2hTriple A A A (a, a, a) * x2hSlotPerm (a, a, a) 4).trace = (A a * A a * A a).trace := by
  rw [trace_triple_slot A A A (a, a, a) 4 (fun x => (x.2.2, x.1, x.2.1))
    (fun x => by funext k; fin_cases k <;> rfl), tr3_sum]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  ring

theorem trace_aaa5 (A : HFam) (a : Fin 7) :
    (x2hTriple A A A (a, a, a) * x2hSlotPerm (a, a, a) 5).trace =
      (A a * A a).trace * (A a).trace := by
  rw [trace_triple_slot A A A (a, a, a) 5 (fun x => (x.2.2, x.2.1, x.1))
    (fun x => by funext k; fin_cases k <;> rfl), tr2_tr1]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  ring

theorem coords_lt_aaa (a : Fin 7) (i : HIdx (a, a, a)) (k : Fin 3) : x2hCoords (a, a, a) i k < hsz a := by
  rw [x2hCoords_hE]
  fin_cases k
  · exact (x2hE (a, a, a) i).1.isLt
  · exact (x2hE (a, a, a) i).2.1.isLt
  · exact (x2hE (a, a, a) i).2.2.isLt

/-- Slot permutations of three equal types compose like `x2Perm3`. -/
theorem slotPerm_mul_aaa (a : Fin 7) (p q r : Fin 6) (hr : x2Perm3 p ∘ x2Perm3 q = x2Perm3 r) :
    x2hSlotPerm (a, a, a) p * x2hSlotPerm (a, a, a) q = x2hSlotPerm (a, a, a) r := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [x2hSlotPerm, Matrix.of_apply, ite_mul, one_mul, zero_mul]
  have h0 : (x2hCoords (a, a, a) i ∘ x2Perm3 p) 0 < hsz (a, a, a).1 := coords_lt_aaa a i (x2Perm3 p 0)
  have h1 : (x2hCoords (a, a, a) i ∘ x2Perm3 p) 1 < hsz (a, a, a).2.1 := coords_lt_aaa a i (x2Perm3 p 1)
  have h2 : (x2hCoords (a, a, a) i ∘ x2Perm3 p) 2 < hsz (a, a, a).2.2 := coords_lt_aaa a i (x2Perm3 p 2)
  rw [Finset.sum_eq_single ⟨hidxN (a, a, a) (x2hCoords (a, a, a) i ∘ x2Perm3 p),
    hidxN_lt (a, a, a) _ h0 h1 h2⟩]
  · rw [if_pos (x2hCoords_hidx (a, a, a) _ h0 h1 h2), x2hCoords_hidx (a, a, a) _ h0 h1 h2,
      Function.comp_assoc, hr]
  · intro l _ hl
    rw [if_neg]
    intro hc
    apply hl
    apply x2hCoords_injective (a, a, a)
    rw [hc, x2hCoords_hidx (a, a, a) _ h0 h1 h2]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem mtab0 (a : Fin 7) : x2hSlotPerm (a, a, a) 0 * x2hSlotPerm (a, a, a) 2 = x2hSlotPerm (a, a, a) 2 :=
  slotPerm_mul_aaa a 0 2 2 (by funext k; fin_cases k <;> rfl)
theorem mtab1 (a : Fin 7) : x2hSlotPerm (a, a, a) 1 * x2hSlotPerm (a, a, a) 2 = x2hSlotPerm (a, a, a) 4 :=
  slotPerm_mul_aaa a 1 2 4 (by funext k; fin_cases k <;> rfl)
theorem mtab2 (a : Fin 7) : x2hSlotPerm (a, a, a) 2 * x2hSlotPerm (a, a, a) 2 = x2hSlotPerm (a, a, a) 0 :=
  slotPerm_mul_aaa a 2 2 0 (by funext k; fin_cases k <;> rfl)
theorem mtab3 (a : Fin 7) : x2hSlotPerm (a, a, a) 3 * x2hSlotPerm (a, a, a) 2 = x2hSlotPerm (a, a, a) 5 :=
  slotPerm_mul_aaa a 3 2 5 (by funext k; fin_cases k <;> rfl)
theorem mtab4 (a : Fin 7) : x2hSlotPerm (a, a, a) 4 * x2hSlotPerm (a, a, a) 2 = x2hSlotPerm (a, a, a) 1 :=
  slotPerm_mul_aaa a 4 2 1 (by funext k; fin_cases k <;> rfl)
theorem mtab5 (a : Fin 7) : x2hSlotPerm (a, a, a) 5 * x2hSlotPerm (a, a, a) 2 = x2hSlotPerm (a, a, a) 3 :=
  slotPerm_mul_aaa a 5 2 3 (by funext k; fin_cases k <;> rfl)

theorem sgn0 : x2Perm3Sign 0 = 1 := rfl
theorem sgn1 : x2Perm3Sign 1 = -1 := rfl
theorem sgn2 : x2Perm3Sign 2 = -1 := rfl
theorem sgn3 : x2Perm3Sign 3 = 1 := rfl
theorem sgn4 : x2Perm3Sign 4 = 1 := rfl
theorem sgn5 : x2Perm3Sign 5 = -1 := rfl

/-! ## Kind projectors by shape -/

/-- The symmetrizer and the antisymmetrizer of the three slots. -/
def hAvg (τ : Fin 7 × Fin 7 × Fin 7) : Matrix (HIdx τ) (HIdx τ) ℂ := (1 / 6 : ℂ) • ∑ p, x2hSlotPerm τ p

def hAlt (τ : Fin 7 × Fin 7 × Fin 7) : Matrix (HIdx τ) (HIdx τ) ℂ :=
  (1 / 6 : ℂ) • ∑ p, ((x2Perm3Sign p : ℚ) : ℂ) • x2hSlotPerm τ p

theorem x2hKindProj_eq (τ : Fin 7 × Fin 7 × Fin 7) (k : ℕ) : x2hKindProj τ k =
    if τ.1 = τ.2.1 ∧ τ.2.1 = τ.2.2 then
      (if k = 0 then hAvg τ else if k = 1 then hAlt τ else 1 - hAvg τ - hAlt τ)
    else if τ.1 = τ.2.1 then
      (1 / 2 : ℂ) • (1 + (if k = 0 then (1 : ℂ) else -1) • x2hSlotPerm τ x2Swap01Idx)
    else if τ.2.1 = τ.2.2 then
      (1 / 2 : ℂ) • (1 + (if k = 0 then (1 : ℂ) else -1) • x2hSlotPerm τ x2Swap12Idx)
    else 1 := rfl

theorem x2hKindProj_aaa (a : Fin 7) (k : ℕ) : x2hKindProj (a, a, a) k =
    if k = 0 then hAvg (a, a, a) else if k = 1 then hAlt (a, a, a) else 1 - hAvg (a, a, a) - hAlt (a, a, a) := by
  rw [x2hKindProj_eq]
  exact if_pos ⟨rfl, rfl⟩

theorem x2hKindProj_aac (a c : Fin 7) (hac : a ≠ c) (k : ℕ) : x2hKindProj (a, a, c) k =
    (1 / 2 : ℂ) • (1 + (if k = 0 then (1 : ℂ) else -1) • x2hSlotPerm (a, a, c) x2Swap01Idx) := by
  rw [x2hKindProj_eq, if_neg (show ¬((a, a, c).1 = (a, a, c).2.1 ∧ (a, a, c).2.1 = (a, a, c).2.2) from
    fun h => hac h.2)]
  exact if_pos rfl

theorem x2hKindProj_abb (a b : Fin 7) (hab : a ≠ b) (k : ℕ) : x2hKindProj (a, b, b) k =
    (1 / 2 : ℂ) • (1 + (if k = 0 then (1 : ℂ) else -1) • x2hSlotPerm (a, b, b) x2Swap12Idx) := by
  rw [x2hKindProj_eq, if_neg (show ¬((a, b, b).1 = (a, b, b).2.1 ∧ (a, b, b).2.1 = (a, b, b).2.2) from
    fun h => hab h.1), if_neg (show ¬((a, b, b).1 = (a, b, b).2.1) from hab)]
  exact if_pos rfl

theorem x2hKindProj_abc (a b c : Fin 7) (hab : a ≠ b) (hbc : b ≠ c) (k : ℕ) :
    x2hKindProj (a, b, c) k = 1 := by
  rw [x2hKindProj_eq, if_neg (show ¬((a, b, c).1 = (a, b, c).2.1 ∧ (a, b, c).2.1 = (a, b, c).2.2) from
    fun h => hab h.1), if_neg (show ¬((a, b, c).1 = (a, b, c).2.1) from hab)]
  exact if_neg (show ¬((a, b, c).2.1 = (a, b, c).2.2) from hbc)

/-! ## The formula -/

/-- Six times the trace of a kind part of a cube, from the local traces (complex version of `x2hG`). -/
def x2hGC (T1 T2 T3 : Fin 7 → ℂ) (τ : Fin 7 × Fin 7 × Fin 7) (k : ℕ) : ℂ :=
  if τ.1 = τ.2.1 ∧ τ.2.1 = τ.2.2 then
    (if k = 0 then T1 τ.1 ^ 3 + 3 * T1 τ.1 * T2 τ.1 + 2 * T3 τ.1
      else if k = 1 then T1 τ.1 ^ 3 - 3 * T1 τ.1 * T2 τ.1 + 2 * T3 τ.1
      else 4 * T1 τ.1 ^ 3 - 4 * T3 τ.1)
  else if τ.1 = τ.2.1 then
    3 * (T1 τ.1 * T1 τ.1 * T1 τ.2.2 + (if k = 0 then 1 else -1) * T2 τ.1 * T1 τ.2.2)
  else if τ.2.1 = τ.2.2 then
    3 * (T1 τ.1 * T1 τ.2.1 * T1 τ.2.1 + (if k = 0 then 1 else -1) * T1 τ.1 * T2 τ.2.1)
  else 6 * (T1 τ.1 * T1 τ.2.1 * T1 τ.2.2)

theorem x2hGC_aaa (T1 T2 T3 : Fin 7 → ℂ) (a : Fin 7) (k : ℕ) : x2hGC T1 T2 T3 (a, a, a) k =
    if k = 0 then T1 a ^ 3 + 3 * T1 a * T2 a + 2 * T3 a
      else if k = 1 then T1 a ^ 3 - 3 * T1 a * T2 a + 2 * T3 a
      else 4 * T1 a ^ 3 - 4 * T3 a := by
  unfold x2hGC
  exact if_pos ⟨rfl, rfl⟩

theorem x2hGC_aac (T1 T2 T3 : Fin 7 → ℂ) (a c : Fin 7) (hac : a ≠ c) (k : ℕ) : x2hGC T1 T2 T3 (a, a, c) k =
    3 * (T1 a * T1 a * T1 c + (if k = 0 then 1 else -1) * T2 a * T1 c) := by
  unfold x2hGC
  rw [if_neg (show ¬((a, a, c).1 = (a, a, c).2.1 ∧ (a, a, c).2.1 = (a, a, c).2.2) from fun h => hac h.2)]
  exact if_pos rfl

theorem x2hGC_abb (T1 T2 T3 : Fin 7 → ℂ) (a b : Fin 7) (hab : a ≠ b) (k : ℕ) : x2hGC T1 T2 T3 (a, b, b) k =
    3 * (T1 a * T1 b * T1 b + (if k = 0 then 1 else -1) * T1 a * T2 b) := by
  unfold x2hGC
  rw [if_neg (show ¬((a, b, b).1 = (a, b, b).2.1 ∧ (a, b, b).2.1 = (a, b, b).2.2) from fun h => hab h.1),
    if_neg (show ¬((a, b, b).1 = (a, b, b).2.1) from hab)]
  exact if_pos rfl

theorem x2hGC_abc (T1 T2 T3 : Fin 7 → ℂ) (a b c : Fin 7) (hab : a ≠ b) (hbc : b ≠ c) (k : ℕ) :
    x2hGC T1 T2 T3 (a, b, c) k = 6 * (T1 a * T1 b * T1 c) := by
  unfold x2hGC
  rw [if_neg (show ¬((a, b, c).1 = (a, b, c).2.1 ∧ (a, b, c).2.1 = (a, b, c).2.2) from fun h => hab h.1),
    if_neg (show ¬((a, b, c).1 = (a, b, c).2.1) from hab)]
  exact if_neg (show ¬((a, b, c).2.1 = (a, b, c).2.2) from hbc)

theorem trace_avg_aaa (A : HFam) (a : Fin 7) :
    (x2hTriple A A A (a, a, a) * hAvg (a, a, a)).trace =
      (1 / 6 : ℂ) * ((A a).trace * ((A a).trace * (A a).trace) + (A a).trace * (A a * A a).trace +
        (A a * A a).trace * (A a).trace + (A a * A a * A a).trace + (A a * A a * A a).trace +
        (A a * A a).trace * (A a).trace) := by
  unfold hAvg
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_sum, Matrix.trace_sum, Fin.sum_univ_six,
    trace_aaa0, trace_aaa1, trace_aaa2, trace_aaa3, trace_aaa4, trace_aaa5]

theorem trace_alt_aaa (A : HFam) (a : Fin 7) :
    (x2hTriple A A A (a, a, a) * hAlt (a, a, a)).trace =
      (1 / 6 : ℂ) * ((A a).trace * ((A a).trace * (A a).trace) - (A a).trace * (A a * A a).trace -
        (A a * A a).trace * (A a).trace + (A a * A a * A a).trace + (A a * A a * A a).trace -
        (A a * A a).trace * (A a).trace) := by
  unfold hAlt
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_sum, Matrix.trace_sum, Fin.sum_univ_six]
  simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, trace_aaa0, trace_aaa1, trace_aaa2,
    trace_aaa3, trace_aaa4, trace_aaa5, sgn0, sgn1, sgn2, sgn3, sgn4, sgn5]
  push_cast
  ring

theorem cube_aaa (A : HFam) (a : Fin 7) (k : ℕ) :
    (x2hTriple A A A (a, a, a) * x2hKindProj (a, a, a) k).trace =
      x2hGC (fun t => (A t).trace) (fun t => (A t * A t).trace) (fun t => (A t * A t * A t).trace)
        (a, a, a) k / 6 := by
  rw [x2hKindProj_aaa, x2hGC_aaa]
  split_ifs with h0 h1
  · rw [trace_avg_aaa]
    ring
  · rw [trace_alt_aaa]
    ring
  · rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_sub, Matrix.mul_one, trace_x2hTriple_aaa,
      trace_avg_aaa, trace_alt_aaa]
    ring

theorem cube_aac (A : HFam) (a c : Fin 7) (hac : a ≠ c) (k : ℕ) :
    (x2hTriple A A A (a, a, c) * x2hKindProj (a, a, c) k).trace =
      x2hGC (fun t => (A t).trace) (fun t => (A t * A t).trace) (fun t => (A t * A t * A t).trace)
        (a, a, c) k / 6 := by
  rw [x2hKindProj_aac a c hac, x2hGC_aac _ _ _ a c hac, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
    Matrix.mul_add, Matrix.mul_one, Matrix.trace_add, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
    trace_x2hTriple_aac, trace_cube_slot01]
  split_ifs <;> ring

theorem cube_abb (A : HFam) (a b : Fin 7) (hab : a ≠ b) (k : ℕ) :
    (x2hTriple A A A (a, b, b) * x2hKindProj (a, b, b) k).trace =
      x2hGC (fun t => (A t).trace) (fun t => (A t * A t).trace) (fun t => (A t * A t * A t).trace)
        (a, b, b) k / 6 := by
  rw [x2hKindProj_abb a b hab, x2hGC_abb _ _ _ a b hab, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
    Matrix.mul_add, Matrix.mul_one, Matrix.trace_add, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
    trace_x2hTriple_abb, trace_cube_slot12]
  split_ifs <;> ring

theorem cube_abc (A : HFam) (a b c : Fin 7) (hab : a ≠ b) (hbc : b ≠ c) (k : ℕ) :
    (x2hTriple A A A (a, b, c) * x2hKindProj (a, b, c) k).trace =
      x2hGC (fun t => (A t).trace) (fun t => (A t * A t).trace) (fun t => (A t * A t * A t).trace)
        (a, b, c) k / 6 := by
  rw [x2hKindProj_abc a b c hab hbc, x2hGC_abc _ _ _ a b c hab hbc, Matrix.mul_one, trace_x2hTriple_abc]
  ring

/-- The trace of a kind part of any cube `A ⊗ A ⊗ A`. -/
theorem cube_kind_trace (A : HFam) (τ : Fin 7 × Fin 7 × Fin 7) (k : ℕ) :
    (x2hTriple A A A τ * x2hKindProj τ k).trace =
      x2hGC (fun t => (A t).trace) (fun t => (A t * A t).trace) (fun t => (A t * A t * A t).trace) τ k / 6 := by
  obtain ⟨a, b, c⟩ := τ
  by_cases hab : a = b
  · by_cases hbc : b = c
    · subst hab
      subst hbc
      exact cube_aaa A _ k
    · subst hab
      exact cube_aac A _ _ hbc k
  · by_cases hbc : b = c
    · subst hbc
      exact cube_abb A _ _ hab k
    · exact cube_abc A _ _ _ hab hbc k

/-- The swap has trace zero on the standard part of any cube of three equal types. -/
theorem cube_split_aaa (A : HFam) (a : Fin 7) :
    (x2hTriple A A A (a, a, a) * x2hKindProj (a, a, a) 2 * x2hSlotPerm (a, a, a) x2Swap01Idx).trace = 0 := by
  rw [show x2Swap01Idx = (2 : Fin 6) from rfl, x2hKindProj_aaa, if_neg (by decide : (2 : ℕ) ≠ 0),
    if_neg (by decide : (2 : ℕ) ≠ 1), Matrix.mul_assoc, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul]
  unfold hAvg hAlt
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.sum_mul, Matrix.sum_mul, Fin.sum_univ_six, Fin.sum_univ_six]
  simp only [Matrix.smul_mul, mtab0, mtab1, mtab2, mtab3, mtab4, mtab5]
  simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_add,
    Matrix.trace_smul, smul_eq_mul, trace_aaa0, trace_aaa1, trace_aaa2, trace_aaa3, trace_aaa4, trace_aaa5,
    sgn0, sgn1, sgn2, sgn3, sgn4, sgn5]
  push_cast
  ring

theorem cube_split (A : HFam) (τ : Fin 7 × Fin 7 × Fin 7) (h : τ.1 = τ.2.1 ∧ τ.2.1 = τ.2.2) :
    (x2hTriple A A A τ * x2hKindProj τ 2 * x2hSlotPerm τ x2Swap01Idx).trace = 0 := by
  obtain ⟨a, b, c⟩ := τ
  obtain ⟨h1, h2⟩ := h
  change a = b at h1
  change b = c at h2
  subst h1
  subst h2
  exact cube_split_aaa A _

/-! ## The carrier -/

theorem trace_map_int {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    (A.map (Int.cast : ℤ → ℂ)).trace = ((A.trace : ℤ) : ℂ) := by
  simp [Matrix.trace]

theorem map_int_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℤ) :
    A.map (Int.cast : ℤ → ℂ) * B.map (Int.cast : ℤ → ℂ) = (A * B).map (Int.cast : ℤ → ℂ) := by
  ext i j
  simp [Matrix.mul_apply]

theorem tr_cast1 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (v : ℤ) (h : A.trace = v) :
    (A.map (Int.cast : ℤ → ℂ)).trace = (v : ℂ) := by
  rw [trace_map_int, h]

theorem tr_cast2 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (v : ℤ) (h : (A * A).trace = v) :
    (A.map (Int.cast : ℤ → ℂ) * A.map (Int.cast : ℤ → ℂ)).trace = (v : ℂ) := by
  rw [map_int_mul, trace_map_int, h]

theorem tr_cast3 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (v : ℤ) (h : (A * A * A).trace = v) :
    (A.map (Int.cast : ℤ → ℂ) * A.map (Int.cast : ℤ → ℂ) * A.map (Int.cast : ℤ → ℂ)).trace = (v : ℂ) := by
  rw [map_int_mul, map_int_mul, trace_map_int, h]

/-- The local traces of the carrier actions are the kernel-checked tables. -/
theorem x2hAct_traces (p : Fin 120) (t : Fin 7) :
    (x2hAct p t).trace = (x2hTrAll t 0 p : ℂ) ∧ (x2hAct p t * x2hAct p t).trace = (x2hTrAll t 1 p : ℂ) ∧
      (x2hAct p t * x2hAct p t * x2hAct p t).trace = (x2hTrAll t 2 p : ℂ) := by
  fin_cases t
  · obtain ⟨e1, e2, e3⟩ := x2hTrCheck0 p
    exact ⟨tr_cast1 (x2hA0 p) _ e1, tr_cast2 (x2hA0 p) _ e2, tr_cast3 (x2hA0 p) _ e3⟩
  · obtain ⟨e1, e2, e3⟩ := x2hTrCheck1 p
    exact ⟨tr_cast1 (x2hA1 p) _ e1, tr_cast2 (x2hA1 p) _ e2, tr_cast3 (x2hA1 p) _ e3⟩
  · obtain ⟨e1, e2, e3⟩ := x2hTrCheck2 p
    exact ⟨tr_cast1 (x2hA2 p) _ e1, tr_cast2 (x2hA2 p) _ e2, tr_cast3 (x2hA2 p) _ e3⟩
  · obtain ⟨e1, e2, e3⟩ := x2hTrCheck3 p
    exact ⟨tr_cast1 (x2hA3 p) _ e1, tr_cast2 (x2hA3 p) _ e2, tr_cast3 (x2hA3 p) _ e3⟩
  · obtain ⟨e1, e2, e3⟩ := x2hTrCheck4 p
    exact ⟨tr_cast1 (x2hA4 p) _ e1, tr_cast2 (x2hA4 p) _ e2, tr_cast3 (x2hA4 p) _ e3⟩
  · obtain ⟨e1, e2, e3⟩ := x2hTrCheck5 p
    exact ⟨tr_cast1 (x2hA5 p) _ e1, tr_cast2 (x2hA5 p) _ e2, tr_cast3 (x2hA5 p) _ e3⟩
  · obtain ⟨e1, e2, e3⟩ := x2hTrCheck6 p
    exact ⟨tr_cast1 (x2hA6 p) _ e1, tr_cast2 (x2hA6 p) _ e2, tr_cast3 (x2hA6 p) _ e3⟩

theorem x2hAct_tr1 (p : Fin 120) (t : Fin 7) : (x2hAct p t).trace = (x2hTrAll t 0 p : ℂ) :=
  (x2hAct_traces p t).1

theorem x2hAct_tr2 (p : Fin 120) (t : Fin 7) : (x2hAct p t * x2hAct p t).trace = (x2hTrAll t 1 p : ℂ) :=
  (x2hAct_traces p t).2.1

theorem x2hAct_tr3 (p : Fin 120) (t : Fin 7) :
    (x2hAct p t * x2hAct p t * x2hAct p t).trace = (x2hTrAll t 2 p : ℂ) :=
  (x2hAct_traces p t).2.2

theorem x2hGC_cast (T1 T2 T3 : Fin 7 → ℤ) (τ : Fin 7 × Fin 7 × Fin 7) (k : ℕ) :
    x2hGC (fun t => (T1 t : ℂ)) (fun t => (T2 t : ℂ)) (fun t => (T3 t : ℂ)) τ k =
      ((x2hG T1 T2 T3 τ k : ℤ) : ℂ) := by
  unfold x2hGC x2hG
  split_ifs <;> push_cast <;> ring

/-- The trace of every kind part of the carrier is `x2hSumG / 576`. -/
theorem carrier_kind_trace (τ : Fin 7 × Fin 7 × Fin 7) (k : ℕ) :
    (x2hCarrier τ * x2hKindProj τ k).trace = ((x2hSumG τ k : ℤ) : ℂ) / 576 := by
  unfold x2hCarrier x2hSumG
  rw [Matrix.sum_mul, Matrix.trace_sum, Int.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p _
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, cube_kind_trace]
  simp only [x2hAct_tr1, x2hAct_tr2, x2hAct_tr3]
  rw [x2hGC_cast]
  unfold x2hWeight x2hDen
  push_cast
  ring

/-! ## The per-key facts (mirror forms of the bridge's `trace_count`, `standard_split`, `empty_kinds`) -/

theorem x2hTraceCount (b : x2Key 0) :
    (x2hCarrier (x2hTau b) * x2hKindProj (x2hTau b) (x2KeyKind 0 b)).trace =
      ((x2KeyDegree 0 b * x2KeySize 0 b : ℕ) : ℂ) := by
  rw [carrier_kind_trace, x2hCountCheck b]
  push_cast
  ring

theorem x2hStdSplit (b : x2Key 0) (hb : x2KeyDegree 0 b = 2) :
    (x2hCarrier (x2hTau b) * x2hKindProj (x2hTau b) 2 * x2hSlotPerm (x2hTau b) x2Swap01Idx).trace = 0 := by
  have h3 := x2hDeg2Check b hb
  unfold x2hCarrier
  rw [Matrix.sum_mul, Matrix.sum_mul, Matrix.trace_sum]
  apply Finset.sum_eq_zero
  intro p _
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_smul, cube_split _ _ h3, smul_zero]

theorem x2hEmptyKinds (τ : Fin 7 × Fin 7 × Fin 7) (h1 : τ.1 ≤ τ.2.1) (h2 : τ.2.1 ≤ τ.2.2) (k : ℕ)
    (hk : k < x2hNumKinds τ) (hno : ∀ b : x2Key 0, x2hTau b = τ → x2KeyKind 0 b ≠ k) :
    (x2hCarrier τ * x2hKindProj τ k).trace = 0 := by
  rcases x2hEmptyCheck τ h1 h2 k hk with ⟨b, hb, hkb⟩ | h0
  · exact absurd hkb (hno b hb)
  · rw [carrier_kind_trace, h0]
    simp

end ThreeCopyQutritWerner.X2Sites
