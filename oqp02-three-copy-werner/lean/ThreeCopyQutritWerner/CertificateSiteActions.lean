module

public import ThreeCopyQutritWerner.CertificateDiagrams
public import ThreeCopyQutritWerner.CertificateLocalGenerators
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section


/-!
# Site matrix units and literal register partial transpose

These identities connect the signed sparse word generators to ordinary site
matrix units. Partial transpose reverses left and right multiplication exactly
at the transposed sites. Everything is stated on the physical word basis; no
representation decomposition or commutant-completeness assumption is used.
-/

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

section MatrixUnits

variable {k : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

/-- The local matrix unit Eᵢⱼ at one physical register, with integer entries. -/
def certificateSiteMatrixUnit (s : Fin k) (i j : n) :
    Matrix (Fin k → n) (Fin k → n) ℤ :=
  fun r c => if c s = j ∧ Function.update c s i = r then 1 else 0

theorem certificateSiteTransition_iff (s : Fin k) (i j : n) (r c : Fin k → n) :
    (c s = j ∧ Function.update c s i = r) ↔
      (r s = i ∧ Function.update r s j = c) := by
  constructor
  · rintro ⟨hc, rfl⟩
    constructor
    · exact Function.update_self _ _ _
    · rw [Function.update_idem, ← hc, Function.update_eq_self]
  · rintro ⟨hr, rfl⟩
    constructor
    · exact Function.update_self _ _ _
    · rw [Function.update_idem, ← hr, Function.update_eq_self]

/-- Left multiplication changes the output word at exactly one register. -/
theorem certificateSiteMatrixUnit_mul_apply (s : Fin k) (i j : n)
    (M : Matrix (Fin k → n) (Fin k → n) ℤ) (r c : Fin k → n) :
    (certificateSiteMatrixUnit s i j * M) r c =
      if r s = i then M (Function.update r s j) c else 0 := by
  simp only [Matrix.mul_apply, certificateSiteMatrixUnit, certificateSiteTransition_iff]
  by_cases h : r s = i <;> simp [h, ite_mul]

/-- Right multiplication changes the input word at exactly one register. -/
theorem certificateMul_siteMatrixUnit_apply (s : Fin k) (i j : n)
    (M : Matrix (Fin k → n) (Fin k → n) ℤ) (r c : Fin k → n) :
    (M * certificateSiteMatrixUnit s i j) r c =
      if c s = j then M r (Function.update c s i) else 0 := by
  simp only [Matrix.mul_apply, certificateSiteMatrixUnit]
  by_cases h : c s = j <;> simp [h, mul_ite]

theorem certificateWordSwap_update_left_mem (S : Finset (Fin k)) (s : Fin k)
    (hs : s ∈ S) (r c : Fin k → n) (a : n) :
    certificateWordSwap S (Function.update r s a) c = certificateWordSwap S r c := by
  ext t
  by_cases ht : t = s
  · subst t; simp [certificateWordSwap, hs]
  · simp [certificateWordSwap, Function.update_of_ne ht]

theorem certificateWordSwap_update_left_notMem (S : Finset (Fin k)) (s : Fin k)
    (hs : s ∉ S) (r c : Fin k → n) (a : n) :
    certificateWordSwap S (Function.update r s a) c =
      Function.update (certificateWordSwap S r c) s a := by
  ext t
  by_cases ht : t = s
  · subst t; simp [certificateWordSwap, hs]
  · simp [certificateWordSwap, Function.update_of_ne ht]

theorem certificateWordSwap_update_right_mem (S : Finset (Fin k)) (s : Fin k)
    (hs : s ∈ S) (r c : Fin k → n) (a : n) :
    certificateWordSwap S r (Function.update c s a) =
      Function.update (certificateWordSwap S r c) s a := by
  ext t
  by_cases ht : t = s
  · subst t; simp [certificateWordSwap, hs]
  · simp [certificateWordSwap, Function.update_of_ne ht]

theorem certificateWordSwap_update_right_notMem (S : Finset (Fin k)) (s : Fin k)
    (hs : s ∉ S) (r c : Fin k → n) (a : n) :
    certificateWordSwap S r (Function.update c s a) = certificateWordSwap S r c := by
  ext t
  by_cases ht : t = s
  · subst t; simp [certificateWordSwap, hs]
  · simp [certificateWordSwap, Function.update_of_ne ht]

/-- On an untransposed site, partial transpose preserves right multiplication. -/
theorem certificateWordTranspose_mul_site_notMem (S : Finset (Fin k)) (s : Fin k)
    (hs : s ∉ S) (i j : n) (M : Matrix (Fin k → n) (Fin k → n) ℤ) :
    certificateWordTranspose S (M * certificateSiteMatrixUnit s i j) =
      certificateWordTranspose S M * certificateSiteMatrixUnit s i j := by
  ext r c
  simp only [certificateWordTranspose, certificateMul_siteMatrixUnit_apply,
    certificateWordSwap_update_left_notMem S s hs,
    certificateWordSwap_update_right_notMem S s hs]
  simp [certificateWordSwap, hs]

/-- On a transposed site, right multiplication becomes left multiplication by Eⱼᵢ. -/
theorem certificateWordTranspose_mul_site_mem (S : Finset (Fin k)) (s : Fin k)
    (hs : s ∈ S) (i j : n) (M : Matrix (Fin k → n) (Fin k → n) ℤ) :
    certificateWordTranspose S (M * certificateSiteMatrixUnit s i j) =
      certificateSiteMatrixUnit s j i * certificateWordTranspose S M := by
  ext r c
  simp only [certificateWordTranspose, certificateMul_siteMatrixUnit_apply,
    certificateSiteMatrixUnit_mul_apply, certificateWordSwap_update_left_mem S s hs,
    certificateWordSwap_update_right_mem S s hs]
  simp [certificateWordSwap, hs]

/-- On an untransposed site, partial transpose preserves left multiplication. -/
theorem certificateWordTranspose_site_mul_notMem (S : Finset (Fin k)) (s : Fin k)
    (hs : s ∉ S) (i j : n) (M : Matrix (Fin k → n) (Fin k → n) ℤ) :
    certificateWordTranspose S (certificateSiteMatrixUnit s i j * M) =
      certificateSiteMatrixUnit s i j * certificateWordTranspose S M := by
  ext r c
  simp only [certificateWordTranspose, certificateSiteMatrixUnit_mul_apply,
    certificateWordSwap_update_left_notMem S s hs,
    certificateWordSwap_update_right_notMem S s hs]
  simp [certificateWordSwap, hs]

/-- On a transposed site, left multiplication becomes right multiplication by Eⱼᵢ. -/
theorem certificateWordTranspose_site_mul_mem (S : Finset (Fin k)) (s : Fin k)
    (hs : s ∈ S) (i j : n) (M : Matrix (Fin k → n) (Fin k → n) ℤ) :
    certificateWordTranspose S (certificateSiteMatrixUnit s i j * M) =
      certificateWordTranspose S M * certificateSiteMatrixUnit s j i := by
  ext r c
  simp only [certificateWordTranspose, certificateSiteMatrixUnit_mul_apply,
    certificateMul_siteMatrixUnit_apply, certificateWordSwap_update_left_mem S s hs,
    certificateWordSwap_update_right_mem S s hs]
  simp [certificateWordSwap, hs]

/-- The ordinary collective matrix-unit generator before partial transpose. -/
def certificateUniformGenerator (i j : n) : Matrix (Fin k → n) (Fin k → n) ℤ :=
  ∑ s : Fin k, certificateSiteMatrixUnit s i j

/-- Fundamental sites act by Eᵢⱼ and dual sites by −Eⱼᵢ. -/
def certificateSignedGenerator (ket : Finset (Fin k)) (i j : n) :
    Matrix (Fin k → n) (Fin k → n) ℤ :=
  ∑ s : Fin k, if s ∈ ket then certificateSiteMatrixUnit s i j
    else -certificateSiteMatrixUnit s j i

/-- Exchanging fundamental and dual sites exchanges i,j and changes the overall sign. -/
theorem certificateSignedGenerator_compl (ket : Finset (Fin k)) (i j : n) :
    certificateSignedGenerator ketᶜ i j = -certificateSignedGenerator ket j i := by
  rw [certificateSignedGenerator, certificateSignedGenerator, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : s ∈ ket <;> simp [hs]

end MatrixUnits

private theorem certificateSparseVector_filterMap {α n : Type*} [DecidableEq n]
    (L : List α) (f : α → Option (n × ℤ)) (w : n) :
    certificateSparseVector (L.filterMap f) w =
      (L.map fun a => match f a with
        | none => 0
        | some b => if b.1 = w then b.2 else 0).sum := by
  induction L with
  | nil => rfl
  | cons a L ih =>
      cases h : f a with
      | none => simpa [h, certificateSparseVector] using ih
      | some b =>
          simpa [h, certificateSparseVector] using
            congrArg (fun z => (if b.1 = w then b.2 else 0) + z) ih

/-- The existing sparse generator is exactly the sum of physical signed site units. -/
theorem certificateLocalGenerator_eq_signed (ket : Finset (Fin 6)) (i j : Fin 3) :
    certificateLocalGenerator ket i j = certificateSignedGenerator ket i j := by
  ext r c
  rw [certificateLocalGenerator, certificateLocalGeneratorWord,
    certificateSparseVector_filterMap, ← List.ofFn_eq_map, Fin.sum_ofFn]
  simp only [certificateSignedGenerator, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : s ∈ ket
  · by_cases hj : c s = j <;>
      simp [hs, hj, certificateSiteMatrixUnit, Matrix.neg_apply]
  · by_cases hi : c s = i <;>
      simp [hs, hi, certificateSiteMatrixUnit, Matrix.neg_apply, neg_ite]

/-- Complementing the signed register convention preserves its full commutant. -/
theorem certificateLocalGenerator_compl (ket : Finset (Fin 6)) (i j : Fin 3) :
    certificateLocalGenerator ketᶜ i j = -certificateLocalGenerator ket j i := by
  simp only [certificateLocalGenerator_eq_signed, certificateSignedGenerator_compl]

end ThreeCopyQutritWerner
