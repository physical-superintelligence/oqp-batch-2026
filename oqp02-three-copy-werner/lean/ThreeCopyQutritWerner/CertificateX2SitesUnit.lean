module

public import ThreeCopyQutritWerner.CertificateX2SitesWShape1
public import ThreeCopyQutritWerner.CertificateX2SitesWShape2
public import ThreeCopyQutritWerner.CertificateX2SitesShape0
public import ThreeCopyQutritWerner.CertificateX2SitesShape1
public import ThreeCopyQutritWerner.CertificateX2SitesShape2
public import ThreeCopyQutritWerner.CertificateX2SitesUnitCheck1_0
public import ThreeCopyQutritWerner.CertificateX2SitesUnitCheck1_1
public import ThreeCopyQutritWerner.CertificateX2SitesUnitCheck1_2
public import ThreeCopyQutritWerner.CertificateX2SitesUnitCheck2_0
public import ThreeCopyQutritWerner.CertificateX2SitesUnitCheck2_1
public import ThreeCopyQutritWerner.CertificateX2SitesUnitCheck2_2
public import ThreeCopyQutritWerner.CertificateX2PackedGlue

@[expose] public section


/-!
# The unit weights invert the pivot compressions (s = 1, 2)

`x2sW s` (row `u`, entry `p`) holds `Wnum_s[p, u] + 2^25` (`W_s = L_s[:, piv]⁻¹ = Wnum_s / den_s`).
Kernel checks by the natural axpy (`natAxpyCheck`): for every unit `u`,
`∑_p Wnum_s[p, u] · C_s(piv p) = den_s · e_u` on the 513 unit slots.
`x2sUnit_int`: the integer identity, for the fibers of `CertificateX2SitesComp`.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open scoped BigOperators

namespace ThreeCopyQutritWerner.X2Sites

open X2


/-! ## List helpers -/

theorem getD_mem_of_lt {l : List ℕ} {a : ℕ} (h : a < l.length) : l.getD a 0 ∈ l := by
  rw [List.getD_eq_getElem _ _ h]
  exact List.getElem_mem h

theorem getD_mem_of_lt' {l : List (List ℕ)} {a : ℕ} (h : a < l.length) : l.getD a [] ∈ l := by
  rw [List.getD_eq_getElem _ _ h]
  exact List.getElem_mem h

theorem ofFn_getD (l : List ℕ) (n : ℕ) (h : l.length = n) :
    List.ofFn (fun a : Fin n => l.getD a 0) = l := by
  subst h
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp [List.getD_eq_getElem _ _ h2]

/-! ## Shapes and bounds (kernel) -/

/-! ## The natural axpy checks (kernel) -/

theorem x2sUnit1_check (u : ℕ) (hu : u < 513) : natAxpyCheck 48 513 25 (x2sW1.getD u []) x2sComp1
    (offset 48 (48 - 1) 513 + 57153600 * 2 ^ (48 * u)) (natAxpyCorr 48 513 25 x2sComp1) = true := by
  by_cases h0 : u < 64
  · exact x2sUnit1_check0 u hu (by omega) h0
  by_cases h1 : u < 128
  · exact x2sUnit1_check1 u hu (by omega) h1
  by_cases h2 : u < 192
  · exact x2sUnit1_check2 u hu (by omega) h2
  by_cases h3 : u < 256
  · exact x2sUnit1_check3 u hu (by omega) h3
  by_cases h4 : u < 320
  · exact x2sUnit1_check4 u hu (by omega) h4
  by_cases h5 : u < 384
  · exact x2sUnit1_check5 u hu (by omega) h5
  by_cases h6 : u < 448
  · exact x2sUnit1_check6 u hu (by omega) h6
  by_cases h7 : u < 512
  · exact x2sUnit1_check7 u hu (by omega) h7
  · exact x2sUnit1_check8 u hu (by omega) hu

theorem x2sUnit2_check (u : ℕ) (hu : u < 513) : natAxpyCheck 48 513 25 (x2sW2.getD u []) x2sComp2
    (offset 48 (48 - 1) 513 + 6350400 * 2 ^ (48 * u)) (natAxpyCorr 48 513 25 x2sComp2) = true := by
  by_cases h0 : u < 64
  · exact x2sUnit2_check0 u hu (by omega) h0
  by_cases h1 : u < 128
  · exact x2sUnit2_check1 u hu (by omega) h1
  by_cases h2 : u < 192
  · exact x2sUnit2_check2 u hu (by omega) h2
  by_cases h3 : u < 256
  · exact x2sUnit2_check3 u hu (by omega) h3
  by_cases h4 : u < 320
  · exact x2sUnit2_check4 u hu (by omega) h4
  by_cases h5 : u < 384
  · exact x2sUnit2_check5 u hu (by omega) h5
  by_cases h6 : u < 448
  · exact x2sUnit2_check6 u hu (by omega) h6
  by_cases h7 : u < 512
  · exact x2sUnit2_check7 u hu (by omega) h7
  · exact x2sUnit2_check8 u hu (by omega) hu

/-! ## Soundness -/

/-- The unit fiber `den · e_u` (offset encoding) has entry `den` at `u`, `0` elsewhere. -/
theorem ent_unit (den u k : ℕ) (hden : den < 2 ^ 47) (hu : u < 513) (hk : k < 513) :
    ent 48 (48 - 1) (offset 48 (48 - 1) 513 + den * 2 ^ (48 * u)) k = if k = u then (den : ℤ) else 0 := by
  have hexp : offset 48 (48 - 1) 513 + den * 2 ^ (48 * u) =
      ∑ s ∈ Finset.range 513, (2 ^ 47 + if s = u then den else 0) * 2 ^ (48 * s) := by
    unfold offset
    rw [repunit_eq 48 513 (by norm_num), Finset.mul_sum]
    simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq' (Finset.range 513) u, if_pos (Finset.mem_range.mpr hu)]
    all_goals norm_num
  have hf : ∀ s, (2 ^ 47 + if s = u then den else 0) < 2 ^ 48 := by
    intro s
    split_ifs <;> omega
  have hd := sum_digit (2 ^ 48) 513 (fun s => 2 ^ 47 + if s = u then den else 0) (by positivity) hf k hk
  unfold ent dig
  rw [hexp]
  simp only [pow_mul]
  rw [hd]
  split_ifs <;> norm_num

/-- One natural axpy check gives the integer identity of the weighted fibers. -/
theorem axpy_int (Wr : List ℕ) (Fs : List ℕ) (oA : ℕ) (outE : ℕ)
    (hWr : Wr.length = 513) (hWb : Wr.all (fun x => Nat.blt x (2 ^ (oA + 1))) = true)
    (hFs : Fs.length = 513 ∧ ∀ p < 513, fiberOK (Fs.getD p 0) = true)
    (hoA : 513 * (2 ^ oA * 2 ^ 9) < 2 ^ (48 - 1))
    (hcheck : natAxpyCheck 48 513 oA Wr Fs outE (natAxpyCorr 48 513 oA Fs) = true)
    (k : ℕ) (hk : k < 513) :
    ∑ p : Fin 513, ((Wr.getD p 0 : ℤ) - 2 ^ oA) * ent 48 (48 - 1) (Fs.getD p 0) k =
      ent 48 (48 - 1) outE k := by
  have hWall := List.all_eq_true.mp hWb
  have hE : ∀ p : Fin 513, Fs.getD p 0 < 2 ^ (48 * 513) := fun p => fiberOK_lt _ (hFs.2 p p.isLt)
  have hentb : ∀ (p : Fin 513) (k' : ℕ), k' < 513 → |ent 48 (48 - 1) (Fs.getD p 0) k'| ≤ 2 ^ 9 :=
    fun p k' hk' => fiberOK_ent _ (hFs.2 p p.isLt) k' hk'
  have hgb : ∀ p : Fin 513, |((Wr.getD p 0 : ℕ) : ℤ) - 2 ^ oA| ≤ 2 ^ oA := by
    intro p
    have h := hWall _ (getD_mem_of_lt (lt_of_lt_of_eq p.isLt hWr.symm))
    have h' := Nat.blt_eq.mp h
    rw [abs_le]
    have h2 : ((Wr.getD p 0 : ℕ) : ℤ) < 2 ^ (oA + 1) := by exact_mod_cast h'
    have h3 : (0 : ℤ) ≤ ((Wr.getD p 0 : ℕ) : ℤ) := Int.natCast_nonneg _
    rw [pow_succ] at h2
    constructor <;> linarith
  have hlin : ∀ k' < 513, |∑ p : Fin 513, ((Wr.getD p 0 : ℕ) - 2 ^ oA : ℤ) *
      ent 48 (48 - 1) (Fs.getD p 0) k'| < 2 ^ (48 - 1) := by
    intro k' hk'
    calc |∑ p : Fin 513, ((Wr.getD p 0 : ℕ) - 2 ^ oA : ℤ) * ent 48 (48 - 1) (Fs.getD p 0) k'|
        ≤ ∑ p : Fin 513, |((Wr.getD p 0 : ℕ) - 2 ^ oA : ℤ) * ent 48 (48 - 1) (Fs.getD p 0) k'| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p : Fin 513, (2 ^ oA * 2 ^ 9 : ℤ) := by
          apply Finset.sum_le_sum
          intro p _
          rw [abs_mul]
          exact mul_le_mul (hgb p) (hentb p k' hk') (abs_nonneg _) (by positivity)
      _ = 513 * (2 ^ oA * 2 ^ 9 : ℤ) := by simp
      _ < 2 ^ (48 - 1) := by exact_mod_cast hoA
  have hcheck' : natAxpyCheck 48 513 oA (List.ofFn fun p : Fin 513 => Wr.getD p 0)
      (List.ofFn fun p : Fin 513 => Fs.getD p 0) outE
      (natAxpyCorr 48 513 oA (List.ofFn fun p : Fin 513 => Fs.getD p 0)) = true := by
    rw [ofFn_getD Wr 513 hWr, ofFn_getD Fs 513 hFs.1]
    exact hcheck
  exact natAxpy_contract 48 513 oA (fun p : Fin 513 => Wr.getD p 0) (fun p : Fin 513 => Fs.getD p 0)
    outE (by norm_num) hE hlin hcheck' k hk

theorem x2sW_row (Wt : List (List ℕ)) (hWt : ∀ u < 513, rowOK (Wt.getD u []) = true)
    (u : ℕ) (hu : u < 513) :
    (Wt.getD u []).length = 513 ∧ (Wt.getD u []).all (fun x => Nat.blt x (2 ^ (25 + 1))) = true := by
  have h := hWt u hu
  unfold rowOK at h
  simp only [Bool.and_eq_true] at h
  exact ⟨beq_iff_eq.mp h.1, h.2⟩

/-- Sector 1: `∑_p Wnum_1[p, u] · C_1(piv p)[k] = den_1 · [k = u]`. -/
theorem x2sUnit1_int (u k : ℕ) (hu : u < 513) (hk : k < 513) :
    ∑ p : Fin 513, (((x2sW1.getD u []).getD p 0 : ℤ) - 2 ^ 25) * ent 48 (48 - 1) (x2sComp1.getD p 0) k =
      if k = u then (57153600 : ℤ) else 0 := by
  obtain ⟨hl, hb⟩ := x2sW_row x2sW1 x2sW1_shape u hu
  rw [axpy_int (x2sW1.getD u []) x2sComp1 25 _ hl hb x2sComp1_shape (by norm_num)
    (x2sUnit1_check u hu) k hk]
  exact ent_unit 57153600 u k (by norm_num) hu hk

/-- Sector 2: `∑_p Wnum_2[p, u] · C_2(piv p)[k] = den_2 · [k = u]`. -/
theorem x2sUnit2_int (u k : ℕ) (hu : u < 513) (hk : k < 513) :
    ∑ p : Fin 513, (((x2sW2.getD u []).getD p 0 : ℤ) - 2 ^ 25) * ent 48 (48 - 1) (x2sComp2.getD p 0) k =
      if k = u then (6350400 : ℤ) else 0 := by
  obtain ⟨hl, hb⟩ := x2sW_row x2sW2 x2sW2_shape u hu
  rw [axpy_int (x2sW2.getD u []) x2sComp2 25 _ hl hb x2sComp2_shape (by norm_num)
    (x2sUnit2_check u hu) k hk]
  exact ent_unit 6350400 u k (by norm_num) hu hk

end ThreeCopyQutritWerner.X2Sites
