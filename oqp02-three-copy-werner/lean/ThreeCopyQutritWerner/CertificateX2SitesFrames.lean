module

public import ThreeCopyQutritWerner.CertificateX2SitesScan
public import ThreeCopyQutritWerner.CertificateX2SitesPerm
public import ThreeCopyQutritWerner.CertificateDescendantSourceSizes

@[expose] public section


/-!
# The three sectors' sparse frames as entry families

`x2sE0 t`, `x2sE1 t`, `x2sE2 t` are the archive's literal frame entry lists
(`certificateLocalFrameEntries{s}_{t}`) over the sizes `certificateDescendantFrames{2,1,2}SourceSize`
(so `certificateMatrixFromSparseEntries (x2sE1 t)` is the sector-1 source frame of type `t`).
Unit slots are laid out as `x2sOff t + a * m t + b`, `x2sOff t = ∑_{t' < t} m t' ^ 2` (513 slots).
-/

set_option maxRecDepth 100000

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner
namespace X2Sites

open X2

/-! ## Entry families -/

def x2sE0 : (t : Fin 7) → List (Word × Fin (certificateDescendantFrames2SourceSize t) × ℤ) := by
  exact
    Fin.cases (certificateLocalFrameEntries0_0) <|
    Fin.cases (certificateLocalFrameEntries0_1) <|
    Fin.cases (certificateLocalFrameEntries0_2) <|
    Fin.cases (certificateLocalFrameEntries0_3) <|
    Fin.cases (certificateLocalFrameEntries0_4) <|
    Fin.cases (certificateLocalFrameEntries0_5) <|
    Fin.cases (certificateLocalFrameEntries0_6) <|
    Fin.rec0

def x2sE1 : (t : Fin 8) → List (Word × Fin (certificateDescendantFrames1SourceSize t) × ℤ) := by
  exact
    Fin.cases (certificateLocalFrameEntries1_0) <|
    Fin.cases (certificateLocalFrameEntries1_1) <|
    Fin.cases (certificateLocalFrameEntries1_2) <|
    Fin.cases (certificateLocalFrameEntries1_3) <|
    Fin.cases (certificateLocalFrameEntries1_4) <|
    Fin.cases (certificateLocalFrameEntries1_5) <|
    Fin.cases (certificateLocalFrameEntries1_6) <|
    Fin.cases (certificateLocalFrameEntries1_7) <|
    Fin.rec0

def x2sE2 : (t : Fin 7) → List (Word × Fin (certificateDescendantFrames2SourceSize t) × ℤ) := by
  exact
    Fin.cases (certificateLocalFrameEntries2_0) <|
    Fin.cases (certificateLocalFrameEntries2_1) <|
    Fin.cases (certificateLocalFrameEntries2_2) <|
    Fin.cases (certificateLocalFrameEntries2_3) <|
    Fin.cases (certificateLocalFrameEntries2_4) <|
    Fin.cases (certificateLocalFrameEntries2_5) <|
    Fin.cases (certificateLocalFrameEntries2_6) <|
    Fin.rec0

/-- Slot offsets of the types of sectors 0 and 2. -/
def x2sOff0 : Fin 7 → ℕ := ![0, 1, 17, 42, 67, 292, 392]

/-- Slot offsets of the types of sector 1. -/
def x2sOff1 : Fin 8 → ℕ := ![0, 1, 5, 9, 90, 139, 188, 477]

/-! ## Layout -/

theorem ij_lt (m i j : ℕ) (hi : i < m) (hj : j < m) : i * m + j < m * m := by
  calc i * m + j < i * m + m := by omega
    _ = (i + 1) * m := by ring
    _ ≤ m * m := Nat.mul_le_mul_right m hi

theorem layout_lt {T : ℕ} (m off : Fin T → ℕ) (L : ℕ) (hend : ∀ t, off t + m t * m t ≤ L) :
    ∀ t (i j : Fin (m t)), off t + i * m t + j < L := by
  intro t i j
  have h1 := ij_lt (m t) i j i.isLt j.isLt
  have h2 := hend t
  generalize (i : ℕ) * m t = A at h1 ⊢
  generalize m t * m t = B at h1 h2
  omega

theorem layout_inj {T : ℕ} (m off : Fin T → ℕ)
    (hstep : ∀ t t' : Fin T, (t : ℕ) < t' → off t + m t * m t ≤ off t') :
    ∀ t t' (i j : Fin (m t)) (i' j' : Fin (m t')),
      off t + i * m t + j = off t' + i' * m t' + j' → t = t' ∧ (i : ℕ) = i' ∧ (j : ℕ) = j' := by
  intro t t' i j i' j' h
  have k1 := ij_lt (m t) i j i.isLt j.isLt
  have k2 := ij_lt (m t') i' j' i'.isLt j'.isLt
  rcases lt_trichotomy (t : ℕ) (t' : ℕ) with hlt | heq | hgt
  · exfalso
    have hs := hstep t t' hlt
    generalize (i : ℕ) * m t = A at h k1
    generalize (i' : ℕ) * m t' = A' at h k2
    generalize m t * m t = B at k1 hs
    omega
  · have htt : t = t' := Fin.ext heq
    subst htt
    have e : (i : ℕ) * m t + j = i' * m t + j' := by omega
    have hm : 0 < m t := lt_of_le_of_lt (Nat.zero_le _) i.isLt
    have hd1 : ((i : ℕ) * m t + j) / m t = i := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt j.isLt, Nat.zero_add]
    have hd2 : ((i' : ℕ) * m t + j') / m t = i' := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt j'.isLt, Nat.zero_add]
    have hii : (i : ℕ) = i' := by
      rw [← hd1, ← hd2, e]
    refine ⟨rfl, hii, ?_⟩
    rw [hii] at e
    omega
  · exfalso
    have hs := hstep t' t hgt
    generalize (i : ℕ) * m t = A at h k1
    generalize (i' : ℕ) * m t' = A' at h k2
    generalize m t' * m t' = B at k2 hs
    omega

/-! ## Kernel facts about the three families -/

theorem x2sE0_absSum : ∀ t, absSum (x2sE0 t) ≤ 300 := by decide +kernel
theorem x2sE1_absSum : ∀ t, absSum (x2sE1 t) ≤ 300 := by decide +kernel
theorem x2sE2_absSum : ∀ t, absSum (x2sE2 t) ≤ 300 := by decide +kernel

theorem x2s0_step : ∀ t t' : Fin 7, (t : ℕ) < t' →
    x2sOff0 t + certificateDescendantFrames2SourceSize t * certificateDescendantFrames2SourceSize t ≤
      x2sOff0 t' := by decide +kernel

theorem x2s1_step : ∀ t t' : Fin 8, (t : ℕ) < t' →
    x2sOff1 t + certificateDescendantFrames1SourceSize t * certificateDescendantFrames1SourceSize t ≤
      x2sOff1 t' := by decide +kernel

theorem x2s0_end : ∀ t : Fin 7,
    x2sOff0 t + certificateDescendantFrames2SourceSize t * certificateDescendantFrames2SourceSize t ≤ 513 := by
  decide +kernel

theorem x2s1_end : ∀ t : Fin 8,
    x2sOff1 t + certificateDescendantFrames1SourceSize t * certificateDescendantFrames1SourceSize t ≤ 513 := by
  decide +kernel

theorem x2s0_big : (∑ t : Fin 7, certificateDescendantFrames2SourceSize t * certificateDescendantFrames2SourceSize t) *
    (729 * (2 * (300 * 300))) < 2 ^ (48 - 1) := by decide +kernel

theorem x2s1_big : (∑ t : Fin 8, certificateDescendantFrames1SourceSize t * certificateDescendantFrames1SourceSize t) *
    (729 * (2 * (300 * 300))) < 2 ^ (48 - 1) := by decide +kernel

/-! ## Scan constants of the three sectors -/

def x2sTys0 : List TyTab := List.ofFn fun t => mkTy 48 (x2sOff0 t) (x2sE0 t)
def x2sTys1 : List TyTab := List.ofFn fun t => mkTy 48 (x2sOff1 t) (x2sE1 t)
def x2sTys2 : List TyTab := List.ofFn fun t => mkTy 48 (x2sOff0 t) (x2sE2 t)
def x2sMask0 : ℕ := lorAll (List.ofFn fun t => rmask (x2sE0 t))
def x2sMask1 : ℕ := lorAll (List.ofFn fun t => rmask (x2sE1 t))
def x2sMask2 : ℕ := lorAll (List.ofFn fun t => rmask (x2sE2 t))

/-- The diagram register sets of the sectors (as in `certificateLocalDecomposition{0,1,2}Compression`). -/
abbrev x2sS0 : Finset (Fin 6) := {5}
abbrev x2sS1 : Finset (Fin 6) := {3, 4, 5}
abbrev x2sS2 : Finset (Fin 6) := {1, 2, 3, 4, 5}

end X2Sites
end ThreeCopyQutritWerner
