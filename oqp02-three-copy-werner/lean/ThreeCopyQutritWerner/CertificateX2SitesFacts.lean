module

public import ThreeCopyQutritWerner.CertificateX2SitesUnits
public import ThreeCopyQutritWerner.CertificateX2SitesComp
public import ThreeCopyQutritWerner.CertificateDiagramOperators
public import ThreeCopyQutritWerner.CertificateDescendantFramesData1
public import ThreeCopyQutritWerner.CertificateDescendantFramesData2

@[expose] public section


/-!
# The per-site unit identities

The explicit unit weights (`x2SitesW s u`, the bridge's `wU s u = ∑_{d ∈ piv} W_s[d, u] δ_{perms[d]}`)
and their compressions. `x2sCompM{0,1,2}` have exactly the bodies of the bridge's
`certificateLocalDecomposition{0,1,2}Compression` (sector 0 with the literal sector-0 frames; the
heavy module CertificateX2SitesBridge identifies them by `rfl`). Main results:
`x2sUnit1M`, `x2sUnit2M` (unit identities in the bridge's `x2UnitMatrix` form).
-/

set_option maxRecDepth 100000

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner.X2Sites

open X2

/-! ## Frames -/

theorem x2sSource1_eq (t : Fin 8) :
    certificateDescendantFrames1Source t = certificateMatrixFromSparseEntries (x2sE1 t) := by
  fin_cases t <;> rfl

theorem x2sSource2_eq (t : Fin 7) :
    certificateDescendantFrames2Source t = certificateMatrixFromSparseEntries (x2sE2 t) := by
  fin_cases t <;> rfl

/-- The literal sector-0 source frames (same as `certificateDescendantFrames0Source`). -/
def x2sSource0 (t : Fin 7) : Matrix Word (Fin (certificateDescendantFrames2SourceSize t)) ℤ :=
  certificateMatrixFromSparseEntries (x2sE0 t)

/-! ## Mirror compressions -/

def x2sCompM0 (w : Equiv.Perm (Fin 6) → ℂ) (t : Fin 7) :
    Matrix (Fin (certificateDescendantFrames2SourceSize t)) (Fin (certificateDescendantFrames2SourceSize t)) ℂ :=
  ((x2sSource0 t).map (Int.cast : ℤ → ℂ))ᴴ * certificateLocalDiagramCombination {5} w *
    (x2sSource0 t).map (Int.cast : ℤ → ℂ)

def x2sCompM1 (w : Equiv.Perm (Fin 6) → ℂ) (t : Fin 8) :
    Matrix (Fin (certificateDescendantFrames1SourceSize t)) (Fin (certificateDescendantFrames1SourceSize t)) ℂ :=
  ((certificateDescendantFrames1Source t).map (Int.cast : ℤ → ℂ))ᴴ *
    certificateLocalDiagramCombination {3, 4, 5} w * (certificateDescendantFrames1Source t).map (Int.cast : ℤ → ℂ)

def x2sCompM2 (w : Equiv.Perm (Fin 6) → ℂ) (t : Fin 7) :
    Matrix (Fin (certificateDescendantFrames2SourceSize t)) (Fin (certificateDescendantFrames2SourceSize t)) ℂ :=
  ((certificateDescendantFrames2Source t).map (Int.cast : ℤ → ℂ))ᴴ *
    certificateLocalDiagramCombination {1, 2, 3, 4, 5} w *
      (certificateDescendantFrames2Source t).map (Int.cast : ℤ → ℂ)

/-- A compression of a diagram combination is the combination of the integer compressions. -/
theorem comp_entry {m : ℕ} (U : Matrix Word (Fin m) ℤ) (S : Finset (Fin 6))
    (w : Equiv.Perm (Fin 6) → ℂ) (i j : Fin m) :
    ((U.map (Int.cast : ℤ → ℂ))ᴴ * certificateLocalDiagramCombination S w * U.map (Int.cast : ℤ → ℂ)) i j =
      ∑ σ, w σ * (((Uᵀ * certificateLocalDiagram (n := Fin 3) (R := ℤ) S σ * U) i j : ℤ) : ℂ) := by
  unfold certificateLocalDiagramCombination
  rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  congr 1
  rw [← certificateLocalDiagram_map (Int.castRingHom ℂ) S σ]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.transpose_apply,
    eq_intCast, star_intCast]
  push_cast
  try rfl

/-! ## The unit identities -/

theorem x2sUnit1M (u : X2U 1) (t : Fin 8) (i j : Fin (certificateDescendantFrames1SourceSize t)) :
    x2sCompM1 (x2SitesW 1 u) t i j =
      if (u.1 : ℕ) = (t : ℕ) ∧ (u.2.1 : ℕ) = i ∧ (u.2.2 : ℕ) = j then 1 else 0 := by
  unfold x2sCompM1
  rw [x2sSource1_eq, comp_entry]
  unfold x2SitesW
  rw [sum_weight_collapse]
  simp only [x2sComp1_spec, x2sWTab1, x2sDen1]
  have hk : x2sOff1 t + (i : ℕ) * certificateDescendantFrames1SourceSize t + j < 513 :=
    layout_lt _ _ 513 x2s1_end t i j
  have hint := x2sUnit1_int (x2sFlatU 1 u) (x2sOff1 t + i * certificateDescendantFrames1SourceSize t + j)
    (x2sFlatU_lt 1 u) hk
  have hcast : ∑ p : Fin 513, (((((x2sW1.getD (x2sFlatU 1 u) []).getD p 0 : ℕ) : ℂ) - 2 ^ 25) /
      ((57153600 : ℕ) : ℂ)) * ((ent 48 (48 - 1) (x2sComp1.getD p 0)
        (x2sOff1 t + i * certificateDescendantFrames1SourceSize t + j) : ℤ) : ℂ) =
      ((∑ p : Fin 513, (((x2sW1.getD (x2sFlatU 1 u) []).getD p 0 : ℤ) - 2 ^ 25) *
        ent 48 (48 - 1) (x2sComp1.getD p 0) (x2sOff1 t + i * certificateDescendantFrames1SourceSize t + j) : ℤ) : ℂ) /
          ((57153600 : ℕ) : ℂ) := by
    rw [Int.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p _
    push_cast
    ring
  refine hcast.trans ?_
  rw [hint]
  have hiff := x2sFlatU_iff 1 u t i j (by rw [x2sMult1]; exact i.isLt) (by rw [x2sMult1]; exact j.isLt)
  rw [x2sOffU1, x2sMult1] at hiff
  by_cases hc : x2sOff1 t + (i : ℕ) * certificateDescendantFrames1SourceSize t + j = x2sFlatU 1 u
  · rw [if_pos hc, if_pos (hiff.mp hc)]
    push_cast
    norm_num
  · rw [if_neg hc, if_neg (fun h => hc (hiff.mpr h))]
    simp

theorem x2sUnit2M (u : X2U 2) (t : Fin 7) (i j : Fin (certificateDescendantFrames2SourceSize t)) :
    x2sCompM2 (x2SitesW 2 u) t i j =
      if (u.1 : ℕ) = ((Fin.castSucc t : Fin 8) : ℕ) ∧ (u.2.1 : ℕ) = i ∧ (u.2.2 : ℕ) = j then 1 else 0 := by
  unfold x2sCompM2
  rw [x2sSource2_eq, comp_entry]
  unfold x2SitesW
  rw [sum_weight_collapse]
  simp only [x2sComp2_spec, x2sWTab2, x2sDen2]
  have hk : x2sOff0 t + (i : ℕ) * certificateDescendantFrames2SourceSize t + j < 513 :=
    layout_lt _ _ 513 x2s0_end t i j
  have hint := x2sUnit2_int (x2sFlatU 2 u) (x2sOff0 t + i * certificateDescendantFrames2SourceSize t + j)
    (x2sFlatU_lt 2 u) hk
  have hcast : ∑ p : Fin 513, (((((x2sW2.getD (x2sFlatU 2 u) []).getD p 0 : ℕ) : ℂ) - 2 ^ 25) /
      ((6350400 : ℕ) : ℂ)) * ((ent 48 (48 - 1) (x2sComp2.getD p 0)
        (x2sOff0 t + i * certificateDescendantFrames2SourceSize t + j) : ℤ) : ℂ) =
      ((∑ p : Fin 513, (((x2sW2.getD (x2sFlatU 2 u) []).getD p 0 : ℤ) - 2 ^ 25) *
        ent 48 (48 - 1) (x2sComp2.getD p 0) (x2sOff0 t + i * certificateDescendantFrames2SourceSize t + j) : ℤ) : ℂ) /
          ((6350400 : ℕ) : ℂ) := by
    rw [Int.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p _
    push_cast
    ring
  refine hcast.trans ?_
  rw [hint]
  have hiff := x2sFlatU_iff 2 u (Fin.castSucc t) i j (by rw [x2sMult2]; exact i.isLt)
    (by rw [x2sMult2]; exact j.isLt)
  rw [x2sOffU2, x2sMult2] at hiff
  by_cases hc : x2sOff0 t + (i : ℕ) * certificateDescendantFrames2SourceSize t + j = x2sFlatU 2 u
  · rw [if_pos hc, if_pos (hiff.mp hc)]
    push_cast
    norm_num
  · rw [if_neg hc, if_neg (fun h => hc (hiff.mpr h))]
    simp

end ThreeCopyQutritWerner.X2Sites
