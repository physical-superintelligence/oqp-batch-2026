module

public import ThreeCopyQutritWerner.CertificateX2BridgeKeyFacts
public import ThreeCopyQutritWerner.CertificateX2SitesDictFacts

@[expose] public section


/-!
# The bridge's per-site facts `X2SiteFacts`

`x2SiteFacts_of_trans`: for any `X2Data` with the exact parity transfers
(`D.transS = X2.x2TransS`, `D.transA = X2.x2TransA`; the concrete `x2DataConcrete` has them by
definition) the explicit unit weights `x2SitesW 1`, `x2SitesW 2` satisfy all five fields of the
bridge's `X2SiteFacts` (unit, dictionary and endpoint-target identities). The finite facts are the
kernel checks of CertificateX2SitesComp/Unit/Dict*; this module only identifies the bridge's
compressions with the mirrors of CertificateX2SitesFacts (same bodies, `rfl`).
-/

set_option maxRecDepth 100000

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner.X2Sites

open X2

theorem x2sFrames0_eq (t : Fin 7) : certificateDescendantFrames0Source t = x2sSource0 t := by
  fin_cases t <;> rfl

theorem x2sCompM1_eq (w : Equiv.Perm (Fin 6) → ℂ) (t : Fin 8) :
    certificateLocalDecomposition1Compression w t = x2sCompM1 w t := rfl

theorem x2sCompM2_eq (w : Equiv.Perm (Fin 6) → ℂ) (t : Fin 7) :
    certificateLocalDecomposition2Compression w t = x2sCompM2 w t := rfl

theorem x2sCompM0_eq (w : Equiv.Perm (Fin 6) → ℂ) (t : Fin 7) :
    certificateLocalDecomposition0Compression w t = x2sCompM0 w t := by
  unfold certificateLocalDecomposition0Compression x2sCompM0
  rw [x2sFrames0_eq]

/-- Entry of a combination of sector-0 units. -/
theorem x2s_units0_apply (c : X2U 0 → ℂ) (t : Fin 7) (i j : Fin (certificatePhysicalFrameSystem0.size t)) :
    (∑ u' : X2U 0, c u' • x2UnitMatrix 0 certificatePhysicalFrameSystem0.size
      (fun t : Fin 7 => ((Fin.castSucc t : Fin 8) : ℕ)) u' t) i j =
      c (x2UnitAt 0 certificatePhysicalFrameSystem0.size Fin.castSucc x2_size0 t i j) := by
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul,
    x2UnitMatrix_apply_eq 0 certificatePhysicalFrameSystem0.size Fin.castSucc x2_size0,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem x2SiteFacts_of_trans (D : X2Data) (hS : D.transS = X2.x2TransS) (hA : D.transA = X2.x2TransA) :
    X2SiteFacts D (x2SitesW 1) (x2SitesW 2) where
  unit1 := by
    intro u t
    ext i j
    rw [x2sCompM1_eq, x2sUnit1M]
    rfl
  unit2 := by
    intro u t
    ext i j
    rw [x2sCompM2_eq, x2sUnit2M]
    rfl
  dict1 := by
    intro u t
    ext i j
    rw [x2sCompM0_eq, x2sDict1M D hS hA, x2s_units0_apply]
    rfl
  dict2 := by
    intro u t
    ext i j
    rw [x2sCompM0_eq, x2sDict2M D hS hA, x2s_units0_apply]
    rfl
  target := by
    intro t
    rw [x2sCompM0_eq]
    exact x2sTargetM t

end ThreeCopyQutritWerner.X2Sites
