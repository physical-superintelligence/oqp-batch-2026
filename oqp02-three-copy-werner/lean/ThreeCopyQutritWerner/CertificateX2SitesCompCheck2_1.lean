module

public import ThreeCopyQutritWerner.CertificateX2SitesFrames
public import ThreeCopyQutritWerner.CertificateX2SitesCompData2

@[expose] public section


/-! Kernel checks of sector-2 pivot compressions, 8 diagrams per
declaration, 4 declarations per module (memory stays small). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 1000

namespace ThreeCopyQutritWerner.X2Sites

open X2

theorem x2sComp2_check4 : ∀ p : Fin 513, 32 ≤ (p : ℕ) → (p : ℕ) < 40 →
    finish (offset 48 (48 - 1) 513) (x2sComp2.getD p 0)
      (scanM x2sMask2 x2sTys2 (3 ^ (rowPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 0 : ℕ)) (3 ^ (rowPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 1 : ℕ)) (3 ^ (rowPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 2 : ℕ)) (3 ^ (rowPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 3 : ℕ)) (3 ^ (rowPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 4 : ℕ)) (3 ^ (rowPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 5 : ℕ))
        (3 ^ (colPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 0 : ℕ)) (3 ^ (colPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 1 : ℕ)) (3 ^ (colPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 2 : ℕ)) (3 ^ (colPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 3 : ℕ)) (3 ^ (colPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 4 : ℕ)) (3 ^ (colPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 5 : ℕ)) 729 (0, 0)) = true := by
  decide +kernel

theorem x2sComp2_check5 : ∀ p : Fin 513, 40 ≤ (p : ℕ) → (p : ℕ) < 48 →
    finish (offset 48 (48 - 1) 513) (x2sComp2.getD p 0)
      (scanM x2sMask2 x2sTys2 (3 ^ (rowPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 0 : ℕ)) (3 ^ (rowPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 1 : ℕ)) (3 ^ (rowPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 2 : ℕ)) (3 ^ (rowPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 3 : ℕ)) (3 ^ (rowPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 4 : ℕ)) (3 ^ (rowPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 5 : ℕ))
        (3 ^ (colPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 0 : ℕ)) (3 ^ (colPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 1 : ℕ)) (3 ^ (colPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 2 : ℕ)) (3 ^ (colPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 3 : ℕ)) (3 ^ (colPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 4 : ℕ)) (3 ^ (colPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 5 : ℕ)) 729 (0, 0)) = true := by
  decide +kernel

theorem x2sComp2_check6 : ∀ p : Fin 513, 48 ≤ (p : ℕ) → (p : ℕ) < 56 →
    finish (offset 48 (48 - 1) 513) (x2sComp2.getD p 0)
      (scanM x2sMask2 x2sTys2 (3 ^ (rowPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 0 : ℕ)) (3 ^ (rowPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 1 : ℕ)) (3 ^ (rowPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 2 : ℕ)) (3 ^ (rowPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 3 : ℕ)) (3 ^ (rowPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 4 : ℕ)) (3 ^ (rowPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 5 : ℕ))
        (3 ^ (colPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 0 : ℕ)) (3 ^ (colPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 1 : ℕ)) (3 ^ (colPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 2 : ℕ)) (3 ^ (colPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 3 : ℕ)) (3 ^ (colPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 4 : ℕ)) (3 ^ (colPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 5 : ℕ)) 729 (0, 0)) = true := by
  decide +kernel

theorem x2sComp2_check7 : ∀ p : Fin 513, 56 ≤ (p : ℕ) → (p : ℕ) < 64 →
    finish (offset 48 (48 - 1) 513) (x2sComp2.getD p 0)
      (scanM x2sMask2 x2sTys2 (3 ^ (rowPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 0 : ℕ)) (3 ^ (rowPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 1 : ℕ)) (3 ^ (rowPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 2 : ℕ)) (3 ^ (rowPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 3 : ℕ)) (3 ^ (rowPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 4 : ℕ)) (3 ^ (rowPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 5 : ℕ))
        (3 ^ (colPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 0 : ℕ)) (3 ^ (colPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 1 : ℕ)) (3 ^ (colPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 2 : ℕ)) (3 ^ (colPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 3 : ℕ)) (3 ^ (colPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 4 : ℕ)) (3 ^ (colPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 5 : ℕ)) 729 (0, 0)) = true := by
  decide +kernel

end ThreeCopyQutritWerner.X2Sites
