module

public import ThreeCopyQutritWerner.CertificateX2SitesFrames
public import ThreeCopyQutritWerner.CertificateX2SitesCompData1

@[expose] public section


/-! Kernel checks of sector-1 pivot compressions, 8 diagrams per
declaration, 4 declarations per module (memory stays small). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 1000

namespace ThreeCopyQutritWerner.X2Sites

open X2

theorem x2sComp1_check28 : ∀ p : Fin 513, 224 ≤ (p : ℕ) → (p : ℕ) < 232 →
    finish (offset 48 (48 - 1) 513) (x2sComp1.getD p 0)
      (scanM x2sMask1 x2sTys1 (3 ^ (rowPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 0 : ℕ)) (3 ^ (rowPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 1 : ℕ)) (3 ^ (rowPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 2 : ℕ)) (3 ^ (rowPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 3 : ℕ)) (3 ^ (rowPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 4 : ℕ)) (3 ^ (rowPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 5 : ℕ))
        (3 ^ (colPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 0 : ℕ)) (3 ^ (colPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 1 : ℕ)) (3 ^ (colPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 2 : ℕ)) (3 ^ (colPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 3 : ℕ)) (3 ^ (colPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 4 : ℕ)) (3 ^ (colPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 5 : ℕ)) 729 (0, 0)) = true := by
  decide +kernel

theorem x2sComp1_check29 : ∀ p : Fin 513, 232 ≤ (p : ℕ) → (p : ℕ) < 240 →
    finish (offset 48 (48 - 1) 513) (x2sComp1.getD p 0)
      (scanM x2sMask1 x2sTys1 (3 ^ (rowPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 0 : ℕ)) (3 ^ (rowPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 1 : ℕ)) (3 ^ (rowPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 2 : ℕ)) (3 ^ (rowPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 3 : ℕ)) (3 ^ (rowPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 4 : ℕ)) (3 ^ (rowPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 5 : ℕ))
        (3 ^ (colPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 0 : ℕ)) (3 ^ (colPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 1 : ℕ)) (3 ^ (colPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 2 : ℕ)) (3 ^ (colPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 3 : ℕ)) (3 ^ (colPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 4 : ℕ)) (3 ^ (colPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 5 : ℕ)) 729 (0, 0)) = true := by
  decide +kernel

theorem x2sComp1_check30 : ∀ p : Fin 513, 240 ≤ (p : ℕ) → (p : ℕ) < 248 →
    finish (offset 48 (48 - 1) 513) (x2sComp1.getD p 0)
      (scanM x2sMask1 x2sTys1 (3 ^ (rowPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 0 : ℕ)) (3 ^ (rowPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 1 : ℕ)) (3 ^ (rowPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 2 : ℕ)) (3 ^ (rowPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 3 : ℕ)) (3 ^ (rowPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 4 : ℕ)) (3 ^ (rowPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 5 : ℕ))
        (3 ^ (colPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 0 : ℕ)) (3 ^ (colPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 1 : ℕ)) (3 ^ (colPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 2 : ℕ)) (3 ^ (colPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 3 : ℕ)) (3 ^ (colPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 4 : ℕ)) (3 ^ (colPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 5 : ℕ)) 729 (0, 0)) = true := by
  decide +kernel

theorem x2sComp1_check31 : ∀ p : Fin 513, 248 ≤ (p : ℕ) → (p : ℕ) < 256 →
    finish (offset 48 (48 - 1) 513) (x2sComp1.getD p 0)
      (scanM x2sMask1 x2sTys1 (3 ^ (rowPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 0 : ℕ)) (3 ^ (rowPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 1 : ℕ)) (3 ^ (rowPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 2 : ℕ)) (3 ^ (rowPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 3 : ℕ)) (3 ^ (rowPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 4 : ℕ)) (3 ^ (rowPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 5 : ℕ))
        (3 ^ (colPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 0 : ℕ)) (3 ^ (colPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 1 : ℕ)) (3 ^ (colPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 2 : ℕ)) (3 ^ (colPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 3 : ℕ)) (3 ^ (colPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 4 : ℕ)) (3 ^ (colPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 5 : ℕ)) 729 (0, 0)) = true := by
  decide +kernel

end ThreeCopyQutritWerner.X2Sites
