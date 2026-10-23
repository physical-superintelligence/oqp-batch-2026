module

public import ThreeCopyQutritWerner.CertificateX2SitesFrames
public import ThreeCopyQutritWerner.CertificateX2SitesCompData0

@[expose] public section


/-! Kernel checks of sector-0 pivot compressions, 8 diagrams per
declaration, 4 declarations per module (memory stays small). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 1000

namespace ThreeCopyQutritWerner.X2Sites

open X2

theorem x2sComp0_check0 : ∀ p : Fin 513, (p : ℕ) < 8 →
    finish (offset 48 (48 - 1) 513) (x2sComp0.getD p 0)
      (scanM x2sMask0 x2sTys0 (3 ^ (rowPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 0 : ℕ)) (3 ^ (rowPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 1 : ℕ)) (3 ^ (rowPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 2 : ℕ)) (3 ^ (rowPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 3 : ℕ)) (3 ^ (rowPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 4 : ℕ)) (3 ^ (rowPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 5 : ℕ))
        (3 ^ (colPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 0 : ℕ)) (3 ^ (colPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 1 : ℕ)) (3 ^ (colPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 2 : ℕ)) (3 ^ (colPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 3 : ℕ)) (3 ^ (colPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 4 : ℕ)) (3 ^ (colPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 5 : ℕ)) 729 (0, 0)) = true := by
  decide +kernel

theorem x2sComp0_check1 : ∀ p : Fin 513, 8 ≤ (p : ℕ) → (p : ℕ) < 16 →
    finish (offset 48 (48 - 1) 513) (x2sComp0.getD p 0)
      (scanM x2sMask0 x2sTys0 (3 ^ (rowPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 0 : ℕ)) (3 ^ (rowPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 1 : ℕ)) (3 ^ (rowPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 2 : ℕ)) (3 ^ (rowPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 3 : ℕ)) (3 ^ (rowPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 4 : ℕ)) (3 ^ (rowPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 5 : ℕ))
        (3 ^ (colPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 0 : ℕ)) (3 ^ (colPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 1 : ℕ)) (3 ^ (colPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 2 : ℕ)) (3 ^ (colPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 3 : ℕ)) (3 ^ (colPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 4 : ℕ)) (3 ^ (colPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 5 : ℕ)) 729 (0, 0)) = true := by
  decide +kernel

theorem x2sComp0_check2 : ∀ p : Fin 513, 16 ≤ (p : ℕ) → (p : ℕ) < 24 →
    finish (offset 48 (48 - 1) 513) (x2sComp0.getD p 0)
      (scanM x2sMask0 x2sTys0 (3 ^ (rowPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 0 : ℕ)) (3 ^ (rowPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 1 : ℕ)) (3 ^ (rowPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 2 : ℕ)) (3 ^ (rowPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 3 : ℕ)) (3 ^ (rowPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 4 : ℕ)) (3 ^ (rowPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 5 : ℕ))
        (3 ^ (colPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 0 : ℕ)) (3 ^ (colPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 1 : ℕ)) (3 ^ (colPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 2 : ℕ)) (3 ^ (colPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 3 : ℕ)) (3 ^ (colPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 4 : ℕ)) (3 ^ (colPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 5 : ℕ)) 729 (0, 0)) = true := by
  decide +kernel

theorem x2sComp0_check3 : ∀ p : Fin 513, 24 ≤ (p : ℕ) → (p : ℕ) < 32 →
    finish (offset 48 (48 - 1) 513) (x2sComp0.getD p 0)
      (scanM x2sMask0 x2sTys0 (3 ^ (rowPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 0 : ℕ)) (3 ^ (rowPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 1 : ℕ)) (3 ^ (rowPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 2 : ℕ)) (3 ^ (rowPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 3 : ℕ)) (3 ^ (rowPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 4 : ℕ)) (3 ^ (rowPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 5 : ℕ))
        (3 ^ (colPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 0 : ℕ)) (3 ^ (colPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 1 : ℕ)) (3 ^ (colPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 2 : ℕ)) (3 ^ (colPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 3 : ℕ)) (3 ^ (colPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 4 : ℕ)) (3 ^ (colPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 5 : ℕ)) 729 (0, 0)) = true := by
  decide +kernel

end ThreeCopyQutritWerner.X2Sites
