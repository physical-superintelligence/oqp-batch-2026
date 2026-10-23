module

public import ThreeCopyQutritWerner.CertificateX2PsdRat
public import ThreeCopyQutritWerner.CertificateX2Nh012k0

@[expose] public section


/-! Holomorphic block `012-0` (empty face): the block vanishes. -/

open scoped Matrix ComplexOrder

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner.X2HBlockPsdH0x012k0

def N : Matrix (Fin 1) (Fin 1) ℤ :=
  ThreeCopyQutritWerner.X2Nh.nh_012k0

theorem N_eq_zero : N = 0 := by decide +kernel

theorem psd : (N.map (Int.castRingHom ℂ)).PosSemidef := by
  rw [N_eq_zero]
  first
  | (rw [Matrix.map_zero _ (map_zero _)]; exact Matrix.PosSemidef.zero)
  | (simpa using (Matrix.PosSemidef.zero : (0 : Matrix (Fin 1) (Fin 1) ℂ).PosSemidef))

theorem psd_scaled : ((1 / ((57735991281730516779464839149788173726453690037306728120320000 : ℤ) : ℂ)) • N.map (Int.castRingHom ℂ)).PosSemidef :=
  certificateX2_int_div_posSemidef N 57735991281730516779464839149788173726453690037306728120320000 (by norm_num) psd

/-- The rational block `(1/den) • N`, in the bridge's `x2Complex` form. -/
theorem psd_rat : (((1 / ((57735991281730516779464839149788173726453690037306728120320000 : ℤ) : ℚ)) • N.map (Int.cast : ℤ → ℚ)).map
    (fun q : ℚ => (q : ℂ))).PosSemidef :=
  certificateX2_rat_int_div_posSemidef N 57735991281730516779464839149788173726453690037306728120320000 (by norm_num) psd

end ThreeCopyQutritWerner.X2HBlockPsdH0x012k0
