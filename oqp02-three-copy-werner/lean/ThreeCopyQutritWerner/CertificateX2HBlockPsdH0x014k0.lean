module

public import ThreeCopyQutritWerner.CertificateX2HBlockPsdH0x014k0Face
public import ThreeCopyQutritWerner.CertificateX2Nh014k0

@[expose] public section


/-! Holomorphic block `014-0` (3 x 3, face dimension 1) in the certificate's quadratic-form coordinates: `N` are the numerators over `den = 57735991281730516779464839149788173726453690037306728120320000`. The kernel checks the face
identity `Pᵀ A P = d² N` (`d = 10`), so `N` is positive semidefinite with its face block `A`. -/

open scoped Matrix ComplexOrder

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner.X2HBlockPsdH0x014k0

open ThreeCopyQutritWerner.X2HBlockPsdH0x014k0Face

def N : Matrix (Fin 3) (Fin 3) ℤ :=
  ThreeCopyQutritWerner.X2Nh.nh_014k0

def P : Matrix (Fin 1) (Fin 3) ℤ :=
  !![-5, 10, 13]

def PtA : Matrix (Fin 3) (Fin 1) ℤ :=
  !![-240284561167046861310922701189258927544583982678692872368000;
    480569122334093722621845402378517855089167965357385744736000;
    624739859034321839408399023092073211615918354964601468156800]

theorem PtA_eq : Pᵀ * A = PtA := by decide +kernel

theorem face_eq : PtA * P = (10 : ℤ) ^ 2 • N := by decide +kernel

/-- The block numerators are positive semidefinite (exact). -/
theorem psd : (N.map (Int.castRingHom ℂ)).PosSemidef :=
  certificateX2_int_posSemidef_of_face N A P 10 (by norm_num) (by rw [PtA_eq]; exact face_eq) A_psd

/-- The rational block `(1/den) • N` is positive semidefinite (exact). -/
theorem psd_scaled : ((1 / ((57735991281730516779464839149788173726453690037306728120320000 : ℤ) : ℂ)) • N.map (Int.castRingHom ℂ)).PosSemidef :=
  certificateX2_int_div_posSemidef N 57735991281730516779464839149788173726453690037306728120320000 (by norm_num) psd

/-- The rational block `(1/den) • N`, in the bridge's `x2Complex` form (`x2Residual` blocks). -/
theorem psd_rat : (((1 / ((57735991281730516779464839149788173726453690037306728120320000 : ℤ) : ℚ)) • N.map (Int.cast : ℤ → ℚ)).map
    (fun q : ℚ => (q : ℂ))).PosSemidef :=
  certificateX2_rat_int_div_posSemidef N 57735991281730516779464839149788173726453690037306728120320000 (by norm_num) psd

end ThreeCopyQutritWerner.X2HBlockPsdH0x014k0
