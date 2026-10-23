module

public import ThreeCopyQutritWerner.CertificateX2HBlockPsdH0x036k0Face
public import ThreeCopyQutritWerner.CertificateX2Nh036k0

@[expose] public section


/-! Holomorphic block `036-0` (2 x 2, face dimension 2) in the certificate's quadratic-form coordinates: `N` are the numerators over `den = 57735991281730516779464839149788173726453690037306728120320000`. The kernel checks the face
identity `Pᵀ A P = d² N` (`d = 1`), so `N` is positive semidefinite with its face block `A`. -/

open scoped Matrix ComplexOrder

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner.X2HBlockPsdH0x036k0

open ThreeCopyQutritWerner.X2HBlockPsdH0x036k0Face

def N : Matrix (Fin 2) (Fin 2) ℤ :=
  ThreeCopyQutritWerner.X2Nh.nh_036k0

def P : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 0;
    0, 1]

def PtA : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1021879131590134024364577660347250641972259274993792170771861504, -387366873613174526595121358403608530606233245756298314237540352;
    -387366873613174526595121358403608530606233245756298314237540352, 413354801652207555653035542131161805373298744752535438185970944]

theorem PtA_eq : Pᵀ * A = PtA := by decide +kernel

theorem face_eq : PtA * P = (1 : ℤ) ^ 2 • N := by decide +kernel

/-- The block numerators are positive semidefinite (exact). -/
theorem psd : (N.map (Int.castRingHom ℂ)).PosSemidef :=
  certificateX2_int_posSemidef_of_face N A P 1 (by norm_num) (by rw [PtA_eq]; exact face_eq) A_psd

/-- The rational block `(1/den) • N` is positive semidefinite (exact). -/
theorem psd_scaled : ((1 / ((57735991281730516779464839149788173726453690037306728120320000 : ℤ) : ℂ)) • N.map (Int.castRingHom ℂ)).PosSemidef :=
  certificateX2_int_div_posSemidef N 57735991281730516779464839149788173726453690037306728120320000 (by norm_num) psd

/-- The rational block `(1/den) • N`, in the bridge's `x2Complex` form (`x2Residual` blocks). -/
theorem psd_rat : (((1 / ((57735991281730516779464839149788173726453690037306728120320000 : ℤ) : ℚ)) • N.map (Int.cast : ℤ → ℚ)).map
    (fun q : ℚ => (q : ℂ))).PosSemidef :=
  certificateX2_rat_int_div_posSemidef N 57735991281730516779464839149788173726453690037306728120320000 (by norm_num) psd

end ThreeCopyQutritWerner.X2HBlockPsdH0x036k0
