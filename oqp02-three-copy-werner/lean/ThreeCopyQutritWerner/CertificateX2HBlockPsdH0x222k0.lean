module

public import ThreeCopyQutritWerner.CertificateX2HBlockPsdH0x222k0Face
public import ThreeCopyQutritWerner.CertificateX2Nh222k0

@[expose] public section


/-! Holomorphic block `222-0` (2 x 2, face dimension 1) in the certificate's quadratic-form coordinates: `N` are the numerators over `den = 57735991281730516779464839149788173726453690037306728120320000`. The kernel checks the face
identity `Pᵀ A P = d² N` (`d = 5`), so `N` is positive semidefinite with its face block `A`. -/

open scoped Matrix ComplexOrder

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner.X2HBlockPsdH0x222k0

open ThreeCopyQutritWerner.X2HBlockPsdH0x222k0Face

def N : Matrix (Fin 2) (Fin 2) ℤ :=
  ThreeCopyQutritWerner.X2Nh.nh_222k0

def P : Matrix (Fin 1) (Fin 2) ℤ :=
  !![-3, -2]

def PtA : Matrix (Fin 2) (Fin 1) ℤ :=
  !![-10267667777479083199032207607265683113528683492206370392227840000;
    -6845111851652722132688138404843788742352455661470913594818560000]

theorem PtA_eq : Pᵀ * A = PtA := by decide +kernel

theorem face_eq : PtA * P = (5 : ℤ) ^ 2 • N := by decide +kernel

/-- The block numerators are positive semidefinite (exact). -/
theorem psd : (N.map (Int.castRingHom ℂ)).PosSemidef :=
  certificateX2_int_posSemidef_of_face N A P 5 (by norm_num) (by rw [PtA_eq]; exact face_eq) A_psd

/-- The rational block `(1/den) • N` is positive semidefinite (exact). -/
theorem psd_scaled : ((1 / ((57735991281730516779464839149788173726453690037306728120320000 : ℤ) : ℂ)) • N.map (Int.castRingHom ℂ)).PosSemidef :=
  certificateX2_int_div_posSemidef N 57735991281730516779464839149788173726453690037306728120320000 (by norm_num) psd

/-- The rational block `(1/den) • N`, in the bridge's `x2Complex` form (`x2Residual` blocks). -/
theorem psd_rat : (((1 / ((57735991281730516779464839149788173726453690037306728120320000 : ℤ) : ℚ)) • N.map (Int.cast : ℤ → ℚ)).map
    (fun q : ℚ => (q : ℂ))).PosSemidef :=
  certificateX2_rat_int_div_posSemidef N 57735991281730516779464839149788173726453690037306728120320000 (by norm_num) psd

end ThreeCopyQutritWerner.X2HBlockPsdH0x222k0
