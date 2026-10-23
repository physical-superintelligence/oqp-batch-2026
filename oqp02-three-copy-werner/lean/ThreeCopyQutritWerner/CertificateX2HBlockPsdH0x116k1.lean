module

public import ThreeCopyQutritWerner.CertificateX2HBlockPsdH0x116k1Face
public import ThreeCopyQutritWerner.CertificateX2Nh116k1

@[expose] public section


/-! Holomorphic block `116-1` (3 x 3, face dimension 3) in the certificate's quadratic-form coordinates: `N` are the numerators over `den = 57735991281730516779464839149788173726453690037306728120320000`. The kernel checks the face
identity `Pᵀ A P = d² N` (`d = 1`), so `N` is positive semidefinite with its face block `A`. -/

open scoped Matrix ComplexOrder

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner.X2HBlockPsdH0x116k1

open ThreeCopyQutritWerner.X2HBlockPsdH0x116k1Face

def N : Matrix (Fin 3) (Fin 3) ℤ :=
  ThreeCopyQutritWerner.X2Nh.nh_116k1

def P : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
    0, 1, 0;
    0, 0, 1]

def PtA : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1106795556845639506982602717542826359835675007017795025155307520, 1543624358691050518706186904172667812393400768744987987226040320, 1504583276323902653227714911064307341129836668761971637712440320;
    1543624358691050518706186904172667812393400768744987987226040320, 11346053240387195856535088641042467589067189459049337550927192064, 2774367775193133918047770937119512798882924038785769362339094016;
    1504583276323902653227714911064307341129836668761971637712440320, 2774367775193133918047770937119512798882924038785769362339094016, 2096729699241419521437330413514803048506754395648953016319366784]

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

end ThreeCopyQutritWerner.X2HBlockPsdH0x116k1
