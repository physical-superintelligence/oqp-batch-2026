module

public import ThreeCopyQutritWerner.CertificateX2HBlockPsdH0x055k0Face
public import ThreeCopyQutritWerner.CertificateX2Nh055k0

@[expose] public section


/-! Holomorphic block `055-0` (3 x 3, face dimension 2) in the certificate's quadratic-form coordinates: `N` are the numerators over `den = 57735991281730516779464839149788173726453690037306728120320000`. The kernel checks the face
identity `Pᵀ A P = d² N` (`d = 24`), so `N` is positive semidefinite with its face block `A`. -/

open scoped Matrix ComplexOrder

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner.X2HBlockPsdH0x055k0

open ThreeCopyQutritWerner.X2HBlockPsdH0x055k0Face

def N : Matrix (Fin 3) (Fin 3) ℤ :=
  ThreeCopyQutritWerner.X2Nh.nh_055k0

def P : Matrix (Fin 2) (Fin 3) ℤ :=
  !![14, 4, 0;
    -9, -18, -24]

def PtA : Matrix (Fin 3) (Fin 2) ℤ :=
  !![283473169774302084991975654105217099150677287166479973201039073280, 595663841820602850760349605225095313114269140930896841174016000;
    74440163099447099873275285991834479486752162771115483454107975680, -9000938505797565603151368849014885350235780592616331256168038400;
    -10192266189438771304672068059465075976464318874478124938516070400, -14266199383160925538573395811900975128417556095594691661227622400]

theorem PtA_eq : Pᵀ * A = PtA := by decide +kernel

theorem face_eq : PtA * P = (24 : ℤ) ^ 2 • N := by decide +kernel

/-- The block numerators are positive semidefinite (exact). -/
theorem psd : (N.map (Int.castRingHom ℂ)).PosSemidef :=
  certificateX2_int_posSemidef_of_face N A P 24 (by norm_num) (by rw [PtA_eq]; exact face_eq) A_psd

/-- The rational block `(1/den) • N` is positive semidefinite (exact). -/
theorem psd_scaled : ((1 / ((57735991281730516779464839149788173726453690037306728120320000 : ℤ) : ℂ)) • N.map (Int.castRingHom ℂ)).PosSemidef :=
  certificateX2_int_div_posSemidef N 57735991281730516779464839149788173726453690037306728120320000 (by norm_num) psd

/-- The rational block `(1/den) • N`, in the bridge's `x2Complex` form (`x2Residual` blocks). -/
theorem psd_rat : (((1 / ((57735991281730516779464839149788173726453690037306728120320000 : ℤ) : ℚ)) • N.map (Int.cast : ℤ → ℚ)).map
    (fun q : ℚ => (q : ℂ))).PosSemidef :=
  certificateX2_rat_int_div_posSemidef N 57735991281730516779464839149788173726453690037306728120320000 (by norm_num) psd

end ThreeCopyQutritWerner.X2HBlockPsdH0x055k0
