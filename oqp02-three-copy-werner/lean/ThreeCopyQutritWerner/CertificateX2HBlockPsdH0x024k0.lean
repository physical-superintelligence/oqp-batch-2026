module

public import ThreeCopyQutritWerner.CertificateX2HBlockPsdH0x024k0Face
public import ThreeCopyQutritWerner.CertificateX2Nh024k0

@[expose] public section


/-! Holomorphic block `024-0` (4 x 4, face dimension 1) in the certificate's quadratic-form coordinates: `N` are the numerators over `den = 57735991281730516779464839149788173726453690037306728120320000`. The kernel checks the face
identity `Pᵀ A P = d² N` (`d = 10`), so `N` is positive semidefinite with its face block `A`. -/

open scoped Matrix ComplexOrder

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner.X2HBlockPsdH0x024k0

open ThreeCopyQutritWerner.X2HBlockPsdH0x024k0Face

def N : Matrix (Fin 4) (Fin 4) ℤ :=
  ThreeCopyQutritWerner.X2Nh.nh_024k0

def P : Matrix (Fin 1) (Fin 4) ℤ :=
  !![5, -5, -10, 3]

def PtA : Matrix (Fin 4) (Fin 1) ℤ :=
  !![3275711786919418201181471970852554300216144708629406680224000;
    -3275711786919418201181471970852554300216144708629406680224000;
    -6551423573838836402362943941705108600432289417258813360448000;
    1965427072151650920708883182511532580129686825177644008134400]

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

end ThreeCopyQutritWerner.X2HBlockPsdH0x024k0
