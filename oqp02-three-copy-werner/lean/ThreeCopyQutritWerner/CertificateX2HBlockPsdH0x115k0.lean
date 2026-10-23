module

public import ThreeCopyQutritWerner.CertificateX2HBlockPsdH0x115k0Face
public import ThreeCopyQutritWerner.CertificateX2Nh115k0

@[expose] public section


/-! Holomorphic block `115-0` (5 x 5, face dimension 2) in the certificate's quadratic-form coordinates: `N` are the numerators over `den = 57735991281730516779464839149788173726453690037306728120320000`. The kernel checks the face
identity `Pᵀ A P = d² N` (`d = 12`), so `N` is positive semidefinite with its face block `A`. -/

open scoped Matrix ComplexOrder

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner.X2HBlockPsdH0x115k0

open ThreeCopyQutritWerner.X2HBlockPsdH0x115k0Face

def N : Matrix (Fin 5) (Fin 5) ℤ :=
  ThreeCopyQutritWerner.X2Nh.nh_115k0

def P : Matrix (Fin 2) (Fin 5) ℤ :=
  !![-7, -12, 4, 0, 52;
    1, 0, 2, -12, -1]

def PtA : Matrix (Fin 5) (Fin 2) ℤ :=
  !![-3722646741740159874660682917053267835668946318982254680602438656, 59192911483870704921248925172901916877494120275739169366599459840;
    -7132148973228897236801279385013226573796508398181516315223924736, -5253281911720362161680760690453371988548202959483558039338209280;
    3252929976363026105880553243413304189356869959307765111631009792, 126265745835321953085018991381483891737810544990703675792206233600;
    -5253281911720362161680760690453371988548202959483558039338209280, -747087911188490994186752426907996606449766864025254938674560983040;
    30468205391348524512665480610852867487405852812162940862692156416, -39493104314919346814946072583701771920438359177675826719081175040]

theorem PtA_eq : Pᵀ * A = PtA := by decide +kernel

theorem face_eq : PtA * P = (12 : ℤ) ^ 2 • N := by decide +kernel

/-- The block numerators are positive semidefinite (exact). -/
theorem psd : (N.map (Int.castRingHom ℂ)).PosSemidef :=
  certificateX2_int_posSemidef_of_face N A P 12 (by norm_num) (by rw [PtA_eq]; exact face_eq) A_psd

/-- The rational block `(1/den) • N` is positive semidefinite (exact). -/
theorem psd_scaled : ((1 / ((57735991281730516779464839149788173726453690037306728120320000 : ℤ) : ℂ)) • N.map (Int.castRingHom ℂ)).PosSemidef :=
  certificateX2_int_div_posSemidef N 57735991281730516779464839149788173726453690037306728120320000 (by norm_num) psd

/-- The rational block `(1/den) • N`, in the bridge's `x2Complex` form (`x2Residual` blocks). -/
theorem psd_rat : (((1 / ((57735991281730516779464839149788173726453690037306728120320000 : ℤ) : ℚ)) • N.map (Int.cast : ℤ → ℚ)).map
    (fun q : ℚ => (q : ℂ))).PosSemidef :=
  certificateX2_rat_int_div_posSemidef N 57735991281730516779464839149788173726453690037306728120320000 (by norm_num) psd

end ThreeCopyQutritWerner.X2HBlockPsdH0x115k0
