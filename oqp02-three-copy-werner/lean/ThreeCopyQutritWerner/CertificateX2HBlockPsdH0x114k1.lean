module

public import ThreeCopyQutritWerner.CertificateX2HBlockPsdH0x114k1Face
public import ThreeCopyQutritWerner.CertificateX2Nh114k1

@[expose] public section


/-! Holomorphic block `114-1` (4 x 4, face dimension 2) in the certificate's quadratic-form coordinates: `N` are the numerators over `den = 57735991281730516779464839149788173726453690037306728120320000`. The kernel checks the face
identity `Pᵀ A P = d² N` (`d = 50`), so `N` is positive semidefinite with its face block `A`. -/

open scoped Matrix ComplexOrder

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner.X2HBlockPsdH0x114k1

open ThreeCopyQutritWerner.X2HBlockPsdH0x114k1Face

def N : Matrix (Fin 4) (Fin 4) ℤ :=
  ThreeCopyQutritWerner.X2Nh.nh_114k1

def P : Matrix (Fin 2) (Fin 4) ℤ :=
  !![-50, -100, -20, 40;
    0, -15, -3, -44]

def PtA : Matrix (Fin 4) (Fin 2) ℤ :=
  !![-1152178734979199602389754031579585738165724745816303270659208800, 2264138693151319100862840436571400087008589894839851807952232000;
    -1625115862013003474520655932187751450228872523180650998932748000, -32831013500233235009911270653299585877793624543613707560044280000;
    -325023172402600694904131186437550290045774504636130199786549600, -6566202700046647001982254130659917175558724908722741512008856000;
    2914185037956520490671102809446500667100138904112112207525331200, -111398564221692950034825330160154785821585231293532554229144768000]

theorem PtA_eq : Pᵀ * A = PtA := by decide +kernel

theorem face_eq : PtA * P = (50 : ℤ) ^ 2 • N := by decide +kernel

/-- The block numerators are positive semidefinite (exact). -/
theorem psd : (N.map (Int.castRingHom ℂ)).PosSemidef :=
  certificateX2_int_posSemidef_of_face N A P 50 (by norm_num) (by rw [PtA_eq]; exact face_eq) A_psd

/-- The rational block `(1/den) • N` is positive semidefinite (exact). -/
theorem psd_scaled : ((1 / ((57735991281730516779464839149788173726453690037306728120320000 : ℤ) : ℂ)) • N.map (Int.castRingHom ℂ)).PosSemidef :=
  certificateX2_int_div_posSemidef N 57735991281730516779464839149788173726453690037306728120320000 (by norm_num) psd

/-- The rational block `(1/den) • N`, in the bridge's `x2Complex` form (`x2Residual` blocks). -/
theorem psd_rat : (((1 / ((57735991281730516779464839149788173726453690037306728120320000 : ℤ) : ℚ)) • N.map (Int.cast : ℤ → ℚ)).map
    (fun q : ℚ => (q : ℂ))).PosSemidef :=
  certificateX2_rat_int_div_posSemidef N 57735991281730516779464839149788173726453690037306728120320000 (by norm_num) psd

end ThreeCopyQutritWerner.X2HBlockPsdH0x114k1
