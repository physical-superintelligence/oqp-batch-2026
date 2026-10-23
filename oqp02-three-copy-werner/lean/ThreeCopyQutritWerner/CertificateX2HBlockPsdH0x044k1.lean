module

public import ThreeCopyQutritWerner.CertificateX2HBlockPsdH0x044k1Face
public import ThreeCopyQutritWerner.CertificateX2Nh044k1

@[expose] public section


/-! Holomorphic block `044-1` (3 x 3, face dimension 2) in the certificate's quadratic-form coordinates: `N` are the numerators over `den = 57735991281730516779464839149788173726453690037306728120320000`. The kernel checks the face
identity `Pᵀ A P = d² N` (`d = 1`), so `N` is positive semidefinite with its face block `A`. -/

open scoped Matrix ComplexOrder

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner.X2HBlockPsdH0x044k1

open ThreeCopyQutritWerner.X2HBlockPsdH0x044k1Face

def N : Matrix (Fin 3) (Fin 3) ℤ :=
  ThreeCopyQutritWerner.X2Nh.nh_044k1

def P : Matrix (Fin 2) (Fin 3) ℤ :=
  !![-1, 0, 0;
    0, 0, -1]

def PtA : Matrix (Fin 3) (Fin 2) ℤ :=
  !![-402124786012189337693818781091940655553673274490895136691687168, 179690930279995146570190844256554558687994511029397891256860416;
    0, 0;
    179690930279995146570190844256554558687994511029397891256860416, -111488385753517928755861794628466778187725025784187068855900928]

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

end ThreeCopyQutritWerner.X2HBlockPsdH0x044k1
