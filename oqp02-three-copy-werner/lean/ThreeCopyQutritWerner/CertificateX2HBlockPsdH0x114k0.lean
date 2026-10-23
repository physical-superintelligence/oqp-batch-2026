module

public import ThreeCopyQutritWerner.CertificateX2HBlockPsdH0x114k0Face
public import ThreeCopyQutritWerner.CertificateX2Nh114k0

@[expose] public section


/-! Holomorphic block `114-0` (7 x 7, face dimension 2) in the certificate's quadratic-form coordinates: `N` are the numerators over `den = 57735991281730516779464839149788173726453690037306728120320000`. The kernel checks the face
identity `Pᵀ A P = d² N` (`d = 20`), so `N` is positive semidefinite with its face block `A`. -/

open scoped Matrix ComplexOrder

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner.X2HBlockPsdH0x114k0

open ThreeCopyQutritWerner.X2HBlockPsdH0x114k0Face

def N : Matrix (Fin 7) (Fin 7) ℤ :=
  ThreeCopyQutritWerner.X2Nh.nh_114k0

def P : Matrix (Fin 2) (Fin 7) ℤ :=
  !![-5, -5, 0, -18, 10, -18, -18;
    0, -5, 5, -11, 5, -21, -1]

def PtA : Matrix (Fin 7) (Fin 2) ℤ :=
  !![-315324448403023504010950219518543651924788745093438280749818880, 62211602440814461352083970086980656056279611617465533846448640;
    -253112845962209042658866249431562995868509133475972746903370240, -429538135856859873888252590961081696839453002160047174891553280;
    -62211602440814461352083970086980656056279611617465533846448640, 491749738297674335240336561048062352895732613777512708738001920;
    -998302488881092799464836056075399703605424336777953636237160960, -857887655467951476661238141992606814568005148487652037376389120;
    568437294365232546669816468950106647793297878569411027653189120, 367326533416045412536168620874101040783173390542581641045104640;
    -873879283999463876760668115901438391492865113543022568544263680, -1841387132063300147141911264088731520359470376042677454852392960;
    -1122725693762721722169003996249361015717983560012884703930058240, 125611821127397193819434980103517891223460079067373380099614720]

theorem PtA_eq : Pᵀ * A = PtA := by decide +kernel

theorem face_eq : PtA * P = (20 : ℤ) ^ 2 • N := by decide +kernel

/-- The block numerators are positive semidefinite (exact). -/
theorem psd : (N.map (Int.castRingHom ℂ)).PosSemidef :=
  certificateX2_int_posSemidef_of_face N A P 20 (by norm_num) (by rw [PtA_eq]; exact face_eq) A_psd

/-- The rational block `(1/den) • N` is positive semidefinite (exact). -/
theorem psd_scaled : ((1 / ((57735991281730516779464839149788173726453690037306728120320000 : ℤ) : ℂ)) • N.map (Int.castRingHom ℂ)).PosSemidef :=
  certificateX2_int_div_posSemidef N 57735991281730516779464839149788173726453690037306728120320000 (by norm_num) psd

/-- The rational block `(1/den) • N`, in the bridge's `x2Complex` form (`x2Residual` blocks). -/
theorem psd_rat : (((1 / ((57735991281730516779464839149788173726453690037306728120320000 : ℤ) : ℚ)) • N.map (Int.cast : ℤ → ℚ)).map
    (fun q : ℚ => (q : ℂ))).PosSemidef :=
  certificateX2_rat_int_div_posSemidef N 57735991281730516779464839149788173726453690037306728120320000 (by norm_num) psd

end ThreeCopyQutritWerner.X2HBlockPsdH0x114k0
