module

public import ThreeCopyQutritWerner.CertificateX2HBlockPsdH0x335k1Face
public import ThreeCopyQutritWerner.CertificateX2Nh335k1

@[expose] public section


/-! Holomorphic block `335-1` (4 x 4, face dimension 2) in the certificate's quadratic-form coordinates: `N` are the numerators over `den = 57735991281730516779464839149788173726453690037306728120320000`. The kernel checks the face
identity `Pᵀ A P = d² N` (`d = 4`), so `N` is positive semidefinite with its face block `A`. -/

open scoped Matrix ComplexOrder

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner.X2HBlockPsdH0x335k1

open ThreeCopyQutritWerner.X2HBlockPsdH0x335k1Face

def N : Matrix (Fin 4) (Fin 4) ℤ :=
  ThreeCopyQutritWerner.X2Nh.nh_335k1

def P : Matrix (Fin 2) (Fin 4) ℤ :=
  !![-3, 4, 0, -2;
    -3, 0, 4, -4]

def PtA : Matrix (Fin 4) (Fin 2) ℤ :=
  !![-2027729550087604260463156484726620275739344835155728336636709120, -10603765146305592577782197056148534279950762138093510810847512320;
    948479032319553784266738616787850871339517963508519441235501056, 1755160367797251896350803362847642829646275150032451674280111104;
    1755160367797251896350803362847642829646275150032451674280111104, 12383193160610204874025459378683736210288074367425562740183238656;
    -2229399883957028788484172671241568265316034131786711394897861632, -13260773344508830822200861060107557625111211942441788577323294208]

theorem PtA_eq : Pᵀ * A = PtA := by decide +kernel

theorem face_eq : PtA * P = (4 : ℤ) ^ 2 • N := by decide +kernel

/-- The block numerators are positive semidefinite (exact). -/
theorem psd : (N.map (Int.castRingHom ℂ)).PosSemidef :=
  certificateX2_int_posSemidef_of_face N A P 4 (by norm_num) (by rw [PtA_eq]; exact face_eq) A_psd

/-- The rational block `(1/den) • N` is positive semidefinite (exact). -/
theorem psd_scaled : ((1 / ((57735991281730516779464839149788173726453690037306728120320000 : ℤ) : ℂ)) • N.map (Int.castRingHom ℂ)).PosSemidef :=
  certificateX2_int_div_posSemidef N 57735991281730516779464839149788173726453690037306728120320000 (by norm_num) psd

/-- The rational block `(1/den) • N`, in the bridge's `x2Complex` form (`x2Residual` blocks). -/
theorem psd_rat : (((1 / ((57735991281730516779464839149788173726453690037306728120320000 : ℤ) : ℚ)) • N.map (Int.cast : ℤ → ℚ)).map
    (fun q : ℚ => (q : ℂ))).PosSemidef :=
  certificateX2_rat_int_div_posSemidef N 57735991281730516779464839149788173726453690037306728120320000 (by norm_num) psd

end ThreeCopyQutritWerner.X2HBlockPsdH0x335k1
