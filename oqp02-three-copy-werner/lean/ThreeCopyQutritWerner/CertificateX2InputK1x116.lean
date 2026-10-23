module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (1, 1, 6) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x116
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k44 : x2Key 1 := ⟨44, by decide⟩
x2_gj_cols gj166 166 1 1 1 6 256
theorem gjc44_0 : (List.range 9).all (fun d => gjCheck 256 1 1 1 6 2 2 17 (x2JCols 166 (0 + d)) (gj166.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok44 : ∀ d < x2KeySize 1 k44, gjCheck 256 1 (x2KeyTypes 1 k44 0) (x2KeyTypes 1 k44 1) (x2KeyTypes 1 k44 2) (x2KeyMult 1 k44 0) (x2KeyMult 1 k44 1) (x2KeyMult 1 k44 2) (x2JCols (x2KeyGlobal 1 k44) d) (gj166.getD d 0) = true := by
  have hr : x2KeySize 1 k44 = 9 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 1 1 6 2 2 17 (x2JCols 166 d) (gj166.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 1 1 6 2 2 17 (x2JCols 166 d) (gj166.getD d 0)) 0 9 gjc44_0 d (Nat.zero_le d) (by omega)
x2_nat_list K1x116k0c "verification/matrix-literals/x2-transfer/corr-light/K1x116k0.hex"
x2_nat_list A1x116k0c "verification/matrix-literals/x2-transfer/corr-light/A1x116k0.hex"
x2_vk_cols u166 gj166 K1x116k0c 256 68
x2_ua_cols ua166 u166 A1x116k0c 68 2
theorem cchk44 : corrKeyChk 1 k44 2 gj166 K1x116k0c u166 A1x116k0c ua166 := by
  have h1 : x2KeyDegree 1 k44 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k44 0 ∧ 1 ≤ x2KeyMult 1 k44 1 ∧ 1 ≤ x2KeyMult 1 k44 2 ∧ glRowOK 1 (x2KeyTypes 1 k44 0) (x2KeyMult 1 k44 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k44 1) (x2KeyMult 1 k44 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k44 2) (x2KeyMult 1 k44 2) 512 = true ∧ gj166.length = x2KeySize 1 k44 ∧ x2KeySize 1 k44 ≤ 512 := by decide +kernel
  have h2 : ∀ c < 2, vCheck 256 (x2KeyMult 1 k44 0 * x2KeyMult 1 k44 1 * x2KeyMult 1 k44 2) (x2KeySize 1 k44) gj166 (K1x116k0c.getD c 0) (u166.getD c 0) = true ∧ slotBoundCheck 256 18 (x2KeyMult 1 k44 0 * x2KeyMult 1 k44 1 * x2KeyMult 1 k44 2) (u166.getD c 0) = true := by decide +kernel
  have h3 : u166.length = 2 ∧ ua166.length = 2 ∧ 2 ≤ 512 := by decide +kernel
  have h4 : ∀ c < 2, uaCheck (x2KeyMult 1 k44 0 * x2KeyMult 1 k44 1 * x2KeyMult 1 k44 2) 2 u166 (A1x116k0c.getD c 0) (ua166.getD c 0) = true := by decide +kernel
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h1
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, gjok44, h2, h3.1, h3.2.1, h3.2.2, h4⟩
def k45 : x2Key 1 := ⟨45, by decide⟩

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k44, ibFS [(ua166, u166, 3)]), (k45, [])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![1, 1, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN44 : N k44 = x2CorrForm 1 k44 2 K1x116k0c A1x116k0c) (hN45 : N k45 = x2TrialForm 1 k45) :
    ∀ e ∈ ks, keyOK (x2Mult 1 1 * x2Mult 1 1 * x2Mult 1 6) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_corrChk 1 N k44 2 _ gj166 K1x116k0c u166 A1x116k0c ua166 (by decide) hN44 cchk44
  · exact keyOK_of_zeroBlock _ 1 N k45 (by rw [hN45]; exact trialForm_zero 1 k45 (by decide))

end ThreeCopyQutritWerner.X2.InK1x116
