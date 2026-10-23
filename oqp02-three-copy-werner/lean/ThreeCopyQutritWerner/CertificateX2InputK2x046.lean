module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (0, 4, 6) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x046
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k22 : x2Key 2 := ⟨22, by decide⟩
x2_gj_cols gj313 313 2 0 4 6 256
theorem gjc22_0 : (List.range 14).all (fun d => gjCheck 256 2 0 4 6 1 15 11 (x2JCols 313 (0 + d)) (gj313.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok22 : ∀ d < x2KeySize 2 k22, gjCheck 256 2 (x2KeyTypes 2 k22 0) (x2KeyTypes 2 k22 1) (x2KeyTypes 2 k22 2) (x2KeyMult 2 k22 0) (x2KeyMult 2 k22 1) (x2KeyMult 2 k22 2) (x2JCols (x2KeyGlobal 2 k22) d) (gj313.getD d 0) = true := by
  have hr : x2KeySize 2 k22 = 14 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 0 4 6 1 15 11 (x2JCols 313 d) (gj313.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 0 4 6 1 15 11 (x2JCols 313 d) (gj313.getD d 0)) 0 14 gjc22_0 d (Nat.zero_le d) (by omega)
x2_v_cols v313 gj313 313 256 165
theorem vc22_0 : (List.range 14).all (fun c => vCheck 256 165 14 gj313 (x2Trial_313.getD (0 + c) 0) (v313.getD (0 + c) 0)) = true := by decide +kernel
theorem vok22 : ∀ c < 14, vCheck 256 (x2KeyMult 2 k22 0 * x2KeyMult 2 k22 1 * x2KeyMult 2 k22 2) (x2KeySize 2 k22) gj313 (x2Trial_313.getD c 0) (v313.getD c 0) = true := by
  intro c hc
  show vCheck 256 165 14 gj313 (x2Trial_313.getD c 0) (v313.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 165 14 gj313 (x2Trial_313.getD c 0) (v313.getD c 0)) 0 14 vc22_0 c (Nat.zero_le c) (by omega)
theorem small22 : x2KeyDegree 2 k22 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k22 0 ∧ 1 ≤ x2KeyMult 2 k22 1 ∧ 1 ≤ x2KeyMult 2 k22 2 ∧ glRowOK 2 (x2KeyTypes 2 k22 0) (x2KeyMult 2 k22 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k22 1) (x2KeyMult 2 k22 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k22 2) (x2KeyMult 2 k22 2) 512 = true ∧ gj313.length = x2KeySize 2 k22 ∧ x2KeySize 2 k22 ≤ 512 ∧ v313.length = 14 := by decide +kernel
theorem chk22 : trialKeyChk 2 k22 14 gj313 x2Trial_313 v313 :=
  trialKeyChk_intro 2 k22 14 gj313 x2Trial_313 v313 small22 gjok22 vok22

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k22, ibFS [(v313, v313, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![0, 4, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN22 : N k22 = x2TrialForm 2 k22) :
    ∀ e ∈ ks, keyOK (x2Mult 2 0 * x2Mult 2 4 * x2Mult 2 6) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 2 N k22 14 _ gj313 x2Trial_313 v313 (by decide) (by rw [hN22]; exact trialForm_eq 2 k22 14 x2Trial_313 (by decide) rfl) chk22

end ThreeCopyQutritWerner.X2.InK2x046
