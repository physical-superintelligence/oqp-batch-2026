module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (3, 4, 4) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x344
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k115 : x2Key 1 := ⟨115, by decide⟩
x2_gj_cols gj237 237 1 3 4 4 256
theorem gjc115_0 : (List.range 40).all (fun d => gjCheck 256 1 3 4 4 9 7 7 (x2JCols 237 (0 + d)) (gj237.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok115 : ∀ d < x2KeySize 1 k115, gjCheck 256 1 (x2KeyTypes 1 k115 0) (x2KeyTypes 1 k115 1) (x2KeyTypes 1 k115 2) (x2KeyMult 1 k115 0) (x2KeyMult 1 k115 1) (x2KeyMult 1 k115 2) (x2JCols (x2KeyGlobal 1 k115) d) (gj237.getD d 0) = true := by
  have hr : x2KeySize 1 k115 = 40 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 3 4 4 9 7 7 (x2JCols 237 d) (gj237.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 3 4 4 9 7 7 (x2JCols 237 d) (gj237.getD d 0)) 0 40 gjc115_0 d (Nat.zero_le d) (by omega)
x2_v_cols v237 gj237 237 256 441
theorem vc115_0 : (List.range 14).all (fun c => vCheck 256 441 40 gj237 (x2Trial_237.getD (0 + c) 0) (v237.getD (0 + c) 0)) = true := by decide +kernel
theorem vok115 : ∀ c < 14, vCheck 256 (x2KeyMult 1 k115 0 * x2KeyMult 1 k115 1 * x2KeyMult 1 k115 2) (x2KeySize 1 k115) gj237 (x2Trial_237.getD c 0) (v237.getD c 0) = true := by
  intro c hc
  show vCheck 256 441 40 gj237 (x2Trial_237.getD c 0) (v237.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 441 40 gj237 (x2Trial_237.getD c 0) (v237.getD c 0)) 0 14 vc115_0 c (Nat.zero_le c) (by omega)
theorem small115 : x2KeyDegree 1 k115 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k115 0 ∧ 1 ≤ x2KeyMult 1 k115 1 ∧ 1 ≤ x2KeyMult 1 k115 2 ∧ glRowOK 1 (x2KeyTypes 1 k115 0) (x2KeyMult 1 k115 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k115 1) (x2KeyMult 1 k115 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k115 2) (x2KeyMult 1 k115 2) 512 = true ∧ gj237.length = x2KeySize 1 k115 ∧ x2KeySize 1 k115 ≤ 512 ∧ v237.length = 14 := by decide +kernel
theorem chk115 : trialKeyChk 1 k115 14 gj237 x2Trial_237 v237 :=
  trialKeyChk_intro 1 k115 14 gj237 x2Trial_237 v237 small115 gjok115 vok115
def k116 : x2Key 1 := ⟨116, by decide⟩
x2_gj_cols gj238 238 1 3 4 4 256
theorem gjc116_0 : (List.range 33).all (fun d => gjCheck 256 1 3 4 4 9 7 7 (x2JCols 238 (0 + d)) (gj238.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok116 : ∀ d < x2KeySize 1 k116, gjCheck 256 1 (x2KeyTypes 1 k116 0) (x2KeyTypes 1 k116 1) (x2KeyTypes 1 k116 2) (x2KeyMult 1 k116 0) (x2KeyMult 1 k116 1) (x2KeyMult 1 k116 2) (x2JCols (x2KeyGlobal 1 k116) d) (gj238.getD d 0) = true := by
  have hr : x2KeySize 1 k116 = 33 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 3 4 4 9 7 7 (x2JCols 238 d) (gj238.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 3 4 4 9 7 7 (x2JCols 238 d) (gj238.getD d 0)) 0 33 gjc116_0 d (Nat.zero_le d) (by omega)
x2_v_cols v238 gj238 238 256 441
theorem vc116_0 : (List.range 15).all (fun c => vCheck 256 441 33 gj238 (x2Trial_238.getD (0 + c) 0) (v238.getD (0 + c) 0)) = true := by decide +kernel
theorem vok116 : ∀ c < 15, vCheck 256 (x2KeyMult 1 k116 0 * x2KeyMult 1 k116 1 * x2KeyMult 1 k116 2) (x2KeySize 1 k116) gj238 (x2Trial_238.getD c 0) (v238.getD c 0) = true := by
  intro c hc
  show vCheck 256 441 33 gj238 (x2Trial_238.getD c 0) (v238.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 441 33 gj238 (x2Trial_238.getD c 0) (v238.getD c 0)) 0 15 vc116_0 c (Nat.zero_le c) (by omega)
theorem small116 : x2KeyDegree 1 k116 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k116 0 ∧ 1 ≤ x2KeyMult 1 k116 1 ∧ 1 ≤ x2KeyMult 1 k116 2 ∧ glRowOK 1 (x2KeyTypes 1 k116 0) (x2KeyMult 1 k116 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k116 1) (x2KeyMult 1 k116 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k116 2) (x2KeyMult 1 k116 2) 512 = true ∧ gj238.length = x2KeySize 1 k116 ∧ x2KeySize 1 k116 ≤ 512 ∧ v238.length = 15 := by decide +kernel
theorem chk116 : trialKeyChk 1 k116 15 gj238 x2Trial_238 v238 :=
  trialKeyChk_intro 1 k116 15 gj238 x2Trial_238 v238 small116 gjok116 vok116

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k115, ibFS [(v237, v237, 94810963968000)]), (k116, ibFS [(v238, v238, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![3, 4, 4] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN115 : N k115 = x2TrialForm 1 k115) (hN116 : N k116 = x2TrialForm 1 k116) :
    ∀ e ∈ ks, keyOK (x2Mult 1 3 * x2Mult 1 4 * x2Mult 1 4) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 1 N k115 14 _ gj237 x2Trial_237 v237 (by decide) (by rw [hN115]; exact trialForm_eq 1 k115 14 x2Trial_237 (by decide) rfl) chk115
  · exact keyOK_of_trialChk 1 N k116 15 _ gj238 x2Trial_238 v238 (by decide) (by rw [hN116]; exact trialForm_eq 1 k116 15 x2Trial_238 (by decide) rfl) chk116

end ThreeCopyQutritWerner.X2.InK1x344
