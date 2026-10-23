module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (1, 7, 7) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x177
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k72 : x2Key 1 := ⟨72, by decide⟩
x2_gj_cols gj194 194 1 1 7 7 256
theorem gjc72_0 : (List.range 7).all (fun d => gjCheck 256 1 1 7 7 2 6 6 (x2JCols 194 (0 + d)) (gj194.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok72 : ∀ d < x2KeySize 1 k72, gjCheck 256 1 (x2KeyTypes 1 k72 0) (x2KeyTypes 1 k72 1) (x2KeyTypes 1 k72 2) (x2KeyMult 1 k72 0) (x2KeyMult 1 k72 1) (x2KeyMult 1 k72 2) (x2JCols (x2KeyGlobal 1 k72) d) (gj194.getD d 0) = true := by
  have hr : x2KeySize 1 k72 = 7 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 1 7 7 2 6 6 (x2JCols 194 d) (gj194.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 1 7 7 2 6 6 (x2JCols 194 d) (gj194.getD d 0)) 0 7 gjc72_0 d (Nat.zero_le d) (by omega)
x2_v_cols v194 gj194 194 256 72
theorem vc72_0 : (List.range 2).all (fun c => vCheck 256 72 7 gj194 (x2Trial_194.getD (0 + c) 0) (v194.getD (0 + c) 0)) = true := by decide +kernel
theorem vok72 : ∀ c < 2, vCheck 256 (x2KeyMult 1 k72 0 * x2KeyMult 1 k72 1 * x2KeyMult 1 k72 2) (x2KeySize 1 k72) gj194 (x2Trial_194.getD c 0) (v194.getD c 0) = true := by
  intro c hc
  show vCheck 256 72 7 gj194 (x2Trial_194.getD c 0) (v194.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 72 7 gj194 (x2Trial_194.getD c 0) (v194.getD c 0)) 0 2 vc72_0 c (Nat.zero_le c) (by omega)
theorem small72 : x2KeyDegree 1 k72 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k72 0 ∧ 1 ≤ x2KeyMult 1 k72 1 ∧ 1 ≤ x2KeyMult 1 k72 2 ∧ glRowOK 1 (x2KeyTypes 1 k72 0) (x2KeyMult 1 k72 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k72 1) (x2KeyMult 1 k72 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k72 2) (x2KeyMult 1 k72 2) 512 = true ∧ gj194.length = x2KeySize 1 k72 ∧ x2KeySize 1 k72 ≤ 512 ∧ v194.length = 2 := by decide +kernel
theorem chk72 : trialKeyChk 1 k72 2 gj194 x2Trial_194 v194 :=
  trialKeyChk_intro 1 k72 2 gj194 x2Trial_194 v194 small72 gjok72 vok72
def k73 : x2Key 1 := ⟨73, by decide⟩
x2_gj_cols gj195 195 1 1 7 7 256
theorem gjc73_0 : (List.range 5).all (fun d => gjCheck 256 1 1 7 7 2 6 6 (x2JCols 195 (0 + d)) (gj195.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok73 : ∀ d < x2KeySize 1 k73, gjCheck 256 1 (x2KeyTypes 1 k73 0) (x2KeyTypes 1 k73 1) (x2KeyTypes 1 k73 2) (x2KeyMult 1 k73 0) (x2KeyMult 1 k73 1) (x2KeyMult 1 k73 2) (x2JCols (x2KeyGlobal 1 k73) d) (gj195.getD d 0) = true := by
  have hr : x2KeySize 1 k73 = 5 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 1 7 7 2 6 6 (x2JCols 195 d) (gj195.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 1 7 7 2 6 6 (x2JCols 195 d) (gj195.getD d 0)) 0 5 gjc73_0 d (Nat.zero_le d) (by omega)
x2_v_cols v195 gj195 195 256 72
theorem vc73_0 : (List.range 2).all (fun c => vCheck 256 72 5 gj195 (x2Trial_195.getD (0 + c) 0) (v195.getD (0 + c) 0)) = true := by decide +kernel
theorem vok73 : ∀ c < 2, vCheck 256 (x2KeyMult 1 k73 0 * x2KeyMult 1 k73 1 * x2KeyMult 1 k73 2) (x2KeySize 1 k73) gj195 (x2Trial_195.getD c 0) (v195.getD c 0) = true := by
  intro c hc
  show vCheck 256 72 5 gj195 (x2Trial_195.getD c 0) (v195.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 72 5 gj195 (x2Trial_195.getD c 0) (v195.getD c 0)) 0 2 vc73_0 c (Nat.zero_le c) (by omega)
theorem small73 : x2KeyDegree 1 k73 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k73 0 ∧ 1 ≤ x2KeyMult 1 k73 1 ∧ 1 ≤ x2KeyMult 1 k73 2 ∧ glRowOK 1 (x2KeyTypes 1 k73 0) (x2KeyMult 1 k73 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k73 1) (x2KeyMult 1 k73 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k73 2) (x2KeyMult 1 k73 2) 512 = true ∧ gj195.length = x2KeySize 1 k73 ∧ x2KeySize 1 k73 ≤ 512 ∧ v195.length = 2 := by decide +kernel
theorem chk73 : trialKeyChk 1 k73 2 gj195 x2Trial_195 v195 :=
  trialKeyChk_intro 1 k73 2 gj195 x2Trial_195 v195 small73 gjok73 vok73

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k72, ibFS [(v194, v194, 94810963968000)]), (k73, ibFS [(v195, v195, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![1, 7, 7] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN72 : N k72 = x2TrialForm 1 k72) (hN73 : N k73 = x2TrialForm 1 k73) :
    ∀ e ∈ ks, keyOK (x2Mult 1 1 * x2Mult 1 7 * x2Mult 1 7) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 1 N k72 2 _ gj194 x2Trial_194 v194 (by decide) (by rw [hN72]; exact trialForm_eq 1 k72 2 x2Trial_194 (by decide) rfl) chk72
  · exact keyOK_of_trialChk 1 N k73 2 _ gj195 x2Trial_195 v195 (by decide) (by rw [hN73]; exact trialForm_eq 1 k73 2 x2Trial_195 (by decide) rfl) chk73

end ThreeCopyQutritWerner.X2.InK1x177
