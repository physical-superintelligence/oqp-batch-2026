module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (3, 3, 4) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x334
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k107 : x2Key 1 := ⟨107, by decide⟩
x2_gj_cols gj229 229 1 3 3 4 256
theorem gjc107_0 : (List.range 54).all (fun d => gjCheck 256 1 3 3 4 9 9 7 (x2JCols 229 (0 + d)) (gj229.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok107 : ∀ d < x2KeySize 1 k107, gjCheck 256 1 (x2KeyTypes 1 k107 0) (x2KeyTypes 1 k107 1) (x2KeyTypes 1 k107 2) (x2KeyMult 1 k107 0) (x2KeyMult 1 k107 1) (x2KeyMult 1 k107 2) (x2JCols (x2KeyGlobal 1 k107) d) (gj229.getD d 0) = true := by
  have hr : x2KeySize 1 k107 = 54 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 3 3 4 9 9 7 (x2JCols 229 d) (gj229.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 3 3 4 9 9 7 (x2JCols 229 d) (gj229.getD d 0)) 0 54 gjc107_0 d (Nat.zero_le d) (by omega)
x2_v_cols v229 gj229 229 256 567
theorem vc107_0 : (List.range 19).all (fun c => vCheck 256 567 54 gj229 (x2Trial_229.getD (0 + c) 0) (v229.getD (0 + c) 0)) = true := by decide +kernel
theorem vok107 : ∀ c < 19, vCheck 256 (x2KeyMult 1 k107 0 * x2KeyMult 1 k107 1 * x2KeyMult 1 k107 2) (x2KeySize 1 k107) gj229 (x2Trial_229.getD c 0) (v229.getD c 0) = true := by
  intro c hc
  show vCheck 256 567 54 gj229 (x2Trial_229.getD c 0) (v229.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 567 54 gj229 (x2Trial_229.getD c 0) (v229.getD c 0)) 0 19 vc107_0 c (Nat.zero_le c) (by omega)
theorem small107 : x2KeyDegree 1 k107 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k107 0 ∧ 1 ≤ x2KeyMult 1 k107 1 ∧ 1 ≤ x2KeyMult 1 k107 2 ∧ glRowOK 1 (x2KeyTypes 1 k107 0) (x2KeyMult 1 k107 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k107 1) (x2KeyMult 1 k107 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k107 2) (x2KeyMult 1 k107 2) 512 = true ∧ gj229.length = x2KeySize 1 k107 ∧ x2KeySize 1 k107 ≤ 512 ∧ v229.length = 19 := by decide +kernel
theorem chk107 : trialKeyChk 1 k107 19 gj229 x2Trial_229 v229 :=
  trialKeyChk_intro 1 k107 19 gj229 x2Trial_229 v229 small107 gjok107 vok107
def k108 : x2Key 1 := ⟨108, by decide⟩
x2_gj_cols gj230 230 1 3 3 4 256
theorem gjc108_0 : (List.range 42).all (fun d => gjCheck 256 1 3 3 4 9 9 7 (x2JCols 230 (0 + d)) (gj230.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok108 : ∀ d < x2KeySize 1 k108, gjCheck 256 1 (x2KeyTypes 1 k108 0) (x2KeyTypes 1 k108 1) (x2KeyTypes 1 k108 2) (x2KeyMult 1 k108 0) (x2KeyMult 1 k108 1) (x2KeyMult 1 k108 2) (x2JCols (x2KeyGlobal 1 k108) d) (gj230.getD d 0) = true := by
  have hr : x2KeySize 1 k108 = 42 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 3 3 4 9 9 7 (x2JCols 230 d) (gj230.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 3 3 4 9 9 7 (x2JCols 230 d) (gj230.getD d 0)) 0 42 gjc108_0 d (Nat.zero_le d) (by omega)
x2_v_cols v230 gj230 230 256 567
theorem vc108_0 : (List.range 10).all (fun c => vCheck 256 567 42 gj230 (x2Trial_230.getD (0 + c) 0) (v230.getD (0 + c) 0)) = true := by decide +kernel
theorem vok108 : ∀ c < 10, vCheck 256 (x2KeyMult 1 k108 0 * x2KeyMult 1 k108 1 * x2KeyMult 1 k108 2) (x2KeySize 1 k108) gj230 (x2Trial_230.getD c 0) (v230.getD c 0) = true := by
  intro c hc
  show vCheck 256 567 42 gj230 (x2Trial_230.getD c 0) (v230.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 567 42 gj230 (x2Trial_230.getD c 0) (v230.getD c 0)) 0 10 vc108_0 c (Nat.zero_le c) (by omega)
theorem small108 : x2KeyDegree 1 k108 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k108 0 ∧ 1 ≤ x2KeyMult 1 k108 1 ∧ 1 ≤ x2KeyMult 1 k108 2 ∧ glRowOK 1 (x2KeyTypes 1 k108 0) (x2KeyMult 1 k108 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k108 1) (x2KeyMult 1 k108 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k108 2) (x2KeyMult 1 k108 2) 512 = true ∧ gj230.length = x2KeySize 1 k108 ∧ x2KeySize 1 k108 ≤ 512 ∧ v230.length = 10 := by decide +kernel
theorem chk108 : trialKeyChk 1 k108 10 gj230 x2Trial_230 v230 :=
  trialKeyChk_intro 1 k108 10 gj230 x2Trial_230 v230 small108 gjok108 vok108

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k107, ibFS [(v229, v229, 94810963968000)]), (k108, ibFS [(v230, v230, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![3, 3, 4] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN107 : N k107 = x2TrialForm 1 k107) (hN108 : N k108 = x2TrialForm 1 k108) :
    ∀ e ∈ ks, keyOK (x2Mult 1 3 * x2Mult 1 3 * x2Mult 1 4) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 1 N k107 19 _ gj229 x2Trial_229 v229 (by decide) (by rw [hN107]; exact trialForm_eq 1 k107 19 x2Trial_229 (by decide) rfl) chk107
  · exact keyOK_of_trialChk 1 N k108 10 _ gj230 x2Trial_230 v230 (by decide) (by rw [hN108]; exact trialForm_eq 1 k108 10 x2Trial_230 (by decide) rfl) chk108

end ThreeCopyQutritWerner.X2.InK1x334
