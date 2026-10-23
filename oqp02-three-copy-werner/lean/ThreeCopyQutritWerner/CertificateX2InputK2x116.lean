module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (1, 1, 6) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x116
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k38 : x2Key 2 := ⟨38, by decide⟩
x2_gj_cols gj329 329 2 1 1 6 256
theorem gjc38_0 : (List.range 9).all (fun d => gjCheck 256 2 1 1 6 4 4 11 (x2JCols 329 (0 + d)) (gj329.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok38 : ∀ d < x2KeySize 2 k38, gjCheck 256 2 (x2KeyTypes 2 k38 0) (x2KeyTypes 2 k38 1) (x2KeyTypes 2 k38 2) (x2KeyMult 2 k38 0) (x2KeyMult 2 k38 1) (x2KeyMult 2 k38 2) (x2JCols (x2KeyGlobal 2 k38) d) (gj329.getD d 0) = true := by
  have hr : x2KeySize 2 k38 = 9 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 1 1 6 4 4 11 (x2JCols 329 d) (gj329.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 1 1 6 4 4 11 (x2JCols 329 d) (gj329.getD d 0)) 0 9 gjc38_0 d (Nat.zero_le d) (by omega)
x2_v_cols v329 gj329 329 256 176
theorem vc38_0 : (List.range 9).all (fun c => vCheck 256 176 9 gj329 (x2Trial_329.getD (0 + c) 0) (v329.getD (0 + c) 0)) = true := by decide +kernel
theorem vok38 : ∀ c < 9, vCheck 256 (x2KeyMult 2 k38 0 * x2KeyMult 2 k38 1 * x2KeyMult 2 k38 2) (x2KeySize 2 k38) gj329 (x2Trial_329.getD c 0) (v329.getD c 0) = true := by
  intro c hc
  show vCheck 256 176 9 gj329 (x2Trial_329.getD c 0) (v329.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 176 9 gj329 (x2Trial_329.getD c 0) (v329.getD c 0)) 0 9 vc38_0 c (Nat.zero_le c) (by omega)
theorem small38 : x2KeyDegree 2 k38 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k38 0 ∧ 1 ≤ x2KeyMult 2 k38 1 ∧ 1 ≤ x2KeyMult 2 k38 2 ∧ glRowOK 2 (x2KeyTypes 2 k38 0) (x2KeyMult 2 k38 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k38 1) (x2KeyMult 2 k38 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k38 2) (x2KeyMult 2 k38 2) 512 = true ∧ gj329.length = x2KeySize 2 k38 ∧ x2KeySize 2 k38 ≤ 512 ∧ v329.length = 9 := by decide +kernel
theorem chk38 : trialKeyChk 2 k38 9 gj329 x2Trial_329 v329 :=
  trialKeyChk_intro 2 k38 9 gj329 x2Trial_329 v329 small38 gjok38 vok38
def k39 : x2Key 2 := ⟨39, by decide⟩
x2_gj_cols gj330 330 2 1 1 6 256
theorem gjc39_0 : (List.range 6).all (fun d => gjCheck 256 2 1 1 6 4 4 11 (x2JCols 330 (0 + d)) (gj330.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok39 : ∀ d < x2KeySize 2 k39, gjCheck 256 2 (x2KeyTypes 2 k39 0) (x2KeyTypes 2 k39 1) (x2KeyTypes 2 k39 2) (x2KeyMult 2 k39 0) (x2KeyMult 2 k39 1) (x2KeyMult 2 k39 2) (x2JCols (x2KeyGlobal 2 k39) d) (gj330.getD d 0) = true := by
  have hr : x2KeySize 2 k39 = 6 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 1 1 6 4 4 11 (x2JCols 330 d) (gj330.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 1 1 6 4 4 11 (x2JCols 330 d) (gj330.getD d 0)) 0 6 gjc39_0 d (Nat.zero_le d) (by omega)
x2_v_cols v330 gj330 330 256 176
theorem vc39_0 : (List.range 6).all (fun c => vCheck 256 176 6 gj330 (x2Trial_330.getD (0 + c) 0) (v330.getD (0 + c) 0)) = true := by decide +kernel
theorem vok39 : ∀ c < 6, vCheck 256 (x2KeyMult 2 k39 0 * x2KeyMult 2 k39 1 * x2KeyMult 2 k39 2) (x2KeySize 2 k39) gj330 (x2Trial_330.getD c 0) (v330.getD c 0) = true := by
  intro c hc
  show vCheck 256 176 6 gj330 (x2Trial_330.getD c 0) (v330.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 176 6 gj330 (x2Trial_330.getD c 0) (v330.getD c 0)) 0 6 vc39_0 c (Nat.zero_le c) (by omega)
theorem small39 : x2KeyDegree 2 k39 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k39 0 ∧ 1 ≤ x2KeyMult 2 k39 1 ∧ 1 ≤ x2KeyMult 2 k39 2 ∧ glRowOK 2 (x2KeyTypes 2 k39 0) (x2KeyMult 2 k39 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k39 1) (x2KeyMult 2 k39 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k39 2) (x2KeyMult 2 k39 2) 512 = true ∧ gj330.length = x2KeySize 2 k39 ∧ x2KeySize 2 k39 ≤ 512 ∧ v330.length = 6 := by decide +kernel
theorem chk39 : trialKeyChk 2 k39 6 gj330 x2Trial_330 v330 :=
  trialKeyChk_intro 2 k39 6 gj330 x2Trial_330 v330 small39 gjok39 vok39

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k38, ibFS [(v329, v329, 94810963968000)]), (k39, ibFS [(v330, v330, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![1, 1, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN38 : N k38 = x2TrialForm 2 k38) (hN39 : N k39 = x2TrialForm 2 k39) :
    ∀ e ∈ ks, keyOK (x2Mult 2 1 * x2Mult 2 1 * x2Mult 2 6) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 2 N k38 9 _ gj329 x2Trial_329 v329 (by decide) (by rw [hN38]; exact trialForm_eq 2 k38 9 x2Trial_329 (by decide) rfl) chk38
  · exact keyOK_of_trialChk 2 N k39 6 _ gj330 x2Trial_330 v330 (by decide) (by rw [hN39]; exact trialForm_eq 2 k39 6 x2Trial_330 (by decide) rfl) chk39

end ThreeCopyQutritWerner.X2.InK2x116
