module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (0, 4, 4) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x044
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k19 : x2Key 2 := ⟨19, by decide⟩
x2_gj_cols gj310 310 2 0 4 4 256
theorem gjc19_0 : (List.range 12).all (fun d => gjCheck 256 2 0 4 4 1 15 15 (x2JCols 310 (0 + d)) (gj310.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok19 : ∀ d < x2KeySize 2 k19, gjCheck 256 2 (x2KeyTypes 2 k19 0) (x2KeyTypes 2 k19 1) (x2KeyTypes 2 k19 2) (x2KeyMult 2 k19 0) (x2KeyMult 2 k19 1) (x2KeyMult 2 k19 2) (x2JCols (x2KeyGlobal 2 k19) d) (gj310.getD d 0) = true := by
  have hr : x2KeySize 2 k19 = 12 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 0 4 4 1 15 15 (x2JCols 310 d) (gj310.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 0 4 4 1 15 15 (x2JCols 310 d) (gj310.getD d 0)) 0 12 gjc19_0 d (Nat.zero_le d) (by omega)
x2_v_cols v310 gj310 310 256 225
theorem vc19_0 : (List.range 7).all (fun c => vCheck 256 225 12 gj310 (x2Trial_310.getD (0 + c) 0) (v310.getD (0 + c) 0)) = true := by decide +kernel
theorem vok19 : ∀ c < 7, vCheck 256 (x2KeyMult 2 k19 0 * x2KeyMult 2 k19 1 * x2KeyMult 2 k19 2) (x2KeySize 2 k19) gj310 (x2Trial_310.getD c 0) (v310.getD c 0) = true := by
  intro c hc
  show vCheck 256 225 12 gj310 (x2Trial_310.getD c 0) (v310.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 225 12 gj310 (x2Trial_310.getD c 0) (v310.getD c 0)) 0 7 vc19_0 c (Nat.zero_le c) (by omega)
theorem small19 : x2KeyDegree 2 k19 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k19 0 ∧ 1 ≤ x2KeyMult 2 k19 1 ∧ 1 ≤ x2KeyMult 2 k19 2 ∧ glRowOK 2 (x2KeyTypes 2 k19 0) (x2KeyMult 2 k19 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k19 1) (x2KeyMult 2 k19 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k19 2) (x2KeyMult 2 k19 2) 512 = true ∧ gj310.length = x2KeySize 2 k19 ∧ x2KeySize 2 k19 ≤ 512 ∧ v310.length = 7 := by decide +kernel
theorem chk19 : trialKeyChk 2 k19 7 gj310 x2Trial_310 v310 :=
  trialKeyChk_intro 2 k19 7 gj310 x2Trial_310 v310 small19 gjok19 vok19
def k20 : x2Key 2 := ⟨20, by decide⟩
x2_gj_cols gj311 311 2 0 4 4 256
theorem gjc20_0 : (List.range 7).all (fun d => gjCheck 256 2 0 4 4 1 15 15 (x2JCols 311 (0 + d)) (gj311.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok20 : ∀ d < x2KeySize 2 k20, gjCheck 256 2 (x2KeyTypes 2 k20 0) (x2KeyTypes 2 k20 1) (x2KeyTypes 2 k20 2) (x2KeyMult 2 k20 0) (x2KeyMult 2 k20 1) (x2KeyMult 2 k20 2) (x2JCols (x2KeyGlobal 2 k20) d) (gj311.getD d 0) = true := by
  have hr : x2KeySize 2 k20 = 7 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 0 4 4 1 15 15 (x2JCols 311 d) (gj311.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 0 4 4 1 15 15 (x2JCols 311 d) (gj311.getD d 0)) 0 7 gjc20_0 d (Nat.zero_le d) (by omega)
x2_v_cols v311 gj311 311 256 225
theorem vc20_0 : (List.range 5).all (fun c => vCheck 256 225 7 gj311 (x2Trial_311.getD (0 + c) 0) (v311.getD (0 + c) 0)) = true := by decide +kernel
theorem vok20 : ∀ c < 5, vCheck 256 (x2KeyMult 2 k20 0 * x2KeyMult 2 k20 1 * x2KeyMult 2 k20 2) (x2KeySize 2 k20) gj311 (x2Trial_311.getD c 0) (v311.getD c 0) = true := by
  intro c hc
  show vCheck 256 225 7 gj311 (x2Trial_311.getD c 0) (v311.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 225 7 gj311 (x2Trial_311.getD c 0) (v311.getD c 0)) 0 5 vc20_0 c (Nat.zero_le c) (by omega)
theorem small20 : x2KeyDegree 2 k20 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k20 0 ∧ 1 ≤ x2KeyMult 2 k20 1 ∧ 1 ≤ x2KeyMult 2 k20 2 ∧ glRowOK 2 (x2KeyTypes 2 k20 0) (x2KeyMult 2 k20 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k20 1) (x2KeyMult 2 k20 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k20 2) (x2KeyMult 2 k20 2) 512 = true ∧ gj311.length = x2KeySize 2 k20 ∧ x2KeySize 2 k20 ≤ 512 ∧ v311.length = 5 := by decide +kernel
theorem chk20 : trialKeyChk 2 k20 5 gj311 x2Trial_311 v311 :=
  trialKeyChk_intro 2 k20 5 gj311 x2Trial_311 v311 small20 gjok20 vok20

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k19, ibFS [(v310, v310, 94810963968000)]), (k20, ibFS [(v311, v311, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![0, 4, 4] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN19 : N k19 = x2TrialForm 2 k19) (hN20 : N k20 = x2TrialForm 2 k20) :
    ∀ e ∈ ks, keyOK (x2Mult 2 0 * x2Mult 2 4 * x2Mult 2 4) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 2 N k19 7 _ gj310 x2Trial_310 v310 (by decide) (by rw [hN19]; exact trialForm_eq 2 k19 7 x2Trial_310 (by decide) rfl) chk19
  · exact keyOK_of_trialChk 2 N k20 5 _ gj311 x2Trial_311 v311 (by decide) (by rw [hN20]; exact trialForm_eq 2 k20 5 x2Trial_311 (by decide) rfl) chk20

end ThreeCopyQutritWerner.X2.InK2x044
