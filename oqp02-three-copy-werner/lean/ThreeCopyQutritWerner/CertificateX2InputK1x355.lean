module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (3, 5, 5) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x355
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k120 : x2Key 1 := ⟨120, by decide⟩
x2_gj_cols gj242 242 1 3 5 5 256
theorem gjc120_0 : (List.range 38).all (fun d => gjCheck 256 1 3 5 5 9 7 7 (x2JCols 242 (0 + d)) (gj242.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok120 : ∀ d < x2KeySize 1 k120, gjCheck 256 1 (x2KeyTypes 1 k120 0) (x2KeyTypes 1 k120 1) (x2KeyTypes 1 k120 2) (x2KeyMult 1 k120 0) (x2KeyMult 1 k120 1) (x2KeyMult 1 k120 2) (x2JCols (x2KeyGlobal 1 k120) d) (gj242.getD d 0) = true := by
  have hr : x2KeySize 1 k120 = 38 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 3 5 5 9 7 7 (x2JCols 242 d) (gj242.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 3 5 5 9 7 7 (x2JCols 242 d) (gj242.getD d 0)) 0 38 gjc120_0 d (Nat.zero_le d) (by omega)
x2_v_cols v242 gj242 242 256 441
theorem vc120_0 : (List.range 14).all (fun c => vCheck 256 441 38 gj242 (x2Trial_242.getD (0 + c) 0) (v242.getD (0 + c) 0)) = true := by decide +kernel
theorem vok120 : ∀ c < 14, vCheck 256 (x2KeyMult 1 k120 0 * x2KeyMult 1 k120 1 * x2KeyMult 1 k120 2) (x2KeySize 1 k120) gj242 (x2Trial_242.getD c 0) (v242.getD c 0) = true := by
  intro c hc
  show vCheck 256 441 38 gj242 (x2Trial_242.getD c 0) (v242.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 441 38 gj242 (x2Trial_242.getD c 0) (v242.getD c 0)) 0 14 vc120_0 c (Nat.zero_le c) (by omega)
theorem small120 : x2KeyDegree 1 k120 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k120 0 ∧ 1 ≤ x2KeyMult 1 k120 1 ∧ 1 ≤ x2KeyMult 1 k120 2 ∧ glRowOK 1 (x2KeyTypes 1 k120 0) (x2KeyMult 1 k120 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k120 1) (x2KeyMult 1 k120 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k120 2) (x2KeyMult 1 k120 2) 512 = true ∧ gj242.length = x2KeySize 1 k120 ∧ x2KeySize 1 k120 ≤ 512 ∧ v242.length = 14 := by decide +kernel
theorem chk120 : trialKeyChk 1 k120 14 gj242 x2Trial_242 v242 :=
  trialKeyChk_intro 1 k120 14 gj242 x2Trial_242 v242 small120 gjok120 vok120
def k121 : x2Key 1 := ⟨121, by decide⟩
x2_gj_cols gj243 243 1 3 5 5 256
theorem gjc121_0 : (List.range 31).all (fun d => gjCheck 256 1 3 5 5 9 7 7 (x2JCols 243 (0 + d)) (gj243.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok121 : ∀ d < x2KeySize 1 k121, gjCheck 256 1 (x2KeyTypes 1 k121 0) (x2KeyTypes 1 k121 1) (x2KeyTypes 1 k121 2) (x2KeyMult 1 k121 0) (x2KeyMult 1 k121 1) (x2KeyMult 1 k121 2) (x2JCols (x2KeyGlobal 1 k121) d) (gj243.getD d 0) = true := by
  have hr : x2KeySize 1 k121 = 31 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 3 5 5 9 7 7 (x2JCols 243 d) (gj243.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 3 5 5 9 7 7 (x2JCols 243 d) (gj243.getD d 0)) 0 31 gjc121_0 d (Nat.zero_le d) (by omega)
x2_v_cols v243 gj243 243 256 441
theorem vc121_0 : (List.range 14).all (fun c => vCheck 256 441 31 gj243 (x2Trial_243.getD (0 + c) 0) (v243.getD (0 + c) 0)) = true := by decide +kernel
theorem vok121 : ∀ c < 14, vCheck 256 (x2KeyMult 1 k121 0 * x2KeyMult 1 k121 1 * x2KeyMult 1 k121 2) (x2KeySize 1 k121) gj243 (x2Trial_243.getD c 0) (v243.getD c 0) = true := by
  intro c hc
  show vCheck 256 441 31 gj243 (x2Trial_243.getD c 0) (v243.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 441 31 gj243 (x2Trial_243.getD c 0) (v243.getD c 0)) 0 14 vc121_0 c (Nat.zero_le c) (by omega)
theorem small121 : x2KeyDegree 1 k121 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k121 0 ∧ 1 ≤ x2KeyMult 1 k121 1 ∧ 1 ≤ x2KeyMult 1 k121 2 ∧ glRowOK 1 (x2KeyTypes 1 k121 0) (x2KeyMult 1 k121 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k121 1) (x2KeyMult 1 k121 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k121 2) (x2KeyMult 1 k121 2) 512 = true ∧ gj243.length = x2KeySize 1 k121 ∧ x2KeySize 1 k121 ≤ 512 ∧ v243.length = 14 := by decide +kernel
theorem chk121 : trialKeyChk 1 k121 14 gj243 x2Trial_243 v243 :=
  trialKeyChk_intro 1 k121 14 gj243 x2Trial_243 v243 small121 gjok121 vok121

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k120, ibFS [(v242, v242, 94810963968000)]), (k121, ibFS [(v243, v243, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![3, 5, 5] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN120 : N k120 = x2TrialForm 1 k120) (hN121 : N k121 = x2TrialForm 1 k121) :
    ∀ e ∈ ks, keyOK (x2Mult 1 3 * x2Mult 1 5 * x2Mult 1 5) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 1 N k120 14 _ gj242 x2Trial_242 v242 (by decide) (by rw [hN120]; exact trialForm_eq 1 k120 14 x2Trial_242 (by decide) rfl) chk120
  · exact keyOK_of_trialChk 1 N k121 14 _ gj243 x2Trial_243 v243 (by decide) (by rw [hN121]; exact trialForm_eq 1 k121 14 x2Trial_243 (by decide) rfl) chk121

end ThreeCopyQutritWerner.X2.InK1x355
