module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (1, 6, 6) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x166
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k69 : x2Key 1 := ⟨69, by decide⟩
x2_gj_cols gj191 191 1 1 6 6 256
theorem gjc69_0 : (List.range 51).all (fun d => gjCheck 256 1 1 6 6 2 17 17 (x2JCols 191 (0 + d)) (gj191.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok69 : ∀ d < x2KeySize 1 k69, gjCheck 256 1 (x2KeyTypes 1 k69 0) (x2KeyTypes 1 k69 1) (x2KeyTypes 1 k69 2) (x2KeyMult 1 k69 0) (x2KeyMult 1 k69 1) (x2KeyMult 1 k69 2) (x2JCols (x2KeyGlobal 1 k69) d) (gj191.getD d 0) = true := by
  have hr : x2KeySize 1 k69 = 51 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 1 6 6 2 17 17 (x2JCols 191 d) (gj191.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 1 6 6 2 17 17 (x2JCols 191 d) (gj191.getD d 0)) 0 51 gjc69_0 d (Nat.zero_le d) (by omega)
x2_v_cols v191 gj191 191 256 578
theorem vc69_0 : (List.range 21).all (fun c => vCheck 256 578 51 gj191 (x2Trial_191.getD (0 + c) 0) (v191.getD (0 + c) 0)) = true := by decide +kernel
theorem vok69 : ∀ c < 21, vCheck 256 (x2KeyMult 1 k69 0 * x2KeyMult 1 k69 1 * x2KeyMult 1 k69 2) (x2KeySize 1 k69) gj191 (x2Trial_191.getD c 0) (v191.getD c 0) = true := by
  intro c hc
  show vCheck 256 578 51 gj191 (x2Trial_191.getD c 0) (v191.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 578 51 gj191 (x2Trial_191.getD c 0) (v191.getD c 0)) 0 21 vc69_0 c (Nat.zero_le c) (by omega)
theorem small69 : x2KeyDegree 1 k69 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k69 0 ∧ 1 ≤ x2KeyMult 1 k69 1 ∧ 1 ≤ x2KeyMult 1 k69 2 ∧ glRowOK 1 (x2KeyTypes 1 k69 0) (x2KeyMult 1 k69 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k69 1) (x2KeyMult 1 k69 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k69 2) (x2KeyMult 1 k69 2) 512 = true ∧ gj191.length = x2KeySize 1 k69 ∧ x2KeySize 1 k69 ≤ 512 ∧ v191.length = 21 := by decide +kernel
theorem chk69 : trialKeyChk 1 k69 21 gj191 x2Trial_191 v191 :=
  trialKeyChk_intro 1 k69 21 gj191 x2Trial_191 v191 small69 gjok69 vok69
def k70 : x2Key 1 := ⟨70, by decide⟩
x2_gj_cols gj192 192 1 1 6 6 256
theorem gjc70_0 : (List.range 45).all (fun d => gjCheck 256 1 1 6 6 2 17 17 (x2JCols 192 (0 + d)) (gj192.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok70 : ∀ d < x2KeySize 1 k70, gjCheck 256 1 (x2KeyTypes 1 k70 0) (x2KeyTypes 1 k70 1) (x2KeyTypes 1 k70 2) (x2KeyMult 1 k70 0) (x2KeyMult 1 k70 1) (x2KeyMult 1 k70 2) (x2JCols (x2KeyGlobal 1 k70) d) (gj192.getD d 0) = true := by
  have hr : x2KeySize 1 k70 = 45 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 1 6 6 2 17 17 (x2JCols 192 d) (gj192.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 1 6 6 2 17 17 (x2JCols 192 d) (gj192.getD d 0)) 0 45 gjc70_0 d (Nat.zero_le d) (by omega)
x2_v_cols v192 gj192 192 256 578
theorem vc70_0 : (List.range 20).all (fun c => vCheck 256 578 45 gj192 (x2Trial_192.getD (0 + c) 0) (v192.getD (0 + c) 0)) = true := by decide +kernel
theorem vok70 : ∀ c < 20, vCheck 256 (x2KeyMult 1 k70 0 * x2KeyMult 1 k70 1 * x2KeyMult 1 k70 2) (x2KeySize 1 k70) gj192 (x2Trial_192.getD c 0) (v192.getD c 0) = true := by
  intro c hc
  show vCheck 256 578 45 gj192 (x2Trial_192.getD c 0) (v192.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 578 45 gj192 (x2Trial_192.getD c 0) (v192.getD c 0)) 0 20 vc70_0 c (Nat.zero_le c) (by omega)
theorem small70 : x2KeyDegree 1 k70 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k70 0 ∧ 1 ≤ x2KeyMult 1 k70 1 ∧ 1 ≤ x2KeyMult 1 k70 2 ∧ glRowOK 1 (x2KeyTypes 1 k70 0) (x2KeyMult 1 k70 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k70 1) (x2KeyMult 1 k70 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k70 2) (x2KeyMult 1 k70 2) 512 = true ∧ gj192.length = x2KeySize 1 k70 ∧ x2KeySize 1 k70 ≤ 512 ∧ v192.length = 20 := by decide +kernel
theorem chk70 : trialKeyChk 1 k70 20 gj192 x2Trial_192 v192 :=
  trialKeyChk_intro 1 k70 20 gj192 x2Trial_192 v192 small70 gjok70 vok70

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k69, ibFS [(v191, v191, 94810963968000)]), (k70, ibFS [(v192, v192, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![1, 6, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN69 : N k69 = x2TrialForm 1 k69) (hN70 : N k70 = x2TrialForm 1 k70) :
    ∀ e ∈ ks, keyOK (x2Mult 1 1 * x2Mult 1 6 * x2Mult 1 6) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 1 N k69 21 _ gj191 x2Trial_191 v191 (by decide) (by rw [hN69]; exact trialForm_eq 1 k69 21 x2Trial_191 (by decide) rfl) chk69
  · exact keyOK_of_trialChk 1 N k70 20 _ gj192 x2Trial_192 v192 (by decide) (by rw [hN70]; exact trialForm_eq 1 k70 20 x2Trial_192 (by decide) rfl) chk70

end ThreeCopyQutritWerner.X2.InK1x166
