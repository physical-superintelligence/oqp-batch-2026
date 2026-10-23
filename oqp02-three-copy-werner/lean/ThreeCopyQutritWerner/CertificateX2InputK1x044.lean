module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (0, 4, 4) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x044
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k22 : x2Key 1 := ⟨22, by decide⟩
x2_gj_cols gj144 144 1 0 4 4 256
theorem gjc22_0 : (List.range 4).all (fun d => gjCheck 256 1 0 4 4 1 7 7 (x2JCols 144 (0 + d)) (gj144.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok22 : ∀ d < x2KeySize 1 k22, gjCheck 256 1 (x2KeyTypes 1 k22 0) (x2KeyTypes 1 k22 1) (x2KeyTypes 1 k22 2) (x2KeyMult 1 k22 0) (x2KeyMult 1 k22 1) (x2KeyMult 1 k22 2) (x2JCols (x2KeyGlobal 1 k22) d) (gj144.getD d 0) = true := by
  have hr : x2KeySize 1 k22 = 4 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 0 4 4 1 7 7 (x2JCols 144 d) (gj144.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 0 4 4 1 7 7 (x2JCols 144 d) (gj144.getD d 0)) 0 4 gjc22_0 d (Nat.zero_le d) (by omega)
x2_v_cols v144 gj144 144 256 49
theorem vc22_0 : (List.range 1).all (fun c => vCheck 256 49 4 gj144 (x2Trial_144.getD (0 + c) 0) (v144.getD (0 + c) 0)) = true := by decide +kernel
theorem vok22 : ∀ c < 1, vCheck 256 (x2KeyMult 1 k22 0 * x2KeyMult 1 k22 1 * x2KeyMult 1 k22 2) (x2KeySize 1 k22) gj144 (x2Trial_144.getD c 0) (v144.getD c 0) = true := by
  intro c hc
  show vCheck 256 49 4 gj144 (x2Trial_144.getD c 0) (v144.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 49 4 gj144 (x2Trial_144.getD c 0) (v144.getD c 0)) 0 1 vc22_0 c (Nat.zero_le c) (by omega)
theorem small22 : x2KeyDegree 1 k22 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k22 0 ∧ 1 ≤ x2KeyMult 1 k22 1 ∧ 1 ≤ x2KeyMult 1 k22 2 ∧ glRowOK 1 (x2KeyTypes 1 k22 0) (x2KeyMult 1 k22 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k22 1) (x2KeyMult 1 k22 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k22 2) (x2KeyMult 1 k22 2) 512 = true ∧ gj144.length = x2KeySize 1 k22 ∧ x2KeySize 1 k22 ≤ 512 ∧ v144.length = 1 := by decide +kernel
theorem chk22 : trialKeyChk 1 k22 1 gj144 x2Trial_144 v144 :=
  trialKeyChk_intro 1 k22 1 gj144 x2Trial_144 v144 small22 gjok22 vok22
def k23 : x2Key 1 := ⟨23, by decide⟩
x2_gj_cols gj145 145 1 0 4 4 256
theorem gjc23_0 : (List.range 4).all (fun d => gjCheck 256 1 0 4 4 1 7 7 (x2JCols 145 (0 + d)) (gj145.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok23 : ∀ d < x2KeySize 1 k23, gjCheck 256 1 (x2KeyTypes 1 k23 0) (x2KeyTypes 1 k23 1) (x2KeyTypes 1 k23 2) (x2KeyMult 1 k23 0) (x2KeyMult 1 k23 1) (x2KeyMult 1 k23 2) (x2JCols (x2KeyGlobal 1 k23) d) (gj145.getD d 0) = true := by
  have hr : x2KeySize 1 k23 = 4 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 0 4 4 1 7 7 (x2JCols 145 d) (gj145.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 0 4 4 1 7 7 (x2JCols 145 d) (gj145.getD d 0)) 0 4 gjc23_0 d (Nat.zero_le d) (by omega)
x2_v_cols v145 gj145 145 256 49
theorem vc23_0 : (List.range 1).all (fun c => vCheck 256 49 4 gj145 (x2Trial_145.getD (0 + c) 0) (v145.getD (0 + c) 0)) = true := by decide +kernel
theorem vok23 : ∀ c < 1, vCheck 256 (x2KeyMult 1 k23 0 * x2KeyMult 1 k23 1 * x2KeyMult 1 k23 2) (x2KeySize 1 k23) gj145 (x2Trial_145.getD c 0) (v145.getD c 0) = true := by
  intro c hc
  show vCheck 256 49 4 gj145 (x2Trial_145.getD c 0) (v145.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 49 4 gj145 (x2Trial_145.getD c 0) (v145.getD c 0)) 0 1 vc23_0 c (Nat.zero_le c) (by omega)
theorem small23 : x2KeyDegree 1 k23 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k23 0 ∧ 1 ≤ x2KeyMult 1 k23 1 ∧ 1 ≤ x2KeyMult 1 k23 2 ∧ glRowOK 1 (x2KeyTypes 1 k23 0) (x2KeyMult 1 k23 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k23 1) (x2KeyMult 1 k23 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k23 2) (x2KeyMult 1 k23 2) 512 = true ∧ gj145.length = x2KeySize 1 k23 ∧ x2KeySize 1 k23 ≤ 512 ∧ v145.length = 1 := by decide +kernel
theorem chk23 : trialKeyChk 1 k23 1 gj145 x2Trial_145 v145 :=
  trialKeyChk_intro 1 k23 1 gj145 x2Trial_145 v145 small23 gjok23 vok23

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k22, ibFS [(v144, v144, 94810963968000)]), (k23, ibFS [(v145, v145, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![0, 4, 4] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN22 : N k22 = x2TrialForm 1 k22) (hN23 : N k23 = x2TrialForm 1 k23) :
    ∀ e ∈ ks, keyOK (x2Mult 1 0 * x2Mult 1 4 * x2Mult 1 4) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 1 N k22 1 _ gj144 x2Trial_144 v144 (by decide) (by rw [hN22]; exact trialForm_eq 1 k22 1 x2Trial_144 (by decide) rfl) chk22
  · exact keyOK_of_trialChk 1 N k23 1 _ gj145 x2Trial_145 v145 (by decide) (by rw [hN23]; exact trialForm_eq 1 k23 1 x2Trial_145 (by decide) rfl) chk23

end ThreeCopyQutritWerner.X2.InK1x044
