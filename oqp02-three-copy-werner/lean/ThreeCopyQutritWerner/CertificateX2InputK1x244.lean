module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (2, 4, 4) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x244
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k90 : x2Key 1 := ⟨90, by decide⟩
x2_gj_cols gj212 212 1 2 4 4 256
theorem gjc90_0 : (List.range 8).all (fun d => gjCheck 256 1 2 4 4 2 7 7 (x2JCols 212 (0 + d)) (gj212.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok90 : ∀ d < x2KeySize 1 k90, gjCheck 256 1 (x2KeyTypes 1 k90 0) (x2KeyTypes 1 k90 1) (x2KeyTypes 1 k90 2) (x2KeyMult 1 k90 0) (x2KeyMult 1 k90 1) (x2KeyMult 1 k90 2) (x2JCols (x2KeyGlobal 1 k90) d) (gj212.getD d 0) = true := by
  have hr : x2KeySize 1 k90 = 8 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 2 4 4 2 7 7 (x2JCols 212 d) (gj212.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 2 4 4 2 7 7 (x2JCols 212 d) (gj212.getD d 0)) 0 8 gjc90_0 d (Nat.zero_le d) (by omega)
x2_v_cols v212 gj212 212 256 98
theorem vc90_0 : (List.range 2).all (fun c => vCheck 256 98 8 gj212 (x2Trial_212.getD (0 + c) 0) (v212.getD (0 + c) 0)) = true := by decide +kernel
theorem vok90 : ∀ c < 2, vCheck 256 (x2KeyMult 1 k90 0 * x2KeyMult 1 k90 1 * x2KeyMult 1 k90 2) (x2KeySize 1 k90) gj212 (x2Trial_212.getD c 0) (v212.getD c 0) = true := by
  intro c hc
  show vCheck 256 98 8 gj212 (x2Trial_212.getD c 0) (v212.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 98 8 gj212 (x2Trial_212.getD c 0) (v212.getD c 0)) 0 2 vc90_0 c (Nat.zero_le c) (by omega)
theorem small90 : x2KeyDegree 1 k90 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k90 0 ∧ 1 ≤ x2KeyMult 1 k90 1 ∧ 1 ≤ x2KeyMult 1 k90 2 ∧ glRowOK 1 (x2KeyTypes 1 k90 0) (x2KeyMult 1 k90 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k90 1) (x2KeyMult 1 k90 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k90 2) (x2KeyMult 1 k90 2) 512 = true ∧ gj212.length = x2KeySize 1 k90 ∧ x2KeySize 1 k90 ≤ 512 ∧ v212.length = 2 := by decide +kernel
theorem chk90 : trialKeyChk 1 k90 2 gj212 x2Trial_212 v212 :=
  trialKeyChk_intro 1 k90 2 gj212 x2Trial_212 v212 small90 gjok90 vok90
def k91 : x2Key 1 := ⟨91, by decide⟩
x2_gj_cols gj213 213 1 2 4 4 256
theorem gjc91_0 : (List.range 8).all (fun d => gjCheck 256 1 2 4 4 2 7 7 (x2JCols 213 (0 + d)) (gj213.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok91 : ∀ d < x2KeySize 1 k91, gjCheck 256 1 (x2KeyTypes 1 k91 0) (x2KeyTypes 1 k91 1) (x2KeyTypes 1 k91 2) (x2KeyMult 1 k91 0) (x2KeyMult 1 k91 1) (x2KeyMult 1 k91 2) (x2JCols (x2KeyGlobal 1 k91) d) (gj213.getD d 0) = true := by
  have hr : x2KeySize 1 k91 = 8 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 2 4 4 2 7 7 (x2JCols 213 d) (gj213.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 2 4 4 2 7 7 (x2JCols 213 d) (gj213.getD d 0)) 0 8 gjc91_0 d (Nat.zero_le d) (by omega)
x2_v_cols v213 gj213 213 256 98
theorem vc91_0 : (List.range 2).all (fun c => vCheck 256 98 8 gj213 (x2Trial_213.getD (0 + c) 0) (v213.getD (0 + c) 0)) = true := by decide +kernel
theorem vok91 : ∀ c < 2, vCheck 256 (x2KeyMult 1 k91 0 * x2KeyMult 1 k91 1 * x2KeyMult 1 k91 2) (x2KeySize 1 k91) gj213 (x2Trial_213.getD c 0) (v213.getD c 0) = true := by
  intro c hc
  show vCheck 256 98 8 gj213 (x2Trial_213.getD c 0) (v213.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 98 8 gj213 (x2Trial_213.getD c 0) (v213.getD c 0)) 0 2 vc91_0 c (Nat.zero_le c) (by omega)
theorem small91 : x2KeyDegree 1 k91 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k91 0 ∧ 1 ≤ x2KeyMult 1 k91 1 ∧ 1 ≤ x2KeyMult 1 k91 2 ∧ glRowOK 1 (x2KeyTypes 1 k91 0) (x2KeyMult 1 k91 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k91 1) (x2KeyMult 1 k91 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k91 2) (x2KeyMult 1 k91 2) 512 = true ∧ gj213.length = x2KeySize 1 k91 ∧ x2KeySize 1 k91 ≤ 512 ∧ v213.length = 2 := by decide +kernel
theorem chk91 : trialKeyChk 1 k91 2 gj213 x2Trial_213 v213 :=
  trialKeyChk_intro 1 k91 2 gj213 x2Trial_213 v213 small91 gjok91 vok91

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k90, ibFS [(v212, v212, 94810963968000)]), (k91, ibFS [(v213, v213, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![2, 4, 4] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN90 : N k90 = x2TrialForm 1 k90) (hN91 : N k91 = x2TrialForm 1 k91) :
    ∀ e ∈ ks, keyOK (x2Mult 1 2 * x2Mult 1 4 * x2Mult 1 4) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 1 N k90 2 _ gj212 x2Trial_212 v212 (by decide) (by rw [hN90]; exact trialForm_eq 1 k90 2 x2Trial_212 (by decide) rfl) chk90
  · exact keyOK_of_trialChk 1 N k91 2 _ gj213 x2Trial_213 v213 (by decide) (by rw [hN91]; exact trialForm_eq 1 k91 2 x2Trial_213 (by decide) rfl) chk91

end ThreeCopyQutritWerner.X2.InK1x244
