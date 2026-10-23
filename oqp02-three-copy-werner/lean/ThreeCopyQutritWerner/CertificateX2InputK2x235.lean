module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (2, 3, 5) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x235
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k73 : x2Key 2 := ⟨73, by decide⟩
x2_gj_cols gj364 364 2 2 3 5 256
theorem gjc73_0 : (List.range 20).all (fun d => gjCheck 256 2 2 3 5 5 5 10 (x2JCols 364 (0 + d)) (gj364.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok73 : ∀ d < x2KeySize 2 k73, gjCheck 256 2 (x2KeyTypes 2 k73 0) (x2KeyTypes 2 k73 1) (x2KeyTypes 2 k73 2) (x2KeyMult 2 k73 0) (x2KeyMult 2 k73 1) (x2KeyMult 2 k73 2) (x2JCols (x2KeyGlobal 2 k73) d) (gj364.getD d 0) = true := by
  have hr : x2KeySize 2 k73 = 20 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 2 3 5 5 5 10 (x2JCols 364 d) (gj364.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 2 3 5 5 5 10 (x2JCols 364 d) (gj364.getD d 0)) 0 20 gjc73_0 d (Nat.zero_le d) (by omega)
x2_v_cols v364 gj364 364 256 250
theorem vc73_0 : (List.range 10).all (fun c => vCheck 256 250 20 gj364 (x2Trial_364.getD (0 + c) 0) (v364.getD (0 + c) 0)) = true := by decide +kernel
theorem vok73 : ∀ c < 10, vCheck 256 (x2KeyMult 2 k73 0 * x2KeyMult 2 k73 1 * x2KeyMult 2 k73 2) (x2KeySize 2 k73) gj364 (x2Trial_364.getD c 0) (v364.getD c 0) = true := by
  intro c hc
  show vCheck 256 250 20 gj364 (x2Trial_364.getD c 0) (v364.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 250 20 gj364 (x2Trial_364.getD c 0) (v364.getD c 0)) 0 10 vc73_0 c (Nat.zero_le c) (by omega)
theorem small73 : x2KeyDegree 2 k73 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k73 0 ∧ 1 ≤ x2KeyMult 2 k73 1 ∧ 1 ≤ x2KeyMult 2 k73 2 ∧ glRowOK 2 (x2KeyTypes 2 k73 0) (x2KeyMult 2 k73 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k73 1) (x2KeyMult 2 k73 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k73 2) (x2KeyMult 2 k73 2) 512 = true ∧ gj364.length = x2KeySize 2 k73 ∧ x2KeySize 2 k73 ≤ 512 ∧ v364.length = 10 := by decide +kernel
theorem chk73 : trialKeyChk 2 k73 10 gj364 x2Trial_364 v364 :=
  trialKeyChk_intro 2 k73 10 gj364 x2Trial_364 v364 small73 gjok73 vok73

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k73, ibFS [(v364, v364, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![2, 3, 5] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN73 : N k73 = x2TrialForm 2 k73) :
    ∀ e ∈ ks, keyOK (x2Mult 2 2 * x2Mult 2 3 * x2Mult 2 5) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 2 N k73 10 _ gj364 x2Trial_364 v364 (by decide) (by rw [hN73]; exact trialForm_eq 2 k73 10 x2Trial_364 (by decide) rfl) chk73

end ThreeCopyQutritWerner.X2.InK2x235
