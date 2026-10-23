module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (1, 3, 5) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x135
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k49 : x2Key 2 := ⟨49, by decide⟩
x2_gj_cols gj340 340 2 1 3 5 256
theorem gjc49_0 : (List.range 16).all (fun d => gjCheck 256 2 1 3 5 4 5 10 (x2JCols 340 (0 + d)) (gj340.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok49 : ∀ d < x2KeySize 2 k49, gjCheck 256 2 (x2KeyTypes 2 k49 0) (x2KeyTypes 2 k49 1) (x2KeyTypes 2 k49 2) (x2KeyMult 2 k49 0) (x2KeyMult 2 k49 1) (x2KeyMult 2 k49 2) (x2JCols (x2KeyGlobal 2 k49) d) (gj340.getD d 0) = true := by
  have hr : x2KeySize 2 k49 = 16 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 1 3 5 4 5 10 (x2JCols 340 d) (gj340.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 1 3 5 4 5 10 (x2JCols 340 d) (gj340.getD d 0)) 0 16 gjc49_0 d (Nat.zero_le d) (by omega)
x2_v_cols v340 gj340 340 256 200
theorem vc49_0 : (List.range 8).all (fun c => vCheck 256 200 16 gj340 (x2Trial_340.getD (0 + c) 0) (v340.getD (0 + c) 0)) = true := by decide +kernel
theorem vok49 : ∀ c < 8, vCheck 256 (x2KeyMult 2 k49 0 * x2KeyMult 2 k49 1 * x2KeyMult 2 k49 2) (x2KeySize 2 k49) gj340 (x2Trial_340.getD c 0) (v340.getD c 0) = true := by
  intro c hc
  show vCheck 256 200 16 gj340 (x2Trial_340.getD c 0) (v340.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 200 16 gj340 (x2Trial_340.getD c 0) (v340.getD c 0)) 0 8 vc49_0 c (Nat.zero_le c) (by omega)
theorem small49 : x2KeyDegree 2 k49 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k49 0 ∧ 1 ≤ x2KeyMult 2 k49 1 ∧ 1 ≤ x2KeyMult 2 k49 2 ∧ glRowOK 2 (x2KeyTypes 2 k49 0) (x2KeyMult 2 k49 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k49 1) (x2KeyMult 2 k49 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k49 2) (x2KeyMult 2 k49 2) 512 = true ∧ gj340.length = x2KeySize 2 k49 ∧ x2KeySize 2 k49 ≤ 512 ∧ v340.length = 8 := by decide +kernel
theorem chk49 : trialKeyChk 2 k49 8 gj340 x2Trial_340 v340 :=
  trialKeyChk_intro 2 k49 8 gj340 x2Trial_340 v340 small49 gjok49 vok49

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k49, ibFS [(v340, v340, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![1, 3, 5] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN49 : N k49 = x2TrialForm 2 k49) :
    ∀ e ∈ ks, keyOK (x2Mult 2 1 * x2Mult 2 3 * x2Mult 2 5) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 2 N k49 8 _ gj340 x2Trial_340 v340 (by decide) (by rw [hN49]; exact trialForm_eq 2 k49 8 x2Trial_340 (by decide) rfl) chk49

end ThreeCopyQutritWerner.X2.InK2x135
