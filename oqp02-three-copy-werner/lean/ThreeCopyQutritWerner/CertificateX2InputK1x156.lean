module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (1, 5, 6) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x156
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k67 : x2Key 1 := ⟨67, by decide⟩
x2_gj_cols gj189 189 1 1 5 6 256
theorem gjc67_0 : (List.range 39).all (fun d => gjCheck 256 1 1 5 6 2 7 17 (x2JCols 189 (0 + d)) (gj189.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok67 : ∀ d < x2KeySize 1 k67, gjCheck 256 1 (x2KeyTypes 1 k67 0) (x2KeyTypes 1 k67 1) (x2KeyTypes 1 k67 2) (x2KeyMult 1 k67 0) (x2KeyMult 1 k67 1) (x2KeyMult 1 k67 2) (x2JCols (x2KeyGlobal 1 k67) d) (gj189.getD d 0) = true := by
  have hr : x2KeySize 1 k67 = 39 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 1 5 6 2 7 17 (x2JCols 189 d) (gj189.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 1 5 6 2 7 17 (x2JCols 189 d) (gj189.getD d 0)) 0 39 gjc67_0 d (Nat.zero_le d) (by omega)
x2_v_cols v189 gj189 189 256 238
theorem vc67_0 : (List.range 15).all (fun c => vCheck 256 238 39 gj189 (x2Trial_189.getD (0 + c) 0) (v189.getD (0 + c) 0)) = true := by decide +kernel
theorem vok67 : ∀ c < 15, vCheck 256 (x2KeyMult 1 k67 0 * x2KeyMult 1 k67 1 * x2KeyMult 1 k67 2) (x2KeySize 1 k67) gj189 (x2Trial_189.getD c 0) (v189.getD c 0) = true := by
  intro c hc
  show vCheck 256 238 39 gj189 (x2Trial_189.getD c 0) (v189.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 238 39 gj189 (x2Trial_189.getD c 0) (v189.getD c 0)) 0 15 vc67_0 c (Nat.zero_le c) (by omega)
theorem small67 : x2KeyDegree 1 k67 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k67 0 ∧ 1 ≤ x2KeyMult 1 k67 1 ∧ 1 ≤ x2KeyMult 1 k67 2 ∧ glRowOK 1 (x2KeyTypes 1 k67 0) (x2KeyMult 1 k67 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k67 1) (x2KeyMult 1 k67 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k67 2) (x2KeyMult 1 k67 2) 512 = true ∧ gj189.length = x2KeySize 1 k67 ∧ x2KeySize 1 k67 ≤ 512 ∧ v189.length = 15 := by decide +kernel
theorem chk67 : trialKeyChk 1 k67 15 gj189 x2Trial_189 v189 :=
  trialKeyChk_intro 1 k67 15 gj189 x2Trial_189 v189 small67 gjok67 vok67

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k67, ibFS [(v189, v189, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![1, 5, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN67 : N k67 = x2TrialForm 1 k67) :
    ∀ e ∈ ks, keyOK (x2Mult 1 1 * x2Mult 1 5 * x2Mult 1 6) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k67 15 _ gj189 x2Trial_189 v189 (by decide) (by rw [hN67]; exact trialForm_eq 1 k67 15 x2Trial_189 (by decide) rfl) chk67

end ThreeCopyQutritWerner.X2.InK1x156
