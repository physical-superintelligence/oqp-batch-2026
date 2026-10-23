module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (1, 4, 6) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x146
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k63 : x2Key 1 := ⟨63, by decide⟩
x2_gj_cols gj185 185 1 1 4 6 256
theorem gjc63_0 : (List.range 40).all (fun d => gjCheck 256 1 1 4 6 2 7 17 (x2JCols 185 (0 + d)) (gj185.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok63 : ∀ d < x2KeySize 1 k63, gjCheck 256 1 (x2KeyTypes 1 k63 0) (x2KeyTypes 1 k63 1) (x2KeyTypes 1 k63 2) (x2KeyMult 1 k63 0) (x2KeyMult 1 k63 1) (x2KeyMult 1 k63 2) (x2JCols (x2KeyGlobal 1 k63) d) (gj185.getD d 0) = true := by
  have hr : x2KeySize 1 k63 = 40 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 1 4 6 2 7 17 (x2JCols 185 d) (gj185.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 1 4 6 2 7 17 (x2JCols 185 d) (gj185.getD d 0)) 0 40 gjc63_0 d (Nat.zero_le d) (by omega)
x2_v_cols v185 gj185 185 256 238
theorem vc63_0 : (List.range 13).all (fun c => vCheck 256 238 40 gj185 (x2Trial_185.getD (0 + c) 0) (v185.getD (0 + c) 0)) = true := by decide +kernel
theorem vok63 : ∀ c < 13, vCheck 256 (x2KeyMult 1 k63 0 * x2KeyMult 1 k63 1 * x2KeyMult 1 k63 2) (x2KeySize 1 k63) gj185 (x2Trial_185.getD c 0) (v185.getD c 0) = true := by
  intro c hc
  show vCheck 256 238 40 gj185 (x2Trial_185.getD c 0) (v185.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 238 40 gj185 (x2Trial_185.getD c 0) (v185.getD c 0)) 0 13 vc63_0 c (Nat.zero_le c) (by omega)
theorem small63 : x2KeyDegree 1 k63 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k63 0 ∧ 1 ≤ x2KeyMult 1 k63 1 ∧ 1 ≤ x2KeyMult 1 k63 2 ∧ glRowOK 1 (x2KeyTypes 1 k63 0) (x2KeyMult 1 k63 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k63 1) (x2KeyMult 1 k63 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k63 2) (x2KeyMult 1 k63 2) 512 = true ∧ gj185.length = x2KeySize 1 k63 ∧ x2KeySize 1 k63 ≤ 512 ∧ v185.length = 13 := by decide +kernel
theorem chk63 : trialKeyChk 1 k63 13 gj185 x2Trial_185 v185 :=
  trialKeyChk_intro 1 k63 13 gj185 x2Trial_185 v185 small63 gjok63 vok63

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k63, ibFS [(v185, v185, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![1, 4, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN63 : N k63 = x2TrialForm 1 k63) :
    ∀ e ∈ ks, keyOK (x2Mult 1 1 * x2Mult 1 4 * x2Mult 1 6) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k63 13 _ gj185 x2Trial_185 v185 (by decide) (by rw [hN63]; exact trialForm_eq 1 k63 13 x2Trial_185 (by decide) rfl) chk63

end ThreeCopyQutritWerner.X2.InK1x146
