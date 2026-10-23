module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (2, 3, 5) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x235
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k87 : x2Key 1 := ⟨87, by decide⟩
x2_gj_cols gj209 209 1 2 3 5 256
theorem gjc87_0 : (List.range 18).all (fun d => gjCheck 256 1 2 3 5 2 9 7 (x2JCols 209 (0 + d)) (gj209.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok87 : ∀ d < x2KeySize 1 k87, gjCheck 256 1 (x2KeyTypes 1 k87 0) (x2KeyTypes 1 k87 1) (x2KeyTypes 1 k87 2) (x2KeyMult 1 k87 0) (x2KeyMult 1 k87 1) (x2KeyMult 1 k87 2) (x2JCols (x2KeyGlobal 1 k87) d) (gj209.getD d 0) = true := by
  have hr : x2KeySize 1 k87 = 18 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 2 3 5 2 9 7 (x2JCols 209 d) (gj209.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 2 3 5 2 9 7 (x2JCols 209 d) (gj209.getD d 0)) 0 18 gjc87_0 d (Nat.zero_le d) (by omega)
x2_v_cols v209 gj209 209 256 126
theorem vc87_0 : (List.range 2).all (fun c => vCheck 256 126 18 gj209 (x2Trial_209.getD (0 + c) 0) (v209.getD (0 + c) 0)) = true := by decide +kernel
theorem vok87 : ∀ c < 2, vCheck 256 (x2KeyMult 1 k87 0 * x2KeyMult 1 k87 1 * x2KeyMult 1 k87 2) (x2KeySize 1 k87) gj209 (x2Trial_209.getD c 0) (v209.getD c 0) = true := by
  intro c hc
  show vCheck 256 126 18 gj209 (x2Trial_209.getD c 0) (v209.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 126 18 gj209 (x2Trial_209.getD c 0) (v209.getD c 0)) 0 2 vc87_0 c (Nat.zero_le c) (by omega)
theorem small87 : x2KeyDegree 1 k87 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k87 0 ∧ 1 ≤ x2KeyMult 1 k87 1 ∧ 1 ≤ x2KeyMult 1 k87 2 ∧ glRowOK 1 (x2KeyTypes 1 k87 0) (x2KeyMult 1 k87 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k87 1) (x2KeyMult 1 k87 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k87 2) (x2KeyMult 1 k87 2) 512 = true ∧ gj209.length = x2KeySize 1 k87 ∧ x2KeySize 1 k87 ≤ 512 ∧ v209.length = 2 := by decide +kernel
theorem chk87 : trialKeyChk 1 k87 2 gj209 x2Trial_209 v209 :=
  trialKeyChk_intro 1 k87 2 gj209 x2Trial_209 v209 small87 gjok87 vok87

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k87, ibFS [(v209, v209, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![2, 3, 5] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN87 : N k87 = x2TrialForm 1 k87) :
    ∀ e ∈ ks, keyOK (x2Mult 1 2 * x2Mult 1 3 * x2Mult 1 5) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k87 2 _ gj209 x2Trial_209 v209 (by decide) (by rw [hN87]; exact trialForm_eq 1 k87 2 x2Trial_209 (by decide) rfl) chk87

end ThreeCopyQutritWerner.X2.InK1x235
