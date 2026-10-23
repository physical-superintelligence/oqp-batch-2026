module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (0, 4, 7) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x047
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k26 : x2Key 1 := ⟨26, by decide⟩
x2_gj_cols gj148 148 1 0 4 7 256
theorem gjc26_0 : (List.range 7).all (fun d => gjCheck 256 1 0 4 7 1 7 6 (x2JCols 148 (0 + d)) (gj148.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok26 : ∀ d < x2KeySize 1 k26, gjCheck 256 1 (x2KeyTypes 1 k26 0) (x2KeyTypes 1 k26 1) (x2KeyTypes 1 k26 2) (x2KeyMult 1 k26 0) (x2KeyMult 1 k26 1) (x2KeyMult 1 k26 2) (x2JCols (x2KeyGlobal 1 k26) d) (gj148.getD d 0) = true := by
  have hr : x2KeySize 1 k26 = 7 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 0 4 7 1 7 6 (x2JCols 148 d) (gj148.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 0 4 7 1 7 6 (x2JCols 148 d) (gj148.getD d 0)) 0 7 gjc26_0 d (Nat.zero_le d) (by omega)
x2_v_cols v148 gj148 148 256 42
theorem vc26_0 : (List.range 2).all (fun c => vCheck 256 42 7 gj148 (x2Trial_148.getD (0 + c) 0) (v148.getD (0 + c) 0)) = true := by decide +kernel
theorem vok26 : ∀ c < 2, vCheck 256 (x2KeyMult 1 k26 0 * x2KeyMult 1 k26 1 * x2KeyMult 1 k26 2) (x2KeySize 1 k26) gj148 (x2Trial_148.getD c 0) (v148.getD c 0) = true := by
  intro c hc
  show vCheck 256 42 7 gj148 (x2Trial_148.getD c 0) (v148.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 42 7 gj148 (x2Trial_148.getD c 0) (v148.getD c 0)) 0 2 vc26_0 c (Nat.zero_le c) (by omega)
theorem small26 : x2KeyDegree 1 k26 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k26 0 ∧ 1 ≤ x2KeyMult 1 k26 1 ∧ 1 ≤ x2KeyMult 1 k26 2 ∧ glRowOK 1 (x2KeyTypes 1 k26 0) (x2KeyMult 1 k26 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k26 1) (x2KeyMult 1 k26 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k26 2) (x2KeyMult 1 k26 2) 512 = true ∧ gj148.length = x2KeySize 1 k26 ∧ x2KeySize 1 k26 ≤ 512 ∧ v148.length = 2 := by decide +kernel
theorem chk26 : trialKeyChk 1 k26 2 gj148 x2Trial_148 v148 :=
  trialKeyChk_intro 1 k26 2 gj148 x2Trial_148 v148 small26 gjok26 vok26

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k26, ibFS [(v148, v148, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![0, 4, 7] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN26 : N k26 = x2TrialForm 1 k26) :
    ∀ e ∈ ks, keyOK (x2Mult 1 0 * x2Mult 1 4 * x2Mult 1 7) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k26 2 _ gj148 x2Trial_148 v148 (by decide) (by rw [hN26]; exact trialForm_eq 1 k26 2 x2Trial_148 (by decide) rfl) chk26

end ThreeCopyQutritWerner.X2.InK1x047
