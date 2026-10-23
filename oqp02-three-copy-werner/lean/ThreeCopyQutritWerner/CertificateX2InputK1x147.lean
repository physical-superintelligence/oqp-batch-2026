module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (1, 4, 7) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x147
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k64 : x2Key 1 := ⟨64, by decide⟩
x2_gj_cols gj186 186 1 1 4 7 256
theorem gjc64_0 : (List.range 14).all (fun d => gjCheck 256 1 1 4 7 2 7 6 (x2JCols 186 (0 + d)) (gj186.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok64 : ∀ d < x2KeySize 1 k64, gjCheck 256 1 (x2KeyTypes 1 k64 0) (x2KeyTypes 1 k64 1) (x2KeyTypes 1 k64 2) (x2KeyMult 1 k64 0) (x2KeyMult 1 k64 1) (x2KeyMult 1 k64 2) (x2JCols (x2KeyGlobal 1 k64) d) (gj186.getD d 0) = true := by
  have hr : x2KeySize 1 k64 = 14 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 1 4 7 2 7 6 (x2JCols 186 d) (gj186.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 1 4 7 2 7 6 (x2JCols 186 d) (gj186.getD d 0)) 0 14 gjc64_0 d (Nat.zero_le d) (by omega)
x2_v_cols v186 gj186 186 256 84
theorem vc64_0 : (List.range 3).all (fun c => vCheck 256 84 14 gj186 (x2Trial_186.getD (0 + c) 0) (v186.getD (0 + c) 0)) = true := by decide +kernel
theorem vok64 : ∀ c < 3, vCheck 256 (x2KeyMult 1 k64 0 * x2KeyMult 1 k64 1 * x2KeyMult 1 k64 2) (x2KeySize 1 k64) gj186 (x2Trial_186.getD c 0) (v186.getD c 0) = true := by
  intro c hc
  show vCheck 256 84 14 gj186 (x2Trial_186.getD c 0) (v186.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 84 14 gj186 (x2Trial_186.getD c 0) (v186.getD c 0)) 0 3 vc64_0 c (Nat.zero_le c) (by omega)
theorem small64 : x2KeyDegree 1 k64 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k64 0 ∧ 1 ≤ x2KeyMult 1 k64 1 ∧ 1 ≤ x2KeyMult 1 k64 2 ∧ glRowOK 1 (x2KeyTypes 1 k64 0) (x2KeyMult 1 k64 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k64 1) (x2KeyMult 1 k64 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k64 2) (x2KeyMult 1 k64 2) 512 = true ∧ gj186.length = x2KeySize 1 k64 ∧ x2KeySize 1 k64 ≤ 512 ∧ v186.length = 3 := by decide +kernel
theorem chk64 : trialKeyChk 1 k64 3 gj186 x2Trial_186 v186 :=
  trialKeyChk_intro 1 k64 3 gj186 x2Trial_186 v186 small64 gjok64 vok64

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k64, ibFS [(v186, v186, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![1, 4, 7] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN64 : N k64 = x2TrialForm 1 k64) :
    ∀ e ∈ ks, keyOK (x2Mult 1 1 * x2Mult 1 4 * x2Mult 1 7) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k64 3 _ gj186 x2Trial_186 v186 (by decide) (by rw [hN64]; exact trialForm_eq 1 k64 3 x2Trial_186 (by decide) rfl) chk64

end ThreeCopyQutritWerner.X2.InK1x147
