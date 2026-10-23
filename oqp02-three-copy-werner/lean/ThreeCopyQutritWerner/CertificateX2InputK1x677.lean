module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (6, 7, 7) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x677
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k164 : x2Key 1 := ⟨164, by decide⟩
x2_gj_cols gj286 286 1 6 7 7 256
theorem gjc164_0 : (List.range 59).all (fun d => gjCheck 256 1 6 7 7 17 6 6 (x2JCols 286 (0 + d)) (gj286.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok164 : ∀ d < x2KeySize 1 k164, gjCheck 256 1 (x2KeyTypes 1 k164 0) (x2KeyTypes 1 k164 1) (x2KeyTypes 1 k164 2) (x2KeyMult 1 k164 0) (x2KeyMult 1 k164 1) (x2KeyMult 1 k164 2) (x2JCols (x2KeyGlobal 1 k164) d) (gj286.getD d 0) = true := by
  have hr : x2KeySize 1 k164 = 59 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 6 7 7 17 6 6 (x2JCols 286 d) (gj286.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 6 7 7 17 6 6 (x2JCols 286 d) (gj286.getD d 0)) 0 59 gjc164_0 d (Nat.zero_le d) (by omega)
x2_v_cols v286 gj286 286 256 612
theorem vc164_0 : (List.range 40).all (fun c => vCheck 256 612 59 gj286 (x2Trial_286.getD (0 + c) 0) (v286.getD (0 + c) 0)) = true := by decide +kernel
theorem vok164 : ∀ c < 40, vCheck 256 (x2KeyMult 1 k164 0 * x2KeyMult 1 k164 1 * x2KeyMult 1 k164 2) (x2KeySize 1 k164) gj286 (x2Trial_286.getD c 0) (v286.getD c 0) = true := by
  intro c hc
  show vCheck 256 612 59 gj286 (x2Trial_286.getD c 0) (v286.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 612 59 gj286 (x2Trial_286.getD c 0) (v286.getD c 0)) 0 40 vc164_0 c (Nat.zero_le c) (by omega)
theorem small164 : x2KeyDegree 1 k164 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k164 0 ∧ 1 ≤ x2KeyMult 1 k164 1 ∧ 1 ≤ x2KeyMult 1 k164 2 ∧ glRowOK 1 (x2KeyTypes 1 k164 0) (x2KeyMult 1 k164 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k164 1) (x2KeyMult 1 k164 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k164 2) (x2KeyMult 1 k164 2) 512 = true ∧ gj286.length = x2KeySize 1 k164 ∧ x2KeySize 1 k164 ≤ 512 ∧ v286.length = 40 := by decide +kernel
theorem chk164 : trialKeyChk 1 k164 40 gj286 x2Trial_286 v286 :=
  trialKeyChk_intro 1 k164 40 gj286 x2Trial_286 v286 small164 gjok164 vok164
def k165 : x2Key 1 := ⟨165, by decide⟩
x2_gj_cols gj287 287 1 6 7 7 256
theorem gjc165_0 : (List.range 43).all (fun d => gjCheck 256 1 6 7 7 17 6 6 (x2JCols 287 (0 + d)) (gj287.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok165 : ∀ d < x2KeySize 1 k165, gjCheck 256 1 (x2KeyTypes 1 k165 0) (x2KeyTypes 1 k165 1) (x2KeyTypes 1 k165 2) (x2KeyMult 1 k165 0) (x2KeyMult 1 k165 1) (x2KeyMult 1 k165 2) (x2JCols (x2KeyGlobal 1 k165) d) (gj287.getD d 0) = true := by
  have hr : x2KeySize 1 k165 = 43 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 6 7 7 17 6 6 (x2JCols 287 d) (gj287.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 6 7 7 17 6 6 (x2JCols 287 d) (gj287.getD d 0)) 0 43 gjc165_0 d (Nat.zero_le d) (by omega)
x2_v_cols v287 gj287 287 256 612
theorem vc165_0 : (List.range 29).all (fun c => vCheck 256 612 43 gj287 (x2Trial_287.getD (0 + c) 0) (v287.getD (0 + c) 0)) = true := by decide +kernel
theorem vok165 : ∀ c < 29, vCheck 256 (x2KeyMult 1 k165 0 * x2KeyMult 1 k165 1 * x2KeyMult 1 k165 2) (x2KeySize 1 k165) gj287 (x2Trial_287.getD c 0) (v287.getD c 0) = true := by
  intro c hc
  show vCheck 256 612 43 gj287 (x2Trial_287.getD c 0) (v287.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 612 43 gj287 (x2Trial_287.getD c 0) (v287.getD c 0)) 0 29 vc165_0 c (Nat.zero_le c) (by omega)
theorem small165 : x2KeyDegree 1 k165 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k165 0 ∧ 1 ≤ x2KeyMult 1 k165 1 ∧ 1 ≤ x2KeyMult 1 k165 2 ∧ glRowOK 1 (x2KeyTypes 1 k165 0) (x2KeyMult 1 k165 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k165 1) (x2KeyMult 1 k165 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k165 2) (x2KeyMult 1 k165 2) 512 = true ∧ gj287.length = x2KeySize 1 k165 ∧ x2KeySize 1 k165 ≤ 512 ∧ v287.length = 29 := by decide +kernel
theorem chk165 : trialKeyChk 1 k165 29 gj287 x2Trial_287 v287 :=
  trialKeyChk_intro 1 k165 29 gj287 x2Trial_287 v287 small165 gjok165 vok165

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k164, ibFS [(v286, v286, 94810963968000)]), (k165, ibFS [(v287, v287, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![6, 7, 7] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN164 : N k164 = x2TrialForm 1 k164) (hN165 : N k165 = x2TrialForm 1 k165) :
    ∀ e ∈ ks, keyOK (x2Mult 1 6 * x2Mult 1 7 * x2Mult 1 7) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 1 N k164 40 _ gj286 x2Trial_286 v286 (by decide) (by rw [hN164]; exact trialForm_eq 1 k164 40 x2Trial_286 (by decide) rfl) chk164
  · exact keyOK_of_trialChk 1 N k165 29 _ gj287 x2Trial_287 v287 (by decide) (by rw [hN165]; exact trialForm_eq 1 k165 29 x2Trial_287 (by decide) rfl) chk165

end ThreeCopyQutritWerner.X2.InK1x677
