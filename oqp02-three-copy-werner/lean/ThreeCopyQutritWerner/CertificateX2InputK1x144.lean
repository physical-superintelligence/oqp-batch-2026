module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (1, 4, 4) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x144
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k60 : x2Key 1 := ⟨60, by decide⟩
x2_gj_cols gj182 182 1 1 4 4 256
theorem gjc60_0 : (List.range 9).all (fun d => gjCheck 256 1 1 4 4 2 7 7 (x2JCols 182 (0 + d)) (gj182.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok60 : ∀ d < x2KeySize 1 k60, gjCheck 256 1 (x2KeyTypes 1 k60 0) (x2KeyTypes 1 k60 1) (x2KeyTypes 1 k60 2) (x2KeyMult 1 k60 0) (x2KeyMult 1 k60 1) (x2KeyMult 1 k60 2) (x2JCols (x2KeyGlobal 1 k60) d) (gj182.getD d 0) = true := by
  have hr : x2KeySize 1 k60 = 9 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 1 4 4 2 7 7 (x2JCols 182 d) (gj182.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 1 4 4 2 7 7 (x2JCols 182 d) (gj182.getD d 0)) 0 9 gjc60_0 d (Nat.zero_le d) (by omega)
x2_v_cols v182 gj182 182 256 98
theorem vc60_0 : (List.range 2).all (fun c => vCheck 256 98 9 gj182 (x2Trial_182.getD (0 + c) 0) (v182.getD (0 + c) 0)) = true := by decide +kernel
theorem vok60 : ∀ c < 2, vCheck 256 (x2KeyMult 1 k60 0 * x2KeyMult 1 k60 1 * x2KeyMult 1 k60 2) (x2KeySize 1 k60) gj182 (x2Trial_182.getD c 0) (v182.getD c 0) = true := by
  intro c hc
  show vCheck 256 98 9 gj182 (x2Trial_182.getD c 0) (v182.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 98 9 gj182 (x2Trial_182.getD c 0) (v182.getD c 0)) 0 2 vc60_0 c (Nat.zero_le c) (by omega)
theorem small60 : x2KeyDegree 1 k60 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k60 0 ∧ 1 ≤ x2KeyMult 1 k60 1 ∧ 1 ≤ x2KeyMult 1 k60 2 ∧ glRowOK 1 (x2KeyTypes 1 k60 0) (x2KeyMult 1 k60 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k60 1) (x2KeyMult 1 k60 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k60 2) (x2KeyMult 1 k60 2) 512 = true ∧ gj182.length = x2KeySize 1 k60 ∧ x2KeySize 1 k60 ≤ 512 ∧ v182.length = 2 := by decide +kernel
theorem chk60 : trialKeyChk 1 k60 2 gj182 x2Trial_182 v182 :=
  trialKeyChk_intro 1 k60 2 gj182 x2Trial_182 v182 small60 gjok60 vok60
def k61 : x2Key 1 := ⟨61, by decide⟩
x2_gj_cols gj183 183 1 1 4 4 256
theorem gjc61_0 : (List.range 7).all (fun d => gjCheck 256 1 1 4 4 2 7 7 (x2JCols 183 (0 + d)) (gj183.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok61 : ∀ d < x2KeySize 1 k61, gjCheck 256 1 (x2KeyTypes 1 k61 0) (x2KeyTypes 1 k61 1) (x2KeyTypes 1 k61 2) (x2KeyMult 1 k61 0) (x2KeyMult 1 k61 1) (x2KeyMult 1 k61 2) (x2JCols (x2KeyGlobal 1 k61) d) (gj183.getD d 0) = true := by
  have hr : x2KeySize 1 k61 = 7 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 1 4 4 2 7 7 (x2JCols 183 d) (gj183.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 1 4 4 2 7 7 (x2JCols 183 d) (gj183.getD d 0)) 0 7 gjc61_0 d (Nat.zero_le d) (by omega)
x2_v_cols v183 gj183 183 256 98
theorem vc61_0 : (List.range 2).all (fun c => vCheck 256 98 7 gj183 (x2Trial_183.getD (0 + c) 0) (v183.getD (0 + c) 0)) = true := by decide +kernel
theorem vok61 : ∀ c < 2, vCheck 256 (x2KeyMult 1 k61 0 * x2KeyMult 1 k61 1 * x2KeyMult 1 k61 2) (x2KeySize 1 k61) gj183 (x2Trial_183.getD c 0) (v183.getD c 0) = true := by
  intro c hc
  show vCheck 256 98 7 gj183 (x2Trial_183.getD c 0) (v183.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 98 7 gj183 (x2Trial_183.getD c 0) (v183.getD c 0)) 0 2 vc61_0 c (Nat.zero_le c) (by omega)
theorem small61 : x2KeyDegree 1 k61 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k61 0 ∧ 1 ≤ x2KeyMult 1 k61 1 ∧ 1 ≤ x2KeyMult 1 k61 2 ∧ glRowOK 1 (x2KeyTypes 1 k61 0) (x2KeyMult 1 k61 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k61 1) (x2KeyMult 1 k61 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k61 2) (x2KeyMult 1 k61 2) 512 = true ∧ gj183.length = x2KeySize 1 k61 ∧ x2KeySize 1 k61 ≤ 512 ∧ v183.length = 2 := by decide +kernel
theorem chk61 : trialKeyChk 1 k61 2 gj183 x2Trial_183 v183 :=
  trialKeyChk_intro 1 k61 2 gj183 x2Trial_183 v183 small61 gjok61 vok61

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k60, ibFS [(v182, v182, 94810963968000)]), (k61, ibFS [(v183, v183, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![1, 4, 4] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN60 : N k60 = x2TrialForm 1 k60) (hN61 : N k61 = x2TrialForm 1 k61) :
    ∀ e ∈ ks, keyOK (x2Mult 1 1 * x2Mult 1 4 * x2Mult 1 4) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 1 N k60 2 _ gj182 x2Trial_182 v182 (by decide) (by rw [hN60]; exact trialForm_eq 1 k60 2 x2Trial_182 (by decide) rfl) chk60
  · exact keyOK_of_trialChk 1 N k61 2 _ gj183 x2Trial_183 v183 (by decide) (by rw [hN61]; exact trialForm_eq 1 k61 2 x2Trial_183 (by decide) rfl) chk61

end ThreeCopyQutritWerner.X2.InK1x144
