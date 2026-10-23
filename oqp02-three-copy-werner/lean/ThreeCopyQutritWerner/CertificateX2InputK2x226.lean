module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (2, 2, 6) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x226
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k68 : x2Key 2 := ⟨68, by decide⟩
x2_gj_cols gj359 359 2 2 2 6 256
theorem gjc68_0 : (List.range 14).all (fun d => gjCheck 256 2 2 2 6 5 5 11 (x2JCols 359 (0 + d)) (gj359.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok68 : ∀ d < x2KeySize 2 k68, gjCheck 256 2 (x2KeyTypes 2 k68 0) (x2KeyTypes 2 k68 1) (x2KeyTypes 2 k68 2) (x2KeyMult 2 k68 0) (x2KeyMult 2 k68 1) (x2KeyMult 2 k68 2) (x2JCols (x2KeyGlobal 2 k68) d) (gj359.getD d 0) = true := by
  have hr : x2KeySize 2 k68 = 14 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 2 2 6 5 5 11 (x2JCols 359 d) (gj359.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 2 2 6 5 5 11 (x2JCols 359 d) (gj359.getD d 0)) 0 14 gjc68_0 d (Nat.zero_le d) (by omega)
x2_v_cols v359 gj359 359 256 275
theorem vc68_0 : (List.range 14).all (fun c => vCheck 256 275 14 gj359 (x2Trial_359.getD (0 + c) 0) (v359.getD (0 + c) 0)) = true := by decide +kernel
theorem vok68 : ∀ c < 14, vCheck 256 (x2KeyMult 2 k68 0 * x2KeyMult 2 k68 1 * x2KeyMult 2 k68 2) (x2KeySize 2 k68) gj359 (x2Trial_359.getD c 0) (v359.getD c 0) = true := by
  intro c hc
  show vCheck 256 275 14 gj359 (x2Trial_359.getD c 0) (v359.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 275 14 gj359 (x2Trial_359.getD c 0) (v359.getD c 0)) 0 14 vc68_0 c (Nat.zero_le c) (by omega)
theorem small68 : x2KeyDegree 2 k68 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k68 0 ∧ 1 ≤ x2KeyMult 2 k68 1 ∧ 1 ≤ x2KeyMult 2 k68 2 ∧ glRowOK 2 (x2KeyTypes 2 k68 0) (x2KeyMult 2 k68 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k68 1) (x2KeyMult 2 k68 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k68 2) (x2KeyMult 2 k68 2) 512 = true ∧ gj359.length = x2KeySize 2 k68 ∧ x2KeySize 2 k68 ≤ 512 ∧ v359.length = 14 := by decide +kernel
theorem chk68 : trialKeyChk 2 k68 14 gj359 x2Trial_359 v359 :=
  trialKeyChk_intro 2 k68 14 gj359 x2Trial_359 v359 small68 gjok68 vok68
def k69 : x2Key 2 := ⟨69, by decide⟩
x2_gj_cols gj360 360 2 2 2 6 256
theorem gjc69_0 : (List.range 10).all (fun d => gjCheck 256 2 2 2 6 5 5 11 (x2JCols 360 (0 + d)) (gj360.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok69 : ∀ d < x2KeySize 2 k69, gjCheck 256 2 (x2KeyTypes 2 k69 0) (x2KeyTypes 2 k69 1) (x2KeyTypes 2 k69 2) (x2KeyMult 2 k69 0) (x2KeyMult 2 k69 1) (x2KeyMult 2 k69 2) (x2JCols (x2KeyGlobal 2 k69) d) (gj360.getD d 0) = true := by
  have hr : x2KeySize 2 k69 = 10 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 2 2 6 5 5 11 (x2JCols 360 d) (gj360.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 2 2 6 5 5 11 (x2JCols 360 d) (gj360.getD d 0)) 0 10 gjc69_0 d (Nat.zero_le d) (by omega)
x2_v_cols v360 gj360 360 256 275
theorem vc69_0 : (List.range 10).all (fun c => vCheck 256 275 10 gj360 (x2Trial_360.getD (0 + c) 0) (v360.getD (0 + c) 0)) = true := by decide +kernel
theorem vok69 : ∀ c < 10, vCheck 256 (x2KeyMult 2 k69 0 * x2KeyMult 2 k69 1 * x2KeyMult 2 k69 2) (x2KeySize 2 k69) gj360 (x2Trial_360.getD c 0) (v360.getD c 0) = true := by
  intro c hc
  show vCheck 256 275 10 gj360 (x2Trial_360.getD c 0) (v360.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 275 10 gj360 (x2Trial_360.getD c 0) (v360.getD c 0)) 0 10 vc69_0 c (Nat.zero_le c) (by omega)
theorem small69 : x2KeyDegree 2 k69 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k69 0 ∧ 1 ≤ x2KeyMult 2 k69 1 ∧ 1 ≤ x2KeyMult 2 k69 2 ∧ glRowOK 2 (x2KeyTypes 2 k69 0) (x2KeyMult 2 k69 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k69 1) (x2KeyMult 2 k69 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k69 2) (x2KeyMult 2 k69 2) 512 = true ∧ gj360.length = x2KeySize 2 k69 ∧ x2KeySize 2 k69 ≤ 512 ∧ v360.length = 10 := by decide +kernel
theorem chk69 : trialKeyChk 2 k69 10 gj360 x2Trial_360 v360 :=
  trialKeyChk_intro 2 k69 10 gj360 x2Trial_360 v360 small69 gjok69 vok69

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k68, ibFS [(v359, v359, 94810963968000)]), (k69, ibFS [(v360, v360, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![2, 2, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN68 : N k68 = x2TrialForm 2 k68) (hN69 : N k69 = x2TrialForm 2 k69) :
    ∀ e ∈ ks, keyOK (x2Mult 2 2 * x2Mult 2 2 * x2Mult 2 6) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 2 N k68 14 _ gj359 x2Trial_359 v359 (by decide) (by rw [hN68]; exact trialForm_eq 2 k68 14 x2Trial_359 (by decide) rfl) chk68
  · exact keyOK_of_trialChk 2 N k69 10 _ gj360 x2Trial_360 v360 (by decide) (by rw [hN69]; exact trialForm_eq 2 k69 10 x2Trial_360 (by decide) rfl) chk69

end ThreeCopyQutritWerner.X2.InK2x226
