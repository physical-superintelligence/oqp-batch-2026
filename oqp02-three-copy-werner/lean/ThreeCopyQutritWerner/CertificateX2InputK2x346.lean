module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (3, 4, 6) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x346
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k95 : x2Key 2 := ⟨95, by decide⟩
x2_gj_cols gj386 386 2 3 4 6 256
theorem gjc95_0 : (List.range 69).all (fun d => gjCheck 256 2 3 4 6 5 15 11 (x2JCols 386 (0 + d)) (gj386.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok95 : ∀ d < x2KeySize 2 k95, gjCheck 256 2 (x2KeyTypes 2 k95 0) (x2KeyTypes 2 k95 1) (x2KeyTypes 2 k95 2) (x2KeyMult 2 k95 0) (x2KeyMult 2 k95 1) (x2KeyMult 2 k95 2) (x2JCols (x2KeyGlobal 2 k95) d) (gj386.getD d 0) = true := by
  have hr : x2KeySize 2 k95 = 69 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 3 4 6 5 15 11 (x2JCols 386 d) (gj386.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 3 4 6 5 15 11 (x2JCols 386 d) (gj386.getD d 0)) 0 69 gjc95_0 d (Nat.zero_le d) (by omega)
x2_v_cols v386 gj386 386 256 825
theorem vc95_0 : (List.range 63).all (fun c => vCheck 256 825 69 gj386 (x2Trial_386.getD (0 + c) 0) (v386.getD (0 + c) 0)) = true := by decide +kernel
theorem vok95 : ∀ c < 63, vCheck 256 (x2KeyMult 2 k95 0 * x2KeyMult 2 k95 1 * x2KeyMult 2 k95 2) (x2KeySize 2 k95) gj386 (x2Trial_386.getD c 0) (v386.getD c 0) = true := by
  intro c hc
  show vCheck 256 825 69 gj386 (x2Trial_386.getD c 0) (v386.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 825 69 gj386 (x2Trial_386.getD c 0) (v386.getD c 0)) 0 63 vc95_0 c (Nat.zero_le c) (by omega)
theorem small95 : x2KeyDegree 2 k95 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k95 0 ∧ 1 ≤ x2KeyMult 2 k95 1 ∧ 1 ≤ x2KeyMult 2 k95 2 ∧ glRowOK 2 (x2KeyTypes 2 k95 0) (x2KeyMult 2 k95 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k95 1) (x2KeyMult 2 k95 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k95 2) (x2KeyMult 2 k95 2) 512 = true ∧ gj386.length = x2KeySize 2 k95 ∧ x2KeySize 2 k95 ≤ 512 ∧ v386.length = 63 := by decide +kernel
theorem chk95 : trialKeyChk 2 k95 63 gj386 x2Trial_386 v386 :=
  trialKeyChk_intro 2 k95 63 gj386 x2Trial_386 v386 small95 gjok95 vok95

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k95, ibFS [(v386, v386, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![3, 4, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN95 : N k95 = x2TrialForm 2 k95) :
    ∀ e ∈ ks, keyOK (x2Mult 2 3 * x2Mult 2 4 * x2Mult 2 6) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 2 N k95 63 _ gj386 x2Trial_386 v386 (by decide) (by rw [hN95]; exact trialForm_eq 2 k95 63 x2Trial_386 (by decide) rfl) chk95

end ThreeCopyQutritWerner.X2.InK2x346
