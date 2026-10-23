module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (3, 4, 7) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x347
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k119 : x2Key 1 := ⟨119, by decide⟩
x2_gj_cols gj241 241 1 3 4 7 256
theorem gjc119_0 : (List.range 63).all (fun d => gjCheck 256 1 3 4 7 9 7 6 (x2JCols 241 (0 + d)) (gj241.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok119 : ∀ d < x2KeySize 1 k119, gjCheck 256 1 (x2KeyTypes 1 k119 0) (x2KeyTypes 1 k119 1) (x2KeyTypes 1 k119 2) (x2KeyMult 1 k119 0) (x2KeyMult 1 k119 1) (x2KeyMult 1 k119 2) (x2JCols (x2KeyGlobal 1 k119) d) (gj241.getD d 0) = true := by
  have hr : x2KeySize 1 k119 = 63 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 3 4 7 9 7 6 (x2JCols 241 d) (gj241.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 3 4 7 9 7 6 (x2JCols 241 d) (gj241.getD d 0)) 0 63 gjc119_0 d (Nat.zero_le d) (by omega)
x2_v_cols v241 gj241 241 256 378
theorem vc119_0 : (List.range 30).all (fun c => vCheck 256 378 63 gj241 (x2Trial_241.getD (0 + c) 0) (v241.getD (0 + c) 0)) = true := by decide +kernel
theorem vok119 : ∀ c < 30, vCheck 256 (x2KeyMult 1 k119 0 * x2KeyMult 1 k119 1 * x2KeyMult 1 k119 2) (x2KeySize 1 k119) gj241 (x2Trial_241.getD c 0) (v241.getD c 0) = true := by
  intro c hc
  show vCheck 256 378 63 gj241 (x2Trial_241.getD c 0) (v241.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 378 63 gj241 (x2Trial_241.getD c 0) (v241.getD c 0)) 0 30 vc119_0 c (Nat.zero_le c) (by omega)
theorem small119 : x2KeyDegree 1 k119 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k119 0 ∧ 1 ≤ x2KeyMult 1 k119 1 ∧ 1 ≤ x2KeyMult 1 k119 2 ∧ glRowOK 1 (x2KeyTypes 1 k119 0) (x2KeyMult 1 k119 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k119 1) (x2KeyMult 1 k119 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k119 2) (x2KeyMult 1 k119 2) 512 = true ∧ gj241.length = x2KeySize 1 k119 ∧ x2KeySize 1 k119 ≤ 512 ∧ v241.length = 30 := by decide +kernel
theorem chk119 : trialKeyChk 1 k119 30 gj241 x2Trial_241 v241 :=
  trialKeyChk_intro 1 k119 30 gj241 x2Trial_241 v241 small119 gjok119 vok119

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k119, ibFS [(v241, v241, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![3, 4, 7] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN119 : N k119 = x2TrialForm 1 k119) :
    ∀ e ∈ ks, keyOK (x2Mult 1 3 * x2Mult 1 4 * x2Mult 1 7) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k119 30 _ gj241 x2Trial_241 v241 (by decide) (by rw [hN119]; exact trialForm_eq 1 k119 30 x2Trial_241 (by decide) rfl) chk119

end ThreeCopyQutritWerner.X2.InK1x347
