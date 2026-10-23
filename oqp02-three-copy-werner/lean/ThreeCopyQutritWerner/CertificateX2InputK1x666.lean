module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (6, 6, 6) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x666
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k159 : x2Key 1 := ⟨159, by decide⟩
x2_gj_cols gj281 281 1 6 6 6 256
theorem gjc159_0 : (List.range 20).all (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 281 (0 + d)) (gj281.getD (0 + d) 0)) = true := by decide +kernel
theorem gjc159_20 : (List.range 20).all (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 281 (20 + d)) (gj281.getD (20 + d) 0)) = true := by decide +kernel
theorem gjc159_40 : (List.range 20).all (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 281 (40 + d)) (gj281.getD (40 + d) 0)) = true := by decide +kernel
theorem gjc159_60 : (List.range 20).all (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 281 (60 + d)) (gj281.getD (60 + d) 0)) = true := by decide +kernel
theorem gjc159_80 : (List.range 20).all (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 281 (80 + d)) (gj281.getD (80 + d) 0)) = true := by decide +kernel
theorem gjc159_100 : (List.range 20).all (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 281 (100 + d)) (gj281.getD (100 + d) 0)) = true := by decide +kernel
theorem gjc159_120 : (List.range 20).all (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 281 (120 + d)) (gj281.getD (120 + d) 0)) = true := by decide +kernel
theorem gjc159_140 : (List.range 19).all (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 281 (140 + d)) (gj281.getD (140 + d) 0)) = true := by decide +kernel
theorem gjok159 : ∀ d < x2KeySize 1 k159, gjCheck 256 1 (x2KeyTypes 1 k159 0) (x2KeyTypes 1 k159 1) (x2KeyTypes 1 k159 2) (x2KeyMult 1 k159 0) (x2KeyMult 1 k159 1) (x2KeyMult 1 k159 2) (x2JCols (x2KeyGlobal 1 k159) d) (gj281.getD d 0) = true := by
  have hr : x2KeySize 1 k159 = 159 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 6 6 6 17 17 17 (x2JCols 281 d) (gj281.getD d 0) = true
  rcases (by omega : (0 ≤ d ∧ d < 20) ∨ (20 ≤ d ∧ d < 40) ∨ (40 ≤ d ∧ d < 60) ∨ (60 ≤ d ∧ d < 80) ∨ (80 ≤ d ∧ d < 100) ∨ (100 ≤ d ∧ d < 120) ∨ (120 ≤ d ∧ d < 140) ∨ (140 ≤ d ∧ d < 159)) with h | h | h | h | h | h | h | h
  · exact rangeAll_sound (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 281 d) (gj281.getD d 0)) 0 20 gjc159_0 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 281 d) (gj281.getD d 0)) 20 20 gjc159_20 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 281 d) (gj281.getD d 0)) 40 20 gjc159_40 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 281 d) (gj281.getD d 0)) 60 20 gjc159_60 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 281 d) (gj281.getD d 0)) 80 20 gjc159_80 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 281 d) (gj281.getD d 0)) 100 20 gjc159_100 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 281 d) (gj281.getD d 0)) 120 20 gjc159_120 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 281 d) (gj281.getD d 0)) 140 19 gjc159_140 d h.1 (by omega)
x2_v_cols v281 gj281 281 256 4913
theorem vc159_0 : (List.range 10).all (fun c => vCheck 256 4913 159 gj281 (x2Trial_281.getD (0 + c) 0) (v281.getD (0 + c) 0)) = true := by decide +kernel
theorem vc159_10 : (List.range 10).all (fun c => vCheck 256 4913 159 gj281 (x2Trial_281.getD (10 + c) 0) (v281.getD (10 + c) 0)) = true := by decide +kernel
theorem vc159_20 : (List.range 10).all (fun c => vCheck 256 4913 159 gj281 (x2Trial_281.getD (20 + c) 0) (v281.getD (20 + c) 0)) = true := by decide +kernel
theorem vc159_30 : (List.range 10).all (fun c => vCheck 256 4913 159 gj281 (x2Trial_281.getD (30 + c) 0) (v281.getD (30 + c) 0)) = true := by decide +kernel
theorem vc159_40 : (List.range 10).all (fun c => vCheck 256 4913 159 gj281 (x2Trial_281.getD (40 + c) 0) (v281.getD (40 + c) 0)) = true := by decide +kernel
theorem vc159_50 : (List.range 10).all (fun c => vCheck 256 4913 159 gj281 (x2Trial_281.getD (50 + c) 0) (v281.getD (50 + c) 0)) = true := by decide +kernel
theorem vc159_60 : (List.range 10).all (fun c => vCheck 256 4913 159 gj281 (x2Trial_281.getD (60 + c) 0) (v281.getD (60 + c) 0)) = true := by decide +kernel
theorem vc159_70 : (List.range 10).all (fun c => vCheck 256 4913 159 gj281 (x2Trial_281.getD (70 + c) 0) (v281.getD (70 + c) 0)) = true := by decide +kernel
theorem vc159_80 : (List.range 10).all (fun c => vCheck 256 4913 159 gj281 (x2Trial_281.getD (80 + c) 0) (v281.getD (80 + c) 0)) = true := by decide +kernel
theorem vc159_90 : (List.range 10).all (fun c => vCheck 256 4913 159 gj281 (x2Trial_281.getD (90 + c) 0) (v281.getD (90 + c) 0)) = true := by decide +kernel
theorem vc159_100 : (List.range 10).all (fun c => vCheck 256 4913 159 gj281 (x2Trial_281.getD (100 + c) 0) (v281.getD (100 + c) 0)) = true := by decide +kernel
theorem vc159_110 : (List.range 10).all (fun c => vCheck 256 4913 159 gj281 (x2Trial_281.getD (110 + c) 0) (v281.getD (110 + c) 0)) = true := by decide +kernel
theorem vc159_120 : (List.range 2).all (fun c => vCheck 256 4913 159 gj281 (x2Trial_281.getD (120 + c) 0) (v281.getD (120 + c) 0)) = true := by decide +kernel
theorem vok159 : ∀ c < 122, vCheck 256 (x2KeyMult 1 k159 0 * x2KeyMult 1 k159 1 * x2KeyMult 1 k159 2) (x2KeySize 1 k159) gj281 (x2Trial_281.getD c 0) (v281.getD c 0) = true := by
  intro c hc
  show vCheck 256 4913 159 gj281 (x2Trial_281.getD c 0) (v281.getD c 0) = true
  rcases (by omega : (0 ≤ c ∧ c < 10) ∨ (10 ≤ c ∧ c < 20) ∨ (20 ≤ c ∧ c < 30) ∨ (30 ≤ c ∧ c < 40) ∨ (40 ≤ c ∧ c < 50) ∨ (50 ≤ c ∧ c < 60) ∨ (60 ≤ c ∧ c < 70) ∨ (70 ≤ c ∧ c < 80) ∨ (80 ≤ c ∧ c < 90) ∨ (90 ≤ c ∧ c < 100) ∨ (100 ≤ c ∧ c < 110) ∨ (110 ≤ c ∧ c < 120) ∨ (120 ≤ c ∧ c < 122)) with h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (fun c => vCheck 256 4913 159 gj281 (x2Trial_281.getD c 0) (v281.getD c 0)) 0 10 vc159_0 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 159 gj281 (x2Trial_281.getD c 0) (v281.getD c 0)) 10 10 vc159_10 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 159 gj281 (x2Trial_281.getD c 0) (v281.getD c 0)) 20 10 vc159_20 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 159 gj281 (x2Trial_281.getD c 0) (v281.getD c 0)) 30 10 vc159_30 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 159 gj281 (x2Trial_281.getD c 0) (v281.getD c 0)) 40 10 vc159_40 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 159 gj281 (x2Trial_281.getD c 0) (v281.getD c 0)) 50 10 vc159_50 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 159 gj281 (x2Trial_281.getD c 0) (v281.getD c 0)) 60 10 vc159_60 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 159 gj281 (x2Trial_281.getD c 0) (v281.getD c 0)) 70 10 vc159_70 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 159 gj281 (x2Trial_281.getD c 0) (v281.getD c 0)) 80 10 vc159_80 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 159 gj281 (x2Trial_281.getD c 0) (v281.getD c 0)) 90 10 vc159_90 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 159 gj281 (x2Trial_281.getD c 0) (v281.getD c 0)) 100 10 vc159_100 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 159 gj281 (x2Trial_281.getD c 0) (v281.getD c 0)) 110 10 vc159_110 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 159 gj281 (x2Trial_281.getD c 0) (v281.getD c 0)) 120 2 vc159_120 c h.1 (by omega)
theorem small159 : x2KeyDegree 1 k159 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k159 0 ∧ 1 ≤ x2KeyMult 1 k159 1 ∧ 1 ≤ x2KeyMult 1 k159 2 ∧ glRowOK 1 (x2KeyTypes 1 k159 0) (x2KeyMult 1 k159 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k159 1) (x2KeyMult 1 k159 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k159 2) (x2KeyMult 1 k159 2) 512 = true ∧ gj281.length = x2KeySize 1 k159 ∧ x2KeySize 1 k159 ≤ 512 ∧ v281.length = 122 := by decide +kernel
theorem chk159 : trialKeyChk 1 k159 122 gj281 x2Trial_281 v281 :=
  trialKeyChk_intro 1 k159 122 gj281 x2Trial_281 v281 small159 gjok159 vok159
def k160 : x2Key 1 := ⟨160, by decide⟩
x2_gj_cols gj282 282 1 6 6 6 256
theorem gjc160_0 : (List.range 20).all (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 282 (0 + d)) (gj282.getD (0 + d) 0)) = true := by decide +kernel
theorem gjc160_20 : (List.range 20).all (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 282 (20 + d)) (gj282.getD (20 + d) 0)) = true := by decide +kernel
theorem gjc160_40 : (List.range 20).all (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 282 (40 + d)) (gj282.getD (40 + d) 0)) = true := by decide +kernel
theorem gjc160_60 : (List.range 20).all (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 282 (60 + d)) (gj282.getD (60 + d) 0)) = true := by decide +kernel
theorem gjc160_80 : (List.range 20).all (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 282 (80 + d)) (gj282.getD (80 + d) 0)) = true := by decide +kernel
theorem gjc160_100 : (List.range 14).all (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 282 (100 + d)) (gj282.getD (100 + d) 0)) = true := by decide +kernel
theorem gjok160 : ∀ d < x2KeySize 1 k160, gjCheck 256 1 (x2KeyTypes 1 k160 0) (x2KeyTypes 1 k160 1) (x2KeyTypes 1 k160 2) (x2KeyMult 1 k160 0) (x2KeyMult 1 k160 1) (x2KeyMult 1 k160 2) (x2JCols (x2KeyGlobal 1 k160) d) (gj282.getD d 0) = true := by
  have hr : x2KeySize 1 k160 = 114 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 6 6 6 17 17 17 (x2JCols 282 d) (gj282.getD d 0) = true
  rcases (by omega : (0 ≤ d ∧ d < 20) ∨ (20 ≤ d ∧ d < 40) ∨ (40 ≤ d ∧ d < 60) ∨ (60 ≤ d ∧ d < 80) ∨ (80 ≤ d ∧ d < 100) ∨ (100 ≤ d ∧ d < 114)) with h | h | h | h | h | h
  · exact rangeAll_sound (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 282 d) (gj282.getD d 0)) 0 20 gjc160_0 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 282 d) (gj282.getD d 0)) 20 20 gjc160_20 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 282 d) (gj282.getD d 0)) 40 20 gjc160_40 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 282 d) (gj282.getD d 0)) 60 20 gjc160_60 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 282 d) (gj282.getD d 0)) 80 20 gjc160_80 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 282 d) (gj282.getD d 0)) 100 14 gjc160_100 d h.1 (by omega)
x2_v_cols v282 gj282 282 256 4913
theorem vc160_0 : (List.range 13).all (fun c => vCheck 256 4913 114 gj282 (x2Trial_282.getD (0 + c) 0) (v282.getD (0 + c) 0)) = true := by decide +kernel
theorem vc160_13 : (List.range 13).all (fun c => vCheck 256 4913 114 gj282 (x2Trial_282.getD (13 + c) 0) (v282.getD (13 + c) 0)) = true := by decide +kernel
theorem vc160_26 : (List.range 13).all (fun c => vCheck 256 4913 114 gj282 (x2Trial_282.getD (26 + c) 0) (v282.getD (26 + c) 0)) = true := by decide +kernel
theorem vc160_39 : (List.range 13).all (fun c => vCheck 256 4913 114 gj282 (x2Trial_282.getD (39 + c) 0) (v282.getD (39 + c) 0)) = true := by decide +kernel
theorem vc160_52 : (List.range 13).all (fun c => vCheck 256 4913 114 gj282 (x2Trial_282.getD (52 + c) 0) (v282.getD (52 + c) 0)) = true := by decide +kernel
theorem vc160_65 : (List.range 13).all (fun c => vCheck 256 4913 114 gj282 (x2Trial_282.getD (65 + c) 0) (v282.getD (65 + c) 0)) = true := by decide +kernel
theorem vc160_78 : (List.range 13).all (fun c => vCheck 256 4913 114 gj282 (x2Trial_282.getD (78 + c) 0) (v282.getD (78 + c) 0)) = true := by decide +kernel
theorem vok160 : ∀ c < 91, vCheck 256 (x2KeyMult 1 k160 0 * x2KeyMult 1 k160 1 * x2KeyMult 1 k160 2) (x2KeySize 1 k160) gj282 (x2Trial_282.getD c 0) (v282.getD c 0) = true := by
  intro c hc
  show vCheck 256 4913 114 gj282 (x2Trial_282.getD c 0) (v282.getD c 0) = true
  rcases (by omega : (0 ≤ c ∧ c < 13) ∨ (13 ≤ c ∧ c < 26) ∨ (26 ≤ c ∧ c < 39) ∨ (39 ≤ c ∧ c < 52) ∨ (52 ≤ c ∧ c < 65) ∨ (65 ≤ c ∧ c < 78) ∨ (78 ≤ c ∧ c < 91)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (fun c => vCheck 256 4913 114 gj282 (x2Trial_282.getD c 0) (v282.getD c 0)) 0 13 vc160_0 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 114 gj282 (x2Trial_282.getD c 0) (v282.getD c 0)) 13 13 vc160_13 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 114 gj282 (x2Trial_282.getD c 0) (v282.getD c 0)) 26 13 vc160_26 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 114 gj282 (x2Trial_282.getD c 0) (v282.getD c 0)) 39 13 vc160_39 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 114 gj282 (x2Trial_282.getD c 0) (v282.getD c 0)) 52 13 vc160_52 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 114 gj282 (x2Trial_282.getD c 0) (v282.getD c 0)) 65 13 vc160_65 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 114 gj282 (x2Trial_282.getD c 0) (v282.getD c 0)) 78 13 vc160_78 c h.1 (by omega)
theorem small160 : x2KeyDegree 1 k160 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k160 0 ∧ 1 ≤ x2KeyMult 1 k160 1 ∧ 1 ≤ x2KeyMult 1 k160 2 ∧ glRowOK 1 (x2KeyTypes 1 k160 0) (x2KeyMult 1 k160 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k160 1) (x2KeyMult 1 k160 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k160 2) (x2KeyMult 1 k160 2) 512 = true ∧ gj282.length = x2KeySize 1 k160 ∧ x2KeySize 1 k160 ≤ 512 ∧ v282.length = 91 := by decide +kernel
theorem chk160 : trialKeyChk 1 k160 91 gj282 x2Trial_282 v282 :=
  trialKeyChk_intro 1 k160 91 gj282 x2Trial_282 v282 small160 gjok160 vok160
def k161 : x2Key 1 := ⟨161, by decide⟩
x2_gj_cols gj283 283 1 6 6 6 256
theorem gjc161_0 : (List.range 20).all (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 283 (0 + d)) (gj283.getD (0 + d) 0)) = true := by decide +kernel
theorem gjc161_20 : (List.range 20).all (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 283 (20 + d)) (gj283.getD (20 + d) 0)) = true := by decide +kernel
theorem gjc161_40 : (List.range 20).all (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 283 (40 + d)) (gj283.getD (40 + d) 0)) = true := by decide +kernel
theorem gjc161_60 : (List.range 20).all (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 283 (60 + d)) (gj283.getD (60 + d) 0)) = true := by decide +kernel
theorem gjc161_80 : (List.range 20).all (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 283 (80 + d)) (gj283.getD (80 + d) 0)) = true := by decide +kernel
theorem gjc161_100 : (List.range 20).all (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 283 (100 + d)) (gj283.getD (100 + d) 0)) = true := by decide +kernel
theorem gjc161_120 : (List.range 20).all (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 283 (120 + d)) (gj283.getD (120 + d) 0)) = true := by decide +kernel
theorem gjc161_140 : (List.range 20).all (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 283 (140 + d)) (gj283.getD (140 + d) 0)) = true := by decide +kernel
theorem gjc161_160 : (List.range 20).all (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 283 (160 + d)) (gj283.getD (160 + d) 0)) = true := by decide +kernel
theorem gjc161_180 : (List.range 20).all (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 283 (180 + d)) (gj283.getD (180 + d) 0)) = true := by decide +kernel
theorem gjc161_200 : (List.range 20).all (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 283 (200 + d)) (gj283.getD (200 + d) 0)) = true := by decide +kernel
theorem gjc161_220 : (List.range 20).all (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 283 (220 + d)) (gj283.getD (220 + d) 0)) = true := by decide +kernel
theorem gjc161_240 : (List.range 20).all (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 283 (240 + d)) (gj283.getD (240 + d) 0)) = true := by decide +kernel
theorem gjc161_260 : (List.range 13).all (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 283 (260 + d)) (gj283.getD (260 + d) 0)) = true := by decide +kernel
theorem gjok161 : ∀ d < x2KeySize 1 k161, gjCheck 256 1 (x2KeyTypes 1 k161 0) (x2KeyTypes 1 k161 1) (x2KeyTypes 1 k161 2) (x2KeyMult 1 k161 0) (x2KeyMult 1 k161 1) (x2KeyMult 1 k161 2) (x2JCols (x2KeyGlobal 1 k161) d) (gj283.getD d 0) = true := by
  have hr : x2KeySize 1 k161 = 273 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 6 6 6 17 17 17 (x2JCols 283 d) (gj283.getD d 0) = true
  rcases (by omega : (0 ≤ d ∧ d < 20) ∨ (20 ≤ d ∧ d < 40) ∨ (40 ≤ d ∧ d < 60) ∨ (60 ≤ d ∧ d < 80) ∨ (80 ≤ d ∧ d < 100) ∨ (100 ≤ d ∧ d < 120) ∨ (120 ≤ d ∧ d < 140) ∨ (140 ≤ d ∧ d < 160) ∨ (160 ≤ d ∧ d < 180) ∨ (180 ≤ d ∧ d < 200) ∨ (200 ≤ d ∧ d < 220) ∨ (220 ≤ d ∧ d < 240) ∨ (240 ≤ d ∧ d < 260) ∨ (260 ≤ d ∧ d < 273)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 283 d) (gj283.getD d 0)) 0 20 gjc161_0 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 283 d) (gj283.getD d 0)) 20 20 gjc161_20 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 283 d) (gj283.getD d 0)) 40 20 gjc161_40 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 283 d) (gj283.getD d 0)) 60 20 gjc161_60 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 283 d) (gj283.getD d 0)) 80 20 gjc161_80 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 283 d) (gj283.getD d 0)) 100 20 gjc161_100 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 283 d) (gj283.getD d 0)) 120 20 gjc161_120 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 283 d) (gj283.getD d 0)) 140 20 gjc161_140 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 283 d) (gj283.getD d 0)) 160 20 gjc161_160 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 283 d) (gj283.getD d 0)) 180 20 gjc161_180 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 283 d) (gj283.getD d 0)) 200 20 gjc161_200 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 283 d) (gj283.getD d 0)) 220 20 gjc161_220 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 283 d) (gj283.getD d 0)) 240 20 gjc161_240 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 6 6 6 17 17 17 (x2JCols 283 d) (gj283.getD d 0)) 260 13 gjc161_260 d h.1 (by omega)
x2_v_cols v283 gj283 283 256 4913
theorem vc161_0 : (List.range 5).all (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD (0 + c) 0) (v283.getD (0 + c) 0)) = true := by decide +kernel
theorem vc161_5 : (List.range 5).all (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD (5 + c) 0) (v283.getD (5 + c) 0)) = true := by decide +kernel
theorem vc161_10 : (List.range 5).all (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD (10 + c) 0) (v283.getD (10 + c) 0)) = true := by decide +kernel
theorem vc161_15 : (List.range 5).all (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD (15 + c) 0) (v283.getD (15 + c) 0)) = true := by decide +kernel
theorem vc161_20 : (List.range 5).all (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD (20 + c) 0) (v283.getD (20 + c) 0)) = true := by decide +kernel
theorem vc161_25 : (List.range 5).all (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD (25 + c) 0) (v283.getD (25 + c) 0)) = true := by decide +kernel
theorem vc161_30 : (List.range 5).all (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD (30 + c) 0) (v283.getD (30 + c) 0)) = true := by decide +kernel
theorem vc161_35 : (List.range 5).all (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD (35 + c) 0) (v283.getD (35 + c) 0)) = true := by decide +kernel
theorem vc161_40 : (List.range 5).all (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD (40 + c) 0) (v283.getD (40 + c) 0)) = true := by decide +kernel
theorem vc161_45 : (List.range 5).all (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD (45 + c) 0) (v283.getD (45 + c) 0)) = true := by decide +kernel
theorem vc161_50 : (List.range 5).all (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD (50 + c) 0) (v283.getD (50 + c) 0)) = true := by decide +kernel
theorem vc161_55 : (List.range 5).all (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD (55 + c) 0) (v283.getD (55 + c) 0)) = true := by decide +kernel
theorem vc161_60 : (List.range 5).all (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD (60 + c) 0) (v283.getD (60 + c) 0)) = true := by decide +kernel
theorem vc161_65 : (List.range 5).all (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD (65 + c) 0) (v283.getD (65 + c) 0)) = true := by decide +kernel
theorem vc161_70 : (List.range 5).all (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD (70 + c) 0) (v283.getD (70 + c) 0)) = true := by decide +kernel
theorem vc161_75 : (List.range 5).all (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD (75 + c) 0) (v283.getD (75 + c) 0)) = true := by decide +kernel
theorem vc161_80 : (List.range 5).all (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD (80 + c) 0) (v283.getD (80 + c) 0)) = true := by decide +kernel
theorem vc161_85 : (List.range 5).all (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD (85 + c) 0) (v283.getD (85 + c) 0)) = true := by decide +kernel
theorem vc161_90 : (List.range 5).all (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD (90 + c) 0) (v283.getD (90 + c) 0)) = true := by decide +kernel
theorem vc161_95 : (List.range 5).all (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD (95 + c) 0) (v283.getD (95 + c) 0)) = true := by decide +kernel
theorem vc161_100 : (List.range 5).all (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD (100 + c) 0) (v283.getD (100 + c) 0)) = true := by decide +kernel
theorem vc161_105 : (List.range 5).all (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD (105 + c) 0) (v283.getD (105 + c) 0)) = true := by decide +kernel
theorem vc161_110 : (List.range 5).all (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD (110 + c) 0) (v283.getD (110 + c) 0)) = true := by decide +kernel
theorem vc161_115 : (List.range 5).all (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD (115 + c) 0) (v283.getD (115 + c) 0)) = true := by decide +kernel
theorem vc161_120 : (List.range 5).all (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD (120 + c) 0) (v283.getD (120 + c) 0)) = true := by decide +kernel
theorem vc161_125 : (List.range 5).all (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD (125 + c) 0) (v283.getD (125 + c) 0)) = true := by decide +kernel
theorem vc161_130 : (List.range 5).all (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD (130 + c) 0) (v283.getD (130 + c) 0)) = true := by decide +kernel
theorem vc161_135 : (List.range 5).all (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD (135 + c) 0) (v283.getD (135 + c) 0)) = true := by decide +kernel
theorem vc161_140 : (List.range 5).all (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD (140 + c) 0) (v283.getD (140 + c) 0)) = true := by decide +kernel
theorem vc161_145 : (List.range 5).all (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD (145 + c) 0) (v283.getD (145 + c) 0)) = true := by decide +kernel
theorem vc161_150 : (List.range 5).all (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD (150 + c) 0) (v283.getD (150 + c) 0)) = true := by decide +kernel
theorem vc161_155 : (List.range 5).all (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD (155 + c) 0) (v283.getD (155 + c) 0)) = true := by decide +kernel
theorem vc161_160 : (List.range 5).all (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD (160 + c) 0) (v283.getD (160 + c) 0)) = true := by decide +kernel
theorem vc161_165 : (List.range 5).all (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD (165 + c) 0) (v283.getD (165 + c) 0)) = true := by decide +kernel
theorem vc161_170 : (List.range 5).all (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD (170 + c) 0) (v283.getD (170 + c) 0)) = true := by decide +kernel
theorem vc161_175 : (List.range 5).all (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD (175 + c) 0) (v283.getD (175 + c) 0)) = true := by decide +kernel
theorem vc161_180 : (List.range 5).all (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD (180 + c) 0) (v283.getD (180 + c) 0)) = true := by decide +kernel
theorem vc161_185 : (List.range 5).all (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD (185 + c) 0) (v283.getD (185 + c) 0)) = true := by decide +kernel
theorem vc161_190 : (List.range 5).all (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD (190 + c) 0) (v283.getD (190 + c) 0)) = true := by decide +kernel
theorem vc161_195 : (List.range 5).all (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD (195 + c) 0) (v283.getD (195 + c) 0)) = true := by decide +kernel
theorem vc161_200 : (List.range 5).all (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD (200 + c) 0) (v283.getD (200 + c) 0)) = true := by decide +kernel
theorem vc161_205 : (List.range 5).all (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD (205 + c) 0) (v283.getD (205 + c) 0)) = true := by decide +kernel
theorem vc161_210 : (List.range 2).all (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD (210 + c) 0) (v283.getD (210 + c) 0)) = true := by decide +kernel
theorem vok161 : ∀ c < 212, vCheck 256 (x2KeyMult 1 k161 0 * x2KeyMult 1 k161 1 * x2KeyMult 1 k161 2) (x2KeySize 1 k161) gj283 (x2Trial_283.getD c 0) (v283.getD c 0) = true := by
  intro c hc
  show vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0) = true
  rcases (by omega : (0 ≤ c ∧ c < 5) ∨ (5 ≤ c ∧ c < 10) ∨ (10 ≤ c ∧ c < 15) ∨ (15 ≤ c ∧ c < 20) ∨ (20 ≤ c ∧ c < 25) ∨ (25 ≤ c ∧ c < 30) ∨ (30 ≤ c ∧ c < 35) ∨ (35 ≤ c ∧ c < 40) ∨ (40 ≤ c ∧ c < 45) ∨ (45 ≤ c ∧ c < 50) ∨ (50 ≤ c ∧ c < 55) ∨ (55 ≤ c ∧ c < 60) ∨ (60 ≤ c ∧ c < 65) ∨ (65 ≤ c ∧ c < 70) ∨ (70 ≤ c ∧ c < 75) ∨ (75 ≤ c ∧ c < 80) ∨ (80 ≤ c ∧ c < 85) ∨ (85 ≤ c ∧ c < 90) ∨ (90 ≤ c ∧ c < 95) ∨ (95 ≤ c ∧ c < 100) ∨ (100 ≤ c ∧ c < 105) ∨ (105 ≤ c ∧ c < 110) ∨ (110 ≤ c ∧ c < 115) ∨ (115 ≤ c ∧ c < 120) ∨ (120 ≤ c ∧ c < 125) ∨ (125 ≤ c ∧ c < 130) ∨ (130 ≤ c ∧ c < 135) ∨ (135 ≤ c ∧ c < 140) ∨ (140 ≤ c ∧ c < 145) ∨ (145 ≤ c ∧ c < 150) ∨ (150 ≤ c ∧ c < 155) ∨ (155 ≤ c ∧ c < 160) ∨ (160 ≤ c ∧ c < 165) ∨ (165 ≤ c ∧ c < 170) ∨ (170 ≤ c ∧ c < 175) ∨ (175 ≤ c ∧ c < 180) ∨ (180 ≤ c ∧ c < 185) ∨ (185 ≤ c ∧ c < 190) ∨ (190 ≤ c ∧ c < 195) ∨ (195 ≤ c ∧ c < 200) ∨ (200 ≤ c ∧ c < 205) ∨ (205 ≤ c ∧ c < 210) ∨ (210 ≤ c ∧ c < 212)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0)) 0 5 vc161_0 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0)) 5 5 vc161_5 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0)) 10 5 vc161_10 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0)) 15 5 vc161_15 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0)) 20 5 vc161_20 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0)) 25 5 vc161_25 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0)) 30 5 vc161_30 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0)) 35 5 vc161_35 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0)) 40 5 vc161_40 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0)) 45 5 vc161_45 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0)) 50 5 vc161_50 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0)) 55 5 vc161_55 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0)) 60 5 vc161_60 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0)) 65 5 vc161_65 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0)) 70 5 vc161_70 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0)) 75 5 vc161_75 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0)) 80 5 vc161_80 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0)) 85 5 vc161_85 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0)) 90 5 vc161_90 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0)) 95 5 vc161_95 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0)) 100 5 vc161_100 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0)) 105 5 vc161_105 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0)) 110 5 vc161_110 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0)) 115 5 vc161_115 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0)) 120 5 vc161_120 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0)) 125 5 vc161_125 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0)) 130 5 vc161_130 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0)) 135 5 vc161_135 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0)) 140 5 vc161_140 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0)) 145 5 vc161_145 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0)) 150 5 vc161_150 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0)) 155 5 vc161_155 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0)) 160 5 vc161_160 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0)) 165 5 vc161_165 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0)) 170 5 vc161_170 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0)) 175 5 vc161_175 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0)) 180 5 vc161_180 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0)) 185 5 vc161_185 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0)) 190 5 vc161_190 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0)) 195 5 vc161_195 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0)) 200 5 vc161_200 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0)) 205 5 vc161_205 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 4913 273 gj283 (x2Trial_283.getD c 0) (v283.getD c 0)) 210 2 vc161_210 c h.1 (by omega)
x2_p_cols p283 v283 17
theorem pok161_0 : partnerCheck 17 (v283.getD 0 0) (p283.getD 0 0) = true := by decide +kernel
theorem pok161_1 : partnerCheck 17 (v283.getD 1 0) (p283.getD 1 0) = true := by decide +kernel
theorem pok161_2 : partnerCheck 17 (v283.getD 2 0) (p283.getD 2 0) = true := by decide +kernel
theorem pok161_3 : partnerCheck 17 (v283.getD 3 0) (p283.getD 3 0) = true := by decide +kernel
theorem pok161_4 : partnerCheck 17 (v283.getD 4 0) (p283.getD 4 0) = true := by decide +kernel
theorem pok161_5 : partnerCheck 17 (v283.getD 5 0) (p283.getD 5 0) = true := by decide +kernel
theorem pok161_6 : partnerCheck 17 (v283.getD 6 0) (p283.getD 6 0) = true := by decide +kernel
theorem pok161_7 : partnerCheck 17 (v283.getD 7 0) (p283.getD 7 0) = true := by decide +kernel
theorem pok161_8 : partnerCheck 17 (v283.getD 8 0) (p283.getD 8 0) = true := by decide +kernel
theorem pok161_9 : partnerCheck 17 (v283.getD 9 0) (p283.getD 9 0) = true := by decide +kernel
theorem pok161_10 : partnerCheck 17 (v283.getD 10 0) (p283.getD 10 0) = true := by decide +kernel
theorem pok161_11 : partnerCheck 17 (v283.getD 11 0) (p283.getD 11 0) = true := by decide +kernel
theorem pok161_12 : partnerCheck 17 (v283.getD 12 0) (p283.getD 12 0) = true := by decide +kernel
theorem pok161_13 : partnerCheck 17 (v283.getD 13 0) (p283.getD 13 0) = true := by decide +kernel
theorem pok161_14 : partnerCheck 17 (v283.getD 14 0) (p283.getD 14 0) = true := by decide +kernel
theorem pok161_15 : partnerCheck 17 (v283.getD 15 0) (p283.getD 15 0) = true := by decide +kernel
theorem pok161_16 : partnerCheck 17 (v283.getD 16 0) (p283.getD 16 0) = true := by decide +kernel
theorem pok161_17 : partnerCheck 17 (v283.getD 17 0) (p283.getD 17 0) = true := by decide +kernel
theorem pok161_18 : partnerCheck 17 (v283.getD 18 0) (p283.getD 18 0) = true := by decide +kernel
theorem pok161_19 : partnerCheck 17 (v283.getD 19 0) (p283.getD 19 0) = true := by decide +kernel
theorem pok161_20 : partnerCheck 17 (v283.getD 20 0) (p283.getD 20 0) = true := by decide +kernel
theorem pok161_21 : partnerCheck 17 (v283.getD 21 0) (p283.getD 21 0) = true := by decide +kernel
theorem pok161_22 : partnerCheck 17 (v283.getD 22 0) (p283.getD 22 0) = true := by decide +kernel
theorem pok161_23 : partnerCheck 17 (v283.getD 23 0) (p283.getD 23 0) = true := by decide +kernel
theorem pok161_24 : partnerCheck 17 (v283.getD 24 0) (p283.getD 24 0) = true := by decide +kernel
theorem pok161_25 : partnerCheck 17 (v283.getD 25 0) (p283.getD 25 0) = true := by decide +kernel
theorem pok161_26 : partnerCheck 17 (v283.getD 26 0) (p283.getD 26 0) = true := by decide +kernel
theorem pok161_27 : partnerCheck 17 (v283.getD 27 0) (p283.getD 27 0) = true := by decide +kernel
theorem pok161_28 : partnerCheck 17 (v283.getD 28 0) (p283.getD 28 0) = true := by decide +kernel
theorem pok161_29 : partnerCheck 17 (v283.getD 29 0) (p283.getD 29 0) = true := by decide +kernel
theorem pok161_30 : partnerCheck 17 (v283.getD 30 0) (p283.getD 30 0) = true := by decide +kernel
theorem pok161_31 : partnerCheck 17 (v283.getD 31 0) (p283.getD 31 0) = true := by decide +kernel
theorem pok161_32 : partnerCheck 17 (v283.getD 32 0) (p283.getD 32 0) = true := by decide +kernel
theorem pok161_33 : partnerCheck 17 (v283.getD 33 0) (p283.getD 33 0) = true := by decide +kernel
theorem pok161_34 : partnerCheck 17 (v283.getD 34 0) (p283.getD 34 0) = true := by decide +kernel
theorem pok161_35 : partnerCheck 17 (v283.getD 35 0) (p283.getD 35 0) = true := by decide +kernel
theorem pok161_36 : partnerCheck 17 (v283.getD 36 0) (p283.getD 36 0) = true := by decide +kernel
theorem pok161_37 : partnerCheck 17 (v283.getD 37 0) (p283.getD 37 0) = true := by decide +kernel
theorem pok161_38 : partnerCheck 17 (v283.getD 38 0) (p283.getD 38 0) = true := by decide +kernel
theorem pok161_39 : partnerCheck 17 (v283.getD 39 0) (p283.getD 39 0) = true := by decide +kernel
theorem pok161_40 : partnerCheck 17 (v283.getD 40 0) (p283.getD 40 0) = true := by decide +kernel
theorem pok161_41 : partnerCheck 17 (v283.getD 41 0) (p283.getD 41 0) = true := by decide +kernel
theorem pok161_42 : partnerCheck 17 (v283.getD 42 0) (p283.getD 42 0) = true := by decide +kernel
theorem pok161_43 : partnerCheck 17 (v283.getD 43 0) (p283.getD 43 0) = true := by decide +kernel
theorem pok161_44 : partnerCheck 17 (v283.getD 44 0) (p283.getD 44 0) = true := by decide +kernel
theorem pok161_45 : partnerCheck 17 (v283.getD 45 0) (p283.getD 45 0) = true := by decide +kernel
theorem pok161_46 : partnerCheck 17 (v283.getD 46 0) (p283.getD 46 0) = true := by decide +kernel
theorem pok161_47 : partnerCheck 17 (v283.getD 47 0) (p283.getD 47 0) = true := by decide +kernel
theorem pok161_48 : partnerCheck 17 (v283.getD 48 0) (p283.getD 48 0) = true := by decide +kernel
theorem pok161_49 : partnerCheck 17 (v283.getD 49 0) (p283.getD 49 0) = true := by decide +kernel
theorem pok161_50 : partnerCheck 17 (v283.getD 50 0) (p283.getD 50 0) = true := by decide +kernel
theorem pok161_51 : partnerCheck 17 (v283.getD 51 0) (p283.getD 51 0) = true := by decide +kernel
theorem pok161_52 : partnerCheck 17 (v283.getD 52 0) (p283.getD 52 0) = true := by decide +kernel
theorem pok161_53 : partnerCheck 17 (v283.getD 53 0) (p283.getD 53 0) = true := by decide +kernel
theorem pok161_54 : partnerCheck 17 (v283.getD 54 0) (p283.getD 54 0) = true := by decide +kernel
theorem pok161_55 : partnerCheck 17 (v283.getD 55 0) (p283.getD 55 0) = true := by decide +kernel
theorem pok161_56 : partnerCheck 17 (v283.getD 56 0) (p283.getD 56 0) = true := by decide +kernel
theorem pok161_57 : partnerCheck 17 (v283.getD 57 0) (p283.getD 57 0) = true := by decide +kernel
theorem pok161_58 : partnerCheck 17 (v283.getD 58 0) (p283.getD 58 0) = true := by decide +kernel
theorem pok161_59 : partnerCheck 17 (v283.getD 59 0) (p283.getD 59 0) = true := by decide +kernel
theorem pok161_60 : partnerCheck 17 (v283.getD 60 0) (p283.getD 60 0) = true := by decide +kernel
theorem pok161_61 : partnerCheck 17 (v283.getD 61 0) (p283.getD 61 0) = true := by decide +kernel
theorem pok161_62 : partnerCheck 17 (v283.getD 62 0) (p283.getD 62 0) = true := by decide +kernel
theorem pok161_63 : partnerCheck 17 (v283.getD 63 0) (p283.getD 63 0) = true := by decide +kernel
theorem pok161_64 : partnerCheck 17 (v283.getD 64 0) (p283.getD 64 0) = true := by decide +kernel
theorem pok161_65 : partnerCheck 17 (v283.getD 65 0) (p283.getD 65 0) = true := by decide +kernel
theorem pok161_66 : partnerCheck 17 (v283.getD 66 0) (p283.getD 66 0) = true := by decide +kernel
theorem pok161_67 : partnerCheck 17 (v283.getD 67 0) (p283.getD 67 0) = true := by decide +kernel
theorem pok161_68 : partnerCheck 17 (v283.getD 68 0) (p283.getD 68 0) = true := by decide +kernel
theorem pok161_69 : partnerCheck 17 (v283.getD 69 0) (p283.getD 69 0) = true := by decide +kernel
theorem pok161_70 : partnerCheck 17 (v283.getD 70 0) (p283.getD 70 0) = true := by decide +kernel
theorem pok161_71 : partnerCheck 17 (v283.getD 71 0) (p283.getD 71 0) = true := by decide +kernel
theorem pok161_72 : partnerCheck 17 (v283.getD 72 0) (p283.getD 72 0) = true := by decide +kernel
theorem pok161_73 : partnerCheck 17 (v283.getD 73 0) (p283.getD 73 0) = true := by decide +kernel
theorem pok161_74 : partnerCheck 17 (v283.getD 74 0) (p283.getD 74 0) = true := by decide +kernel
theorem pok161_75 : partnerCheck 17 (v283.getD 75 0) (p283.getD 75 0) = true := by decide +kernel
theorem pok161_76 : partnerCheck 17 (v283.getD 76 0) (p283.getD 76 0) = true := by decide +kernel
theorem pok161_77 : partnerCheck 17 (v283.getD 77 0) (p283.getD 77 0) = true := by decide +kernel
theorem pok161_78 : partnerCheck 17 (v283.getD 78 0) (p283.getD 78 0) = true := by decide +kernel
theorem pok161_79 : partnerCheck 17 (v283.getD 79 0) (p283.getD 79 0) = true := by decide +kernel
theorem pok161_80 : partnerCheck 17 (v283.getD 80 0) (p283.getD 80 0) = true := by decide +kernel
theorem pok161_81 : partnerCheck 17 (v283.getD 81 0) (p283.getD 81 0) = true := by decide +kernel
theorem pok161_82 : partnerCheck 17 (v283.getD 82 0) (p283.getD 82 0) = true := by decide +kernel
theorem pok161_83 : partnerCheck 17 (v283.getD 83 0) (p283.getD 83 0) = true := by decide +kernel
theorem pok161_84 : partnerCheck 17 (v283.getD 84 0) (p283.getD 84 0) = true := by decide +kernel
theorem pok161_85 : partnerCheck 17 (v283.getD 85 0) (p283.getD 85 0) = true := by decide +kernel
theorem pok161_86 : partnerCheck 17 (v283.getD 86 0) (p283.getD 86 0) = true := by decide +kernel
theorem pok161_87 : partnerCheck 17 (v283.getD 87 0) (p283.getD 87 0) = true := by decide +kernel
theorem pok161_88 : partnerCheck 17 (v283.getD 88 0) (p283.getD 88 0) = true := by decide +kernel
theorem pok161_89 : partnerCheck 17 (v283.getD 89 0) (p283.getD 89 0) = true := by decide +kernel
theorem pok161_90 : partnerCheck 17 (v283.getD 90 0) (p283.getD 90 0) = true := by decide +kernel
theorem pok161_91 : partnerCheck 17 (v283.getD 91 0) (p283.getD 91 0) = true := by decide +kernel
theorem pok161_92 : partnerCheck 17 (v283.getD 92 0) (p283.getD 92 0) = true := by decide +kernel
theorem pok161_93 : partnerCheck 17 (v283.getD 93 0) (p283.getD 93 0) = true := by decide +kernel
theorem pok161_94 : partnerCheck 17 (v283.getD 94 0) (p283.getD 94 0) = true := by decide +kernel
theorem pok161_95 : partnerCheck 17 (v283.getD 95 0) (p283.getD 95 0) = true := by decide +kernel
theorem pok161_96 : partnerCheck 17 (v283.getD 96 0) (p283.getD 96 0) = true := by decide +kernel
theorem pok161_97 : partnerCheck 17 (v283.getD 97 0) (p283.getD 97 0) = true := by decide +kernel
theorem pok161_98 : partnerCheck 17 (v283.getD 98 0) (p283.getD 98 0) = true := by decide +kernel
theorem pok161_99 : partnerCheck 17 (v283.getD 99 0) (p283.getD 99 0) = true := by decide +kernel
theorem pok161_100 : partnerCheck 17 (v283.getD 100 0) (p283.getD 100 0) = true := by decide +kernel
theorem pok161_101 : partnerCheck 17 (v283.getD 101 0) (p283.getD 101 0) = true := by decide +kernel
theorem pok161_102 : partnerCheck 17 (v283.getD 102 0) (p283.getD 102 0) = true := by decide +kernel
theorem pok161_103 : partnerCheck 17 (v283.getD 103 0) (p283.getD 103 0) = true := by decide +kernel
theorem pok161_104 : partnerCheck 17 (v283.getD 104 0) (p283.getD 104 0) = true := by decide +kernel
theorem pok161_105 : partnerCheck 17 (v283.getD 105 0) (p283.getD 105 0) = true := by decide +kernel
theorem pok161_106 : partnerCheck 17 (v283.getD 106 0) (p283.getD 106 0) = true := by decide +kernel
theorem pok161_107 : partnerCheck 17 (v283.getD 107 0) (p283.getD 107 0) = true := by decide +kernel
theorem pok161_108 : partnerCheck 17 (v283.getD 108 0) (p283.getD 108 0) = true := by decide +kernel
theorem pok161_109 : partnerCheck 17 (v283.getD 109 0) (p283.getD 109 0) = true := by decide +kernel
theorem pok161_110 : partnerCheck 17 (v283.getD 110 0) (p283.getD 110 0) = true := by decide +kernel
theorem pok161_111 : partnerCheck 17 (v283.getD 111 0) (p283.getD 111 0) = true := by decide +kernel
theorem pok161_112 : partnerCheck 17 (v283.getD 112 0) (p283.getD 112 0) = true := by decide +kernel
theorem pok161_113 : partnerCheck 17 (v283.getD 113 0) (p283.getD 113 0) = true := by decide +kernel
theorem pok161_114 : partnerCheck 17 (v283.getD 114 0) (p283.getD 114 0) = true := by decide +kernel
theorem pok161_115 : partnerCheck 17 (v283.getD 115 0) (p283.getD 115 0) = true := by decide +kernel
theorem pok161_116 : partnerCheck 17 (v283.getD 116 0) (p283.getD 116 0) = true := by decide +kernel
theorem pok161_117 : partnerCheck 17 (v283.getD 117 0) (p283.getD 117 0) = true := by decide +kernel
theorem pok161_118 : partnerCheck 17 (v283.getD 118 0) (p283.getD 118 0) = true := by decide +kernel
theorem pok161_119 : partnerCheck 17 (v283.getD 119 0) (p283.getD 119 0) = true := by decide +kernel
theorem pok161_120 : partnerCheck 17 (v283.getD 120 0) (p283.getD 120 0) = true := by decide +kernel
theorem pok161_121 : partnerCheck 17 (v283.getD 121 0) (p283.getD 121 0) = true := by decide +kernel
theorem pok161_122 : partnerCheck 17 (v283.getD 122 0) (p283.getD 122 0) = true := by decide +kernel
theorem pok161_123 : partnerCheck 17 (v283.getD 123 0) (p283.getD 123 0) = true := by decide +kernel
theorem pok161_124 : partnerCheck 17 (v283.getD 124 0) (p283.getD 124 0) = true := by decide +kernel
theorem pok161_125 : partnerCheck 17 (v283.getD 125 0) (p283.getD 125 0) = true := by decide +kernel
theorem pok161_126 : partnerCheck 17 (v283.getD 126 0) (p283.getD 126 0) = true := by decide +kernel
theorem pok161_127 : partnerCheck 17 (v283.getD 127 0) (p283.getD 127 0) = true := by decide +kernel
theorem pok161_128 : partnerCheck 17 (v283.getD 128 0) (p283.getD 128 0) = true := by decide +kernel
theorem pok161_129 : partnerCheck 17 (v283.getD 129 0) (p283.getD 129 0) = true := by decide +kernel
theorem pok161_130 : partnerCheck 17 (v283.getD 130 0) (p283.getD 130 0) = true := by decide +kernel
theorem pok161_131 : partnerCheck 17 (v283.getD 131 0) (p283.getD 131 0) = true := by decide +kernel
theorem pok161_132 : partnerCheck 17 (v283.getD 132 0) (p283.getD 132 0) = true := by decide +kernel
theorem pok161_133 : partnerCheck 17 (v283.getD 133 0) (p283.getD 133 0) = true := by decide +kernel
theorem pok161_134 : partnerCheck 17 (v283.getD 134 0) (p283.getD 134 0) = true := by decide +kernel
theorem pok161_135 : partnerCheck 17 (v283.getD 135 0) (p283.getD 135 0) = true := by decide +kernel
theorem pok161_136 : partnerCheck 17 (v283.getD 136 0) (p283.getD 136 0) = true := by decide +kernel
theorem pok161_137 : partnerCheck 17 (v283.getD 137 0) (p283.getD 137 0) = true := by decide +kernel
theorem pok161_138 : partnerCheck 17 (v283.getD 138 0) (p283.getD 138 0) = true := by decide +kernel
theorem pok161_139 : partnerCheck 17 (v283.getD 139 0) (p283.getD 139 0) = true := by decide +kernel
theorem pok161_140 : partnerCheck 17 (v283.getD 140 0) (p283.getD 140 0) = true := by decide +kernel
theorem pok161_141 : partnerCheck 17 (v283.getD 141 0) (p283.getD 141 0) = true := by decide +kernel
theorem pok161_142 : partnerCheck 17 (v283.getD 142 0) (p283.getD 142 0) = true := by decide +kernel
theorem pok161_143 : partnerCheck 17 (v283.getD 143 0) (p283.getD 143 0) = true := by decide +kernel
theorem pok161_144 : partnerCheck 17 (v283.getD 144 0) (p283.getD 144 0) = true := by decide +kernel
theorem pok161_145 : partnerCheck 17 (v283.getD 145 0) (p283.getD 145 0) = true := by decide +kernel
theorem pok161_146 : partnerCheck 17 (v283.getD 146 0) (p283.getD 146 0) = true := by decide +kernel
theorem pok161_147 : partnerCheck 17 (v283.getD 147 0) (p283.getD 147 0) = true := by decide +kernel
theorem pok161_148 : partnerCheck 17 (v283.getD 148 0) (p283.getD 148 0) = true := by decide +kernel
theorem pok161_149 : partnerCheck 17 (v283.getD 149 0) (p283.getD 149 0) = true := by decide +kernel
theorem pok161_150 : partnerCheck 17 (v283.getD 150 0) (p283.getD 150 0) = true := by decide +kernel
theorem pok161_151 : partnerCheck 17 (v283.getD 151 0) (p283.getD 151 0) = true := by decide +kernel
theorem pok161_152 : partnerCheck 17 (v283.getD 152 0) (p283.getD 152 0) = true := by decide +kernel
theorem pok161_153 : partnerCheck 17 (v283.getD 153 0) (p283.getD 153 0) = true := by decide +kernel
theorem pok161_154 : partnerCheck 17 (v283.getD 154 0) (p283.getD 154 0) = true := by decide +kernel
theorem pok161_155 : partnerCheck 17 (v283.getD 155 0) (p283.getD 155 0) = true := by decide +kernel
theorem pok161_156 : partnerCheck 17 (v283.getD 156 0) (p283.getD 156 0) = true := by decide +kernel
theorem pok161_157 : partnerCheck 17 (v283.getD 157 0) (p283.getD 157 0) = true := by decide +kernel
theorem pok161_158 : partnerCheck 17 (v283.getD 158 0) (p283.getD 158 0) = true := by decide +kernel
theorem pok161_159 : partnerCheck 17 (v283.getD 159 0) (p283.getD 159 0) = true := by decide +kernel
theorem pok161_160 : partnerCheck 17 (v283.getD 160 0) (p283.getD 160 0) = true := by decide +kernel
theorem pok161_161 : partnerCheck 17 (v283.getD 161 0) (p283.getD 161 0) = true := by decide +kernel
theorem pok161_162 : partnerCheck 17 (v283.getD 162 0) (p283.getD 162 0) = true := by decide +kernel
theorem pok161_163 : partnerCheck 17 (v283.getD 163 0) (p283.getD 163 0) = true := by decide +kernel
theorem pok161_164 : partnerCheck 17 (v283.getD 164 0) (p283.getD 164 0) = true := by decide +kernel
theorem pok161_165 : partnerCheck 17 (v283.getD 165 0) (p283.getD 165 0) = true := by decide +kernel
theorem pok161_166 : partnerCheck 17 (v283.getD 166 0) (p283.getD 166 0) = true := by decide +kernel
theorem pok161_167 : partnerCheck 17 (v283.getD 167 0) (p283.getD 167 0) = true := by decide +kernel
theorem pok161_168 : partnerCheck 17 (v283.getD 168 0) (p283.getD 168 0) = true := by decide +kernel
theorem pok161_169 : partnerCheck 17 (v283.getD 169 0) (p283.getD 169 0) = true := by decide +kernel
theorem pok161_170 : partnerCheck 17 (v283.getD 170 0) (p283.getD 170 0) = true := by decide +kernel
theorem pok161_171 : partnerCheck 17 (v283.getD 171 0) (p283.getD 171 0) = true := by decide +kernel
theorem pok161_172 : partnerCheck 17 (v283.getD 172 0) (p283.getD 172 0) = true := by decide +kernel
theorem pok161_173 : partnerCheck 17 (v283.getD 173 0) (p283.getD 173 0) = true := by decide +kernel
theorem pok161_174 : partnerCheck 17 (v283.getD 174 0) (p283.getD 174 0) = true := by decide +kernel
theorem pok161_175 : partnerCheck 17 (v283.getD 175 0) (p283.getD 175 0) = true := by decide +kernel
theorem pok161_176 : partnerCheck 17 (v283.getD 176 0) (p283.getD 176 0) = true := by decide +kernel
theorem pok161_177 : partnerCheck 17 (v283.getD 177 0) (p283.getD 177 0) = true := by decide +kernel
theorem pok161_178 : partnerCheck 17 (v283.getD 178 0) (p283.getD 178 0) = true := by decide +kernel
theorem pok161_179 : partnerCheck 17 (v283.getD 179 0) (p283.getD 179 0) = true := by decide +kernel
theorem pok161_180 : partnerCheck 17 (v283.getD 180 0) (p283.getD 180 0) = true := by decide +kernel
theorem pok161_181 : partnerCheck 17 (v283.getD 181 0) (p283.getD 181 0) = true := by decide +kernel
theorem pok161_182 : partnerCheck 17 (v283.getD 182 0) (p283.getD 182 0) = true := by decide +kernel
theorem pok161_183 : partnerCheck 17 (v283.getD 183 0) (p283.getD 183 0) = true := by decide +kernel
theorem pok161_184 : partnerCheck 17 (v283.getD 184 0) (p283.getD 184 0) = true := by decide +kernel
theorem pok161_185 : partnerCheck 17 (v283.getD 185 0) (p283.getD 185 0) = true := by decide +kernel
theorem pok161_186 : partnerCheck 17 (v283.getD 186 0) (p283.getD 186 0) = true := by decide +kernel
theorem pok161_187 : partnerCheck 17 (v283.getD 187 0) (p283.getD 187 0) = true := by decide +kernel
theorem pok161_188 : partnerCheck 17 (v283.getD 188 0) (p283.getD 188 0) = true := by decide +kernel
theorem pok161_189 : partnerCheck 17 (v283.getD 189 0) (p283.getD 189 0) = true := by decide +kernel
theorem pok161_190 : partnerCheck 17 (v283.getD 190 0) (p283.getD 190 0) = true := by decide +kernel
theorem pok161_191 : partnerCheck 17 (v283.getD 191 0) (p283.getD 191 0) = true := by decide +kernel
theorem pok161_192 : partnerCheck 17 (v283.getD 192 0) (p283.getD 192 0) = true := by decide +kernel
theorem pok161_193 : partnerCheck 17 (v283.getD 193 0) (p283.getD 193 0) = true := by decide +kernel
theorem pok161_194 : partnerCheck 17 (v283.getD 194 0) (p283.getD 194 0) = true := by decide +kernel
theorem pok161_195 : partnerCheck 17 (v283.getD 195 0) (p283.getD 195 0) = true := by decide +kernel
theorem pok161_196 : partnerCheck 17 (v283.getD 196 0) (p283.getD 196 0) = true := by decide +kernel
theorem pok161_197 : partnerCheck 17 (v283.getD 197 0) (p283.getD 197 0) = true := by decide +kernel
theorem pok161_198 : partnerCheck 17 (v283.getD 198 0) (p283.getD 198 0) = true := by decide +kernel
theorem pok161_199 : partnerCheck 17 (v283.getD 199 0) (p283.getD 199 0) = true := by decide +kernel
theorem pok161_200 : partnerCheck 17 (v283.getD 200 0) (p283.getD 200 0) = true := by decide +kernel
theorem pok161_201 : partnerCheck 17 (v283.getD 201 0) (p283.getD 201 0) = true := by decide +kernel
theorem pok161_202 : partnerCheck 17 (v283.getD 202 0) (p283.getD 202 0) = true := by decide +kernel
theorem pok161_203 : partnerCheck 17 (v283.getD 203 0) (p283.getD 203 0) = true := by decide +kernel
theorem pok161_204 : partnerCheck 17 (v283.getD 204 0) (p283.getD 204 0) = true := by decide +kernel
theorem pok161_205 : partnerCheck 17 (v283.getD 205 0) (p283.getD 205 0) = true := by decide +kernel
theorem pok161_206 : partnerCheck 17 (v283.getD 206 0) (p283.getD 206 0) = true := by decide +kernel
theorem pok161_207 : partnerCheck 17 (v283.getD 207 0) (p283.getD 207 0) = true := by decide +kernel
theorem pok161_208 : partnerCheck 17 (v283.getD 208 0) (p283.getD 208 0) = true := by decide +kernel
theorem pok161_209 : partnerCheck 17 (v283.getD 209 0) (p283.getD 209 0) = true := by decide +kernel
theorem pok161_210 : partnerCheck 17 (v283.getD 210 0) (p283.getD 210 0) = true := by decide +kernel
theorem pok161_211 : partnerCheck 17 (v283.getD 211 0) (p283.getD 211 0) = true := by decide +kernel
theorem pok161 : ∀ c < 212, partnerCheck (x2KeyMult 1 k161 0) (v283.getD c 0) (p283.getD c 0) = true := by
  intro c hc
  show partnerCheck 17 (v283.getD c 0) (p283.getD c 0) = true
  interval_cases c
  · exact pok161_0
  · exact pok161_1
  · exact pok161_2
  · exact pok161_3
  · exact pok161_4
  · exact pok161_5
  · exact pok161_6
  · exact pok161_7
  · exact pok161_8
  · exact pok161_9
  · exact pok161_10
  · exact pok161_11
  · exact pok161_12
  · exact pok161_13
  · exact pok161_14
  · exact pok161_15
  · exact pok161_16
  · exact pok161_17
  · exact pok161_18
  · exact pok161_19
  · exact pok161_20
  · exact pok161_21
  · exact pok161_22
  · exact pok161_23
  · exact pok161_24
  · exact pok161_25
  · exact pok161_26
  · exact pok161_27
  · exact pok161_28
  · exact pok161_29
  · exact pok161_30
  · exact pok161_31
  · exact pok161_32
  · exact pok161_33
  · exact pok161_34
  · exact pok161_35
  · exact pok161_36
  · exact pok161_37
  · exact pok161_38
  · exact pok161_39
  · exact pok161_40
  · exact pok161_41
  · exact pok161_42
  · exact pok161_43
  · exact pok161_44
  · exact pok161_45
  · exact pok161_46
  · exact pok161_47
  · exact pok161_48
  · exact pok161_49
  · exact pok161_50
  · exact pok161_51
  · exact pok161_52
  · exact pok161_53
  · exact pok161_54
  · exact pok161_55
  · exact pok161_56
  · exact pok161_57
  · exact pok161_58
  · exact pok161_59
  · exact pok161_60
  · exact pok161_61
  · exact pok161_62
  · exact pok161_63
  · exact pok161_64
  · exact pok161_65
  · exact pok161_66
  · exact pok161_67
  · exact pok161_68
  · exact pok161_69
  · exact pok161_70
  · exact pok161_71
  · exact pok161_72
  · exact pok161_73
  · exact pok161_74
  · exact pok161_75
  · exact pok161_76
  · exact pok161_77
  · exact pok161_78
  · exact pok161_79
  · exact pok161_80
  · exact pok161_81
  · exact pok161_82
  · exact pok161_83
  · exact pok161_84
  · exact pok161_85
  · exact pok161_86
  · exact pok161_87
  · exact pok161_88
  · exact pok161_89
  · exact pok161_90
  · exact pok161_91
  · exact pok161_92
  · exact pok161_93
  · exact pok161_94
  · exact pok161_95
  · exact pok161_96
  · exact pok161_97
  · exact pok161_98
  · exact pok161_99
  · exact pok161_100
  · exact pok161_101
  · exact pok161_102
  · exact pok161_103
  · exact pok161_104
  · exact pok161_105
  · exact pok161_106
  · exact pok161_107
  · exact pok161_108
  · exact pok161_109
  · exact pok161_110
  · exact pok161_111
  · exact pok161_112
  · exact pok161_113
  · exact pok161_114
  · exact pok161_115
  · exact pok161_116
  · exact pok161_117
  · exact pok161_118
  · exact pok161_119
  · exact pok161_120
  · exact pok161_121
  · exact pok161_122
  · exact pok161_123
  · exact pok161_124
  · exact pok161_125
  · exact pok161_126
  · exact pok161_127
  · exact pok161_128
  · exact pok161_129
  · exact pok161_130
  · exact pok161_131
  · exact pok161_132
  · exact pok161_133
  · exact pok161_134
  · exact pok161_135
  · exact pok161_136
  · exact pok161_137
  · exact pok161_138
  · exact pok161_139
  · exact pok161_140
  · exact pok161_141
  · exact pok161_142
  · exact pok161_143
  · exact pok161_144
  · exact pok161_145
  · exact pok161_146
  · exact pok161_147
  · exact pok161_148
  · exact pok161_149
  · exact pok161_150
  · exact pok161_151
  · exact pok161_152
  · exact pok161_153
  · exact pok161_154
  · exact pok161_155
  · exact pok161_156
  · exact pok161_157
  · exact pok161_158
  · exact pok161_159
  · exact pok161_160
  · exact pok161_161
  · exact pok161_162
  · exact pok161_163
  · exact pok161_164
  · exact pok161_165
  · exact pok161_166
  · exact pok161_167
  · exact pok161_168
  · exact pok161_169
  · exact pok161_170
  · exact pok161_171
  · exact pok161_172
  · exact pok161_173
  · exact pok161_174
  · exact pok161_175
  · exact pok161_176
  · exact pok161_177
  · exact pok161_178
  · exact pok161_179
  · exact pok161_180
  · exact pok161_181
  · exact pok161_182
  · exact pok161_183
  · exact pok161_184
  · exact pok161_185
  · exact pok161_186
  · exact pok161_187
  · exact pok161_188
  · exact pok161_189
  · exact pok161_190
  · exact pok161_191
  · exact pok161_192
  · exact pok161_193
  · exact pok161_194
  · exact pok161_195
  · exact pok161_196
  · exact pok161_197
  · exact pok161_198
  · exact pok161_199
  · exact pok161_200
  · exact pok161_201
  · exact pok161_202
  · exact pok161_203
  · exact pok161_204
  · exact pok161_205
  · exact pok161_206
  · exact pok161_207
  · exact pok161_208
  · exact pok161_209
  · exact pok161_210
  · exact pok161_211
theorem small161 : x2KeyDegree 1 k161 = 2 ∧ x2KeyMult 1 k161 0 = x2KeyMult 1 k161 1 ∧ x2KeyMult 1 k161 1 = x2KeyMult 1 k161 2 ∧ 1 ≤ x2KeyMult 1 k161 0 ∧ glRowOK 1 (x2KeyTypes 1 k161 0) (x2KeyMult 1 k161 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k161 1) (x2KeyMult 1 k161 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k161 2) (x2KeyMult 1 k161 2) 512 = true ∧ gj283.length = x2KeySize 1 k161 ∧ x2KeySize 1 k161 ≤ 512 ∧ v283.length = 212 ∧ p283.length = 212 := by decide +kernel
theorem chk161 : trial2KeyChk 1 k161 212 gj283 x2Trial_283 v283 p283 :=
  trial2KeyChk_intro 1 k161 212 gj283 x2Trial_283 v283 p283 small161 gjok161 vok161 pok161

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k159, ibFS [(v281, v281, 94810963968000)]), (k160, ibFS [(v282, v282, 94810963968000)]), (k161, ibFS [(v283, v283, 94810963968000), (p283, p283, 31603654656000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![6, 6, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN159 : N k159 = x2TrialForm 1 k159) (hN160 : N k160 = x2TrialForm 1 k160) (hN161 : N k161 = x2TrialForm 1 k161) :
    ∀ e ∈ ks, keyOK (x2Mult 1 6 * x2Mult 1 6 * x2Mult 1 6) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact keyOK_of_trialChk 1 N k159 122 _ gj281 x2Trial_281 v281 (by decide) (by rw [hN159]; exact trialForm_eq 1 k159 122 x2Trial_281 (by decide) rfl) chk159
  · exact keyOK_of_trialChk 1 N k160 91 _ gj282 x2Trial_282 v282 (by decide) (by rw [hN160]; exact trialForm_eq 1 k160 91 x2Trial_282 (by decide) rfl) chk160
  · exact keyOK_of_trial2Chk 1 N k161 212 _ gj283 x2Trial_283 v283 p283 (by decide) (by rw [hN161]; exact trialForm_eq 1 k161 212 x2Trial_283 (by decide) rfl) chk161

end ThreeCopyQutritWerner.X2.InK1x666
