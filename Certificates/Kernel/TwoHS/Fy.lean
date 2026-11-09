module

public import Certificates.Kernel.TwoHS.HYWords
public import Certificates.Kernel.TwoHS.FyPins
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyCheck
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CFSG.KD.TwoHS

open CFSG.EvenSporadicStandard.TwoHS

theorem fy_r3 : wEq (fyRWord ++ fyRWord ++ fyRWord) [] = true := by
  apply wEq_of_beq (by quickRfl)
  rewrite [WK_append (u := fyRWord ++ fyRWord) (v := fyRWord) (by quickRfl) (by quickRfl),
    WK_append (u := fyRWord) (v := fyRWord) (by quickRfl) (by quickRfl), WK_fyR, WK_nil]
  simp only [pc_eq_C]
  quickRfl

theorem fy_cc0 : wEq (fyC 0 ++ fyC 0) tWord = true := by
  apply wEq_of_beq (by quickRfl)
  rewrite [WK_append (u := fyC 0) (v := fyC 0) (by quickRfl) (by quickRfl), WK_fyC0, WK_fyT]
  simp only [pc_eq_C]
  quickRfl

theorem fy_cc1 : wEq (fyC 1 ++ fyC 1) tWord = true := by
  apply wEq_of_beq (by quickRfl)
  rewrite [WK_append (u := fyC 1) (v := fyC 1) (by quickRfl) (by quickRfl), WK_fyC1, WK_fyT]
  simp only [pc_eq_C]
  quickRfl

theorem fy_cc2 : wEq (fyC 2 ++ fyC 2) tWord = true := by
  apply wEq_of_beq (by quickRfl)
  rewrite [WK_append (u := fyC 2) (v := fyC 2) (by quickRfl) (by quickRfl), WK_fyC2, WK_fyT]
  simp only [pc_eq_C]
  quickRfl

theorem fy_cc3 : wEq (fyC 3 ++ fyC 3) tWord = true := by
  apply wEq_of_beq (by quickRfl)
  rewrite [WK_append (u := fyC 3) (v := fyC 3) (by quickRfl) (by quickRfl), WK_fyC3, WK_fyT]
  simp only [pc_eq_C]
  quickRfl

theorem fy_cr0 : wEq (fyC 0 ++ fyRWord) (fyRWord ++ fyC 0) = true := by
  apply wEq_of_beq (by quickRfl)
  rewrite [WK_append (u := fyC 0) (v := fyRWord) (by quickRfl) (by quickRfl),
    WK_append (u := fyRWord) (v := fyC 0) (by quickRfl) (by quickRfl), WK_fyC0, WK_fyR]
  simp only [pc_eq_C]
  quickRfl

theorem fy_cr1 : wEq (fyC 1 ++ fyRWord) (fyRWord ++ fyC 1) = true := by
  apply wEq_of_beq (by quickRfl)
  rewrite [WK_append (u := fyC 1) (v := fyRWord) (by quickRfl) (by quickRfl),
    WK_append (u := fyRWord) (v := fyC 1) (by quickRfl) (by quickRfl), WK_fyC1, WK_fyR]
  simp only [pc_eq_C]
  quickRfl

theorem fy_cr2 : wEq (fyC 2 ++ fyRWord) (fyRWord ++ fyC 2) = true := by
  apply wEq_of_beq (by quickRfl)
  rewrite [WK_append (u := fyC 2) (v := fyRWord) (by quickRfl) (by quickRfl),
    WK_append (u := fyRWord) (v := fyC 2) (by quickRfl) (by quickRfl), WK_fyC2, WK_fyR]
  simp only [pc_eq_C]
  quickRfl

theorem fy_cr3 : wEq (fyC 3 ++ fyRWord) (fyRWord ++ fyC 3) = true := by
  apply wEq_of_beq (by quickRfl)
  rewrite [WK_append (u := fyC 3) (v := fyRWord) (by quickRfl) (by quickRfl),
    WK_append (u := fyRWord) (v := fyC 3) (by quickRfl) (by quickRfl), WK_fyC3, WK_fyR]
  simp only [pc_eq_C]
  quickRfl

theorem fy_ca0 : wEq (fyC 0 ++ fyAWord) (tWord ++ fyAWord ++ sigWord (fyC 0)) = true := by
  apply wEq_of_beq (by quickRfl)
  rewrite [WK_append (u := fyC 0) (v := fyAWord) (by quickRfl) (by quickRfl),
    WK_append (u := tWord ++ fyAWord) (v := sigWord (fyC 0)) (by quickRfl) (by quickRfl),
    WK_append (u := tWord) (v := fyAWord) (by quickRfl) (by quickRfl), WK_fyC0, WK_fyA, WK_fyT,
    WK_sigWordP (fyC 0)]
  simp only [pc_eq_C]
  quickRfl

theorem fy_ca1 : wEq (fyC 1 ++ fyAWord) (tWord ++ fyAWord ++ sigWord (fyC 1)) = true := by
  apply wEq_of_beq (by quickRfl)
  rewrite [WK_append (u := fyC 1) (v := fyAWord) (by quickRfl) (by quickRfl),
    WK_append (u := tWord ++ fyAWord) (v := sigWord (fyC 1)) (by quickRfl) (by quickRfl),
    WK_append (u := tWord) (v := fyAWord) (by quickRfl) (by quickRfl), WK_fyC1, WK_fyA, WK_fyT,
    WK_sigWordP (fyC 1)]
  simp only [pc_eq_C]
  quickRfl

theorem fy_ca2 : wEq (fyC 2 ++ fyAWord) (tWord ++ fyAWord ++ sigWord (fyC 2)) = true := by
  apply wEq_of_beq (by quickRfl)
  rewrite [WK_append (u := fyC 2) (v := fyAWord) (by quickRfl) (by quickRfl),
    WK_append (u := tWord ++ fyAWord) (v := sigWord (fyC 2)) (by quickRfl) (by quickRfl),
    WK_append (u := tWord) (v := fyAWord) (by quickRfl) (by quickRfl), WK_fyC2, WK_fyA, WK_fyT,
    WK_sigWordP (fyC 2)]
  simp only [pc_eq_C]
  quickRfl

theorem fy_ca3 : wEq (fyC 3 ++ fyAWord) (tWord ++ fyAWord ++ sigWord (fyC 3)) = true := by
  apply wEq_of_beq (by quickRfl)
  rewrite [WK_append (u := fyC 3) (v := fyAWord) (by quickRfl) (by quickRfl),
    WK_append (u := tWord ++ fyAWord) (v := sigWord (fyC 3)) (by quickRfl) (by quickRfl),
    WK_append (u := tWord) (v := fyAWord) (by quickRfl) (by quickRfl), WK_fyC3, WK_fyA, WK_fyT,
    WK_sigWordP (fyC 3)]
  simp only [pc_eq_C]
  quickRfl

theorem fy_b0 : wEq (fyC 0 ++ fyC 1 ++ fyC 0) (fyC 1 ++ fyC 0 ++ fyC 1) = true := by
  apply wEq_of_beq (by quickRfl)
  rewrite [WK_append (u := fyC 0 ++ fyC 1) (v := fyC 0) (by quickRfl) (by quickRfl),
    WK_append (u := fyC 0) (v := fyC 1) (by quickRfl) (by quickRfl),
    WK_append (u := fyC 1 ++ fyC 0) (v := fyC 1) (by quickRfl) (by quickRfl),
    WK_append (u := fyC 1) (v := fyC 0) (by quickRfl) (by quickRfl), WK_fyC0, WK_fyC1]
  simp only [pc_eq_C]
  quickRfl

theorem fy_b1 : wEq (fyC 1 ++ fyC 2 ++ fyC 1) (fyC 2 ++ fyC 1 ++ fyC 2) = true := by
  apply wEq_of_beq (by quickRfl)
  rewrite [WK_append (u := fyC 1 ++ fyC 2) (v := fyC 1) (by quickRfl) (by quickRfl),
    WK_append (u := fyC 1) (v := fyC 2) (by quickRfl) (by quickRfl),
    WK_append (u := fyC 2 ++ fyC 1) (v := fyC 2) (by quickRfl) (by quickRfl),
    WK_append (u := fyC 2) (v := fyC 1) (by quickRfl) (by quickRfl), WK_fyC1, WK_fyC2]
  simp only [pc_eq_C]
  quickRfl

theorem fy_b2 : wEq (fyC 2 ++ fyC 3 ++ fyC 2) (fyC 3 ++ fyC 2 ++ fyC 3) = true := by
  apply wEq_of_beq (by quickRfl)
  rewrite [WK_append (u := fyC 2 ++ fyC 3) (v := fyC 2) (by quickRfl) (by quickRfl),
    WK_append (u := fyC 2) (v := fyC 3) (by quickRfl) (by quickRfl),
    WK_append (u := fyC 3 ++ fyC 2) (v := fyC 3) (by quickRfl) (by quickRfl),
    WK_append (u := fyC 3) (v := fyC 2) (by quickRfl) (by quickRfl), WK_fyC2, WK_fyC3]
  simp only [pc_eq_C]
  quickRfl

theorem fy_c02 : wEq (fyC 0 ++ fyC 2) (fyC 2 ++ fyC 0) = true := by
  apply wEq_of_beq (by quickRfl)
  rewrite [WK_append (u := fyC 0) (v := fyC 2) (by quickRfl) (by quickRfl),
    WK_append (u := fyC 2) (v := fyC 0) (by quickRfl) (by quickRfl), WK_fyC0, WK_fyC2]
  simp only [pc_eq_C]
  quickRfl

theorem fy_c03 : wEq (fyC 0 ++ fyC 3) (fyC 3 ++ fyC 0) = true := by
  apply wEq_of_beq (by quickRfl)
  rewrite [WK_append (u := fyC 0) (v := fyC 3) (by quickRfl) (by quickRfl),
    WK_append (u := fyC 3) (v := fyC 0) (by quickRfl) (by quickRfl), WK_fyC0, WK_fyC3]
  simp only [pc_eq_C]
  quickRfl

theorem fy_c13 : wEq (fyC 1 ++ fyC 3) (fyC 3 ++ fyC 1) = true := by
  apply wEq_of_beq (by quickRfl)
  rewrite [WK_append (u := fyC 1) (v := fyC 3) (by quickRfl) (by quickRfl),
    WK_append (u := fyC 3) (v := fyC 1) (by quickRfl) (by quickRfl), WK_fyC1, WK_fyC3]
  simp only [pc_eq_C]
  quickRfl

theorem fy_as : wEq (fyAWord ++ sigWord fyAWord) [] = true := by
  apply wEq_of_beq (by quickRfl)
  rewrite [WK_append (u := fyAWord) (v := sigWord fyAWord) (by quickRfl) (by quickRfl), WK_fyA,
    WK_sigWordP fyAWord, WK_nil]
  simp only [pc_eq_C]
  quickRfl

theorem fy_ar : wEq (fyAWord ++ sigWord fyRWord) (fyRWord ++ fyAWord) = true := by
  apply wEq_of_beq (by quickRfl)
  rewrite [WK_append (u := fyAWord) (v := sigWord fyRWord) (by quickRfl) (by quickRfl),
    WK_append (u := fyRWord) (v := fyAWord) (by quickRfl) (by quickRfl), WK_fyA,
    WK_sigWordP fyRWord, WK_fyR]
  simp only [pc_eq_C]
  quickRfl

theorem fy_l : wEq (fyLWord ++ fyAWord) (fyAWord ++ sigWord (fyC 0) ++ tWord ++ sigWord fyLWord) =
    true := by
  apply wEq_of_beq (by quickRfl)
  rewrite [WK_append (u := fyLWord) (v := fyAWord) (by quickRfl) (by quickRfl),
    WK_append (u := fyAWord ++ sigWord (fyC 0) ++ tWord) (v := sigWord fyLWord) (by quickRfl)
      (by quickRfl),
    WK_append (u := fyAWord ++ sigWord (fyC 0)) (v := tWord) (by quickRfl) (by quickRfl),
    WK_append (u := fyAWord) (v := sigWord (fyC 0)) (by quickRfl) (by quickRfl), WK_fyL, WK_fyA,
    WK_sigWordP (fyC 0), WK_fyT, WK_sigWordP fyLWord]
  simp only [pc_eq_C]
  quickRfl

theorem fy_r' : (!wEq fyRWord []) = true := by
  apply not_wEq_of_beq (by quickRfl)
  rewrite [WK_fyR, WK_nil]
  quickRfl

theorem fy_c01' : (!wEq (fyC 0) (fyC 1)) = true := by
  apply not_wEq_of_beq (by quickRfl)
  rewrite [WK_fyC0, WK_fyC1]
  quickRfl

theorem fy_c20' : (!wEq (fyC 2) (fyC 0)) = true := by
  apply not_wEq_of_beq (by quickRfl)
  rewrite [WK_fyC2, WK_fyC0]
  quickRfl

theorem fy_c2t' : (!wEq (fyC 2) (fyC 0 ++ tWord)) = true := by
  apply not_wEq_of_beq (by quickRfl)
  rewrite [WK_append (u := fyC 0) (v := tWord) (by quickRfl) (by quickRfl), WK_fyC2, WK_fyC0,
    WK_fyT]
  simp only [pc_eq_C]
  quickRfl

theorem fy_r : wEq fyRWord [] = false := by simpa using fy_r'
theorem fy_c01 : wEq (fyC 0) (fyC 1) = false := by simpa using fy_c01'
theorem fy_c20 : wEq (fyC 2) (fyC 0) = false := by simpa using fy_c20'
theorem fy_c2t : wEq (fyC 2) (fyC 0 ++ tWord) = false := by simpa using fy_c2t'

end CFSG.KD.TwoHS

end
