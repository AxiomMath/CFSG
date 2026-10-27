module

public import Certificates.Kernel.TwoHS.HYWords
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyCheck
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CFSG.KD.TwoHS

open CFSG.EvenSporadicStandard.TwoHS

theorem fy_r3 : wEq (fyRWord ++ fyRWord ++ fyRWord) [] = true := by quickRfl
theorem fy_cc0 : wEq (fyC 0 ++ fyC 0) tWord = true := by quickRfl
theorem fy_cc1 : wEq (fyC 1 ++ fyC 1) tWord = true := by quickRfl
theorem fy_cc2 : wEq (fyC 2 ++ fyC 2) tWord = true := by quickRfl
theorem fy_cc3 : wEq (fyC 3 ++ fyC 3) tWord = true := by quickRfl
theorem fy_cr0 : wEq (fyC 0 ++ fyRWord) (fyRWord ++ fyC 0) = true := by quickRfl
theorem fy_cr1 : wEq (fyC 1 ++ fyRWord) (fyRWord ++ fyC 1) = true := by quickRfl
theorem fy_cr2 : wEq (fyC 2 ++ fyRWord) (fyRWord ++ fyC 2) = true := by quickRfl
theorem fy_cr3 : wEq (fyC 3 ++ fyRWord) (fyRWord ++ fyC 3) = true := by quickRfl
theorem fy_ca0 : wEq (fyC 0 ++ fyAWord) (tWord ++ fyAWord ++ sigWord (fyC 0)) = true := by quickRfl
theorem fy_ca1 : wEq (fyC 1 ++ fyAWord) (tWord ++ fyAWord ++ sigWord (fyC 1)) = true := by quickRfl
theorem fy_ca2 : wEq (fyC 2 ++ fyAWord) (tWord ++ fyAWord ++ sigWord (fyC 2)) = true := by quickRfl
theorem fy_ca3 : wEq (fyC 3 ++ fyAWord) (tWord ++ fyAWord ++ sigWord (fyC 3)) = true := by quickRfl
theorem fy_b0 : wEq (fyC 0 ++ fyC 1 ++ fyC 0) (fyC 1 ++ fyC 0 ++ fyC 1) = true := by quickRfl
theorem fy_b1 : wEq (fyC 1 ++ fyC 2 ++ fyC 1) (fyC 2 ++ fyC 1 ++ fyC 2) = true := by quickRfl
theorem fy_b2 : wEq (fyC 2 ++ fyC 3 ++ fyC 2) (fyC 3 ++ fyC 2 ++ fyC 3) = true := by quickRfl
theorem fy_c02 : wEq (fyC 0 ++ fyC 2) (fyC 2 ++ fyC 0) = true := by quickRfl
theorem fy_c03 : wEq (fyC 0 ++ fyC 3) (fyC 3 ++ fyC 0) = true := by quickRfl
theorem fy_c13 : wEq (fyC 1 ++ fyC 3) (fyC 3 ++ fyC 1) = true := by quickRfl
theorem fy_as : wEq (fyAWord ++ sigWord fyAWord) [] = true := by quickRfl
theorem fy_ar : wEq (fyAWord ++ sigWord fyRWord) (fyRWord ++ fyAWord) = true := by quickRfl
theorem fy_l : wEq (fyLWord ++ fyAWord) (fyAWord ++ sigWord (fyC 0) ++ tWord ++ sigWord fyLWord) =
    true := by quickRfl

theorem fy_r' : (!wEq fyRWord []) = true := by quickRfl
theorem fy_c01' : (!wEq (fyC 0) (fyC 1)) = true := by quickRfl
theorem fy_c20' : (!wEq (fyC 2) (fyC 0)) = true := by quickRfl
theorem fy_c2t' : (!wEq (fyC 2) (fyC 0 ++ tWord)) = true := by quickRfl

theorem fy_r : wEq fyRWord [] = false := by simpa using fy_r'
theorem fy_c01 : wEq (fyC 0) (fyC 1) = false := by simpa using fy_c01'
theorem fy_c20 : wEq (fyC 2) (fyC 0) = false := by simpa using fy_c20'
theorem fy_c2t : wEq (fyC 2) (fyC 0 ++ tWord) = false := by simpa using fy_c2t'

end CFSG.KD.TwoHS

end
