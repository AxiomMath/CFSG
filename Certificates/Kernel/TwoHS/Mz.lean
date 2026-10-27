module

public import Certificates.Kernel.TwoHS.HYWords
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUModCheck
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CFSG.KD.TwoHS

open CFSG.EvenSporadicStandard.TwoHS

theorem mz_r3 : wEq (mzRW ++ mzRW ++ mzRW) [] = true := by quickRfl
theorem mz_rb0 : wEq (mzRW ++ betaW 0) (kapW (colOf mzRData ([0, 1, 3].getD 0 0)) ++ mzRW) = true := by
  quickRfl
theorem mz_rb1 : wEq (mzRW ++ betaW 1) (kapW (colOf mzRData ([0, 1, 3].getD 1 0)) ++ mzRW) = true := by
  quickRfl
theorem mz_rb2 : wEq (mzRW ++ betaW 2) (kapW (colOf mzRData ([0, 1, 3].getD 2 0)) ++ mzRW) = true := by
  quickRfl
theorem mz_as : wEq (mzAW ++ sigWord mzAW) [] = true := by quickRfl
theorem mz_ab0 : wEq (mzAW ++ sigWord (betaW 0)) (rptW (betaW 0) 3 ++ mzAW) = true := by quickRfl
theorem mz_ab1 : wEq (mzAW ++ sigWord (betaW 1)) (rptW (betaW 1) 3 ++ mzAW) = true := by quickRfl
theorem mz_ab2 : wEq (mzAW ++ sigWord (betaW 2)) (rptW (betaW 2) 3 ++ mzAW) = true := by quickRfl
theorem mz_ra : wEq (mzRW ++ mzAW) (mzAW ++ sigWord mzRW) = true := by quickRfl
theorem mz_p3 : wEq (mzPW ++ mzPW ++ mzPW) [] = true := by quickRfl
theorem mz_pr : wEq (mzPW ++ mzRW) (mzRW ++ mzPW) = true := by quickRfl
theorem mz_pa : wEq (mzPW ++ mzAW) (mzAW ++ sigWord mzPW) = true := by quickRfl
theorem mz_g1 : wEq (gamma1Word ++ mzAW) (kapW mzEps ++ mzAW ++ sigWord gamma1Word) = true := by
  quickRfl
theorem mz_g2 : wEq (gamma2Word ++ sigWord mzAW) (kapW mzEps ++ mzAW ++ sigWord gamma2Word) =
    true := by quickRfl

theorem mz_r' : (!wEq mzRW []) = true := by quickRfl
theorem mz_p' : (!wEq mzPW []) = true := by quickRfl
theorem mz_pR' : (!wEq mzPW mzRW) = true := by quickRfl
theorem mz_prr' : (!wEq mzPW (mzRW ++ mzRW)) = true := by quickRfl

theorem mz_r : wEq mzRW [] = false := by simpa using mz_r'
theorem mz_p : wEq mzPW [] = false := by simpa using mz_p'
theorem mz_pR : wEq mzPW mzRW = false := by simpa using mz_pR'
theorem mz_prr : wEq mzPW (mzRW ++ mzRW) = false := by simpa using mz_prr'

end CFSG.KD.TwoHS

end
