module

public import CFSG.Certificates.Kernel.GMS78RuNSound
public import Certificates.Kernel.GMS78.S
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
import Batteries.Tactic.Init

public section

namespace CertificateChecks.KernelGMS78

open CFSG.KC.GMS

theorem bindNC_ok : bindNC CFSG.GMS78RuS.sBasis CFSG.GMS78RuN.nBetaTab CFSG.GMS78RuN.nCols
    CFSG.GMS78RuN.nBasis CFSG.GMS78RuS.dCodeTab CFSG.GMS78RuN.nTwTab = true := by quickRfl
theorem inv_ok : invTabOK INV = true := by quickRfl
theorem gamCol_ok : kGamCol QT = true := by quickRfl
theorem dPart_0 : kDPart QT INV 0 = true := by quickRfl
theorem dPart_1 : kDPart QT INV 1 = true := by quickRfl
theorem dPart_2 : kDPart QT INV 2 = true := by quickRfl
theorem dPart_3 : kDPart QT INV 3 = true := by quickRfl
theorem dPart_4 : kDPart QT INV 4 = true := by quickRfl
theorem dPart_5 : kDPart QT INV 5 = true := by quickRfl
theorem dPart_6 : kDPart QT INV 6 = true := by quickRfl
theorem dPart_7 : kDPart QT INV 7 = true := by quickRfl

theorem nCoord_eq : CFSG.GMS78RuN.gamColCheck = true ∧ CFSG.GMS78RuN.dPartCheck = true := by
  rw [gamCol_eq, dPart_eq]
  refine nc_sound _ _ _ _ _ _ _ bindQ_ok bindNC_ok (by quickRfl) inv_ok gamCol_ok fun d hd => ?_
  interval_cases d
  exacts [dPart_0, dPart_1, dPart_2, dPart_3, dPart_4, dPart_5, dPart_6, dPart_7]

end CertificateChecks.KernelGMS78

end
