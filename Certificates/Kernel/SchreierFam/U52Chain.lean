module

public import Certificates.Data.GrSLitL34FactsCF23U52Data
public import Certificates.Data.Kernel.Misc.ArrEnum
public import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Data.GrSLitL34FactsCF23U52Data
import CFSG.Certificates.Kernel.Common.Harness
import all CFSG.Fischer.F4
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelSchreierFam

@[expose] def dU52 : List (List ℤ) := CFSG.ComponentClassification.GSThmB.U52.chainW.toList.drop 2

end CertificateChecks.KernelSchreierFam

end

#ks_rawchain CertificateChecks.KernelSchreierFam.U52 341 9 16
  CFSG.ComponentClassification.GSThmB.U52.chainS CFSG.ComponentClassification.GSThmB.U52.baseArr 2
  CertificateChecks.KernelSchreierFam.dU52

public section

namespace CertificateChecks.KernelSchreierFam.U52

open CFSG.ComponentClassification.GSThmB.U52 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum

theorem bS : ∀ j < 9, arrBind chainS[j]! 341 9 (S j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem perm : allN 9 (fun j => permOK 341 9 (mask 9) (341 * 9) (S j) (SI j)) = true := by
  quickRfl

theorem bget : ∀ t < 5, baseArr[t]! = pg 9 (mask 9) BP t := by decide +kernel

theorem orbProd : ((List.range 5).map fun i => rcnt (LR i)).prod = 13685760 := by decide +kernel

theorem hNS : 341 ≤ NS * 16 := by decide +kernel

end CertificateChecks.KernelSchreierFam.U52
