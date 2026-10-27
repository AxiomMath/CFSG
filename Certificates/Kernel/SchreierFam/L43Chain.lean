module

public import Certificates.Data.CatFactsL4U4P1L43Data
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1CentTriv
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import Certificates.Data.Kernel.Misc.ArrEnum
public import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Data.CatFactsL4U4P1L43Data
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
public import Mathlib

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelSchreierFam

@[expose] def dL43 : List (List ℤ) :=
  CFSG.ComponentClassification.HarrisLit.P1.L43.chainW.toList.drop 2

end CertificateChecks.KernelSchreierFam

end

#ks_rawchain CertificateChecks.KernelSchreierFam.L43 80 7 16
  CFSG.ComponentClassification.HarrisLit.P1.L43.chainS
  CFSG.ComponentClassification.HarrisLit.P1.L43.baseArr 2
  CertificateChecks.KernelSchreierFam.dL43

public section

namespace CertificateChecks.KernelSchreierFam.L43

open CFSG.ComponentClassification.HarrisLit.P1 CFSG.ComponentClassification.HarrisLit.P1.L43
  CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.Sporadic.SmallOddCore.Native

theorem bS : ∀ j < 11, arrBind chainS[j]! 80 7 (S j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem perm : allN 11 (fun j => permOK 80 7 (mask 7) (80 * 7) (S j) (SI j)) = true := by
  quickRfl

theorem bget : ∀ t < 6, baseArr[t]! = pg 7 (mask 7) BP t := by decide +kernel

theorem orbProd : ((List.range 6).map fun i => rcnt (LR i)).prod = 6065280 := by decide +kernel

theorem hNS : 80 ≤ NS * 16 := by decide +kernel

@[expose] noncomputable def siftL43 (T : CFSG.Sporadic.Th.Native.Table) : Bool :=
  arrBind (natArr T) 80 7 (packL 7 (natArr T).toList).1 &&
    allN 80 (fun i => Nat.blt (pg 7 (mask 7) (packL 7 (natArr T).toList).1 i) 80) &&
    Nat.beq (Nat.shiftRight (packL 7 (natArr T).toList).1 (80 * 7)) 0 &&
    siftK 80 7 (mask 7) (80 * 7) (pidn 80 7) LR TRI BP 6 0 (packL 7 (natArr T).toList).1

theorem centK : centTrivOK 80 siftL43 l43CentTriv = true := by decide +kernel

theorem centNeg : centTrivOK 80 siftL43 l43CentTriv.dropLast = false := by decide +kernel

end CertificateChecks.KernelSchreierFam.L43
