module

public import Certificates.Kernel.J2Fix280.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Fix280

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum
open CFSG.KC.B3S3K (cm)
open CFSG.RankThree.PartTwo.J2Residue.C280

theorem c111603W : szOK 315 9 = true := by quickRfl

theorem c111603P : permB 315 9 (AB 0) = true ∧ permB 315 9 (AB 1) = true ∧ permB 315 9 Z = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem c111603B : checkBK = true := by quickRfl

theorem c111603C : checkCK = true := by quickRfl

end CertificateChecks.KernelJ2Fix280

end
