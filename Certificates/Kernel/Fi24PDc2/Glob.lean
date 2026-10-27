module

public import Certificates.Data.Kernel.Fi24PDc2.Defs
public import Certificates.Data.Kernel.SporLatDc2Check
public import Certificates.Kernel.Sporadic.Fi24K.C2077
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Fi24PDc2

open CFSG.KC.SLD2

theorem glob : globOK C D = true := by
  quickRfl

theorem borbs : (List.range D.bo.length).all (fun i => borbOK C D (D.bo.getD i default)) =
    true := by
  quickRfl

theorem rec1s : (List.range D.R1.length).all (fun c => rec1OK C D (D.R1.getD c default)) =
    true := by
  quickRfl

theorem frest : fRestOK C D = true := by
  quickRfl

theorem frows : (List.range C.nf).all (fRowOK C D) = true := by
  quickRfl

theorem rootIdx : rootIdxOK C D = true := by
  quickRfl

theorem shape : shapeOK = true := by
  quickRfl

theorem lets : letOK = true := by
  quickRfl

theorem sepB : (D.sep == [0, 1, 2, 5]) = true := by
  quickRfl

theorem sb : sbOK = true := by
  quickRfl

theorem sbSize : (SB.C.flatten.length == 256) = true := by
  quickRfl

theorem codes : (Nat.beq (LT.lc.getD 6 0) (CertificateChecks.KernelSpor.Fi24PC.S 0) &&
    Nat.beq (LT.lc.getD 7 0) (CertificateChecks.KernelSpor.Fi24PC.S 1)) = true := by
  quickRfl

end CFSG.KD.Fi24PDc2

end
