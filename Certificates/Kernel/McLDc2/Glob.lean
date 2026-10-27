module

public import Certificates.Data.Kernel.McLDc2.Defs
public import Certificates.Data.Kernel.SporLatDc2Check
public import Certificates.Kernel.Misc.Perm.HSMcL
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.McLDc2

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

theorem nR1 : Nat.beq D.R1.length 302 = true := by
  quickRfl

theorem nroots : Nat.beq D.roots.length 290 = true := by
  quickRfl

theorem shape : shapeOK = true := by
  quickRfl

theorem lets : letOK = true := by
  quickRfl

theorem sepB : (D.sep == [0, 1, 2, 3, 4]) = true := by
  quickRfl

theorem sb : sbOK = true := by
  quickRfl

theorem sbSize : (SB.C.flatten.length == 128) = true := by
  quickRfl

theorem codes : (Nat.beq (LT.lc.getD 5 0) (CertificateChecks.KernelMisc.HSMcL.MS.F 0) &&
    Nat.beq (LT.lc.getD 6 0) (CertificateChecks.KernelMisc.HSMcL.MS.F 1)) = true := by
  quickRfl

end CFSG.KD.McLDc2

end
