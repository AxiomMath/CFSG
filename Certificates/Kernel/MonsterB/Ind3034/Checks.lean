
module

public import Certificates.Data.Kernel.Ind3034K
public import Certificates.Kernel.MonsterB.IndOrbData
public import Certificates.Kernel.MonsterB.IndTransData
public import Certificates.Kernel.MonsterB.Diag3031Data
public import Certificates.Kernel.MonsterB.Ind3034.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KC.Ind3034

open CertificateChecks.KernelMonB

theorem kX : chkX IG.F = true := by quickRfl

theorem kW : chkW IG.F = true := by quickRfl

theorem kT : chkT ITr.F = true := by quickRfl

theorem kS : chkS ITr.F = true := by quickRfl

theorem kZ : zFrom IG.F (SortTree.recT CertificateChecks.Diag3031.R 6 292) CFSG.KD.I3034.W.c0 0 =
    true := by quickRfl

end CFSG.KC.Ind3034

end
