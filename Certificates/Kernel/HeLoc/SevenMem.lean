module

public import Certificates.Kernel.HeLoc.SevenDefs
public import Certificates.Kernel.SporSch.Ru.RowsGen
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.MonsterB.BfsReplay
public import Certificates.Data.Kernel.SporSch.PairHeCnt

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHeLoc.Seven

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CertificateChecks.KernelSpor

theorem kPerm : allN 75 (fun k => permOK 8330 14 (mask 14) (8330 * 14) (A k) (AI k)) = true := by
  quickRfl

theorem kNF : allN 75 (fun k => bAnd(nfValidK 5 HeC.LR (NF.getD k 0), Nat.blt (FL.getD k 0) 2)) =
    true := by
  quickRfl

end CertificateChecks.KernelHeLoc.Seven

end
