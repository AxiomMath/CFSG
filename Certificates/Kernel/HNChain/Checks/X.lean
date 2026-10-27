module

public import Certificates.Kernel.HNChain.Data
public import CFSG.Certificates.Kernel.Local.HN.X.Data
public import Certificates.Data.Kernel.SporSch.HNXBind
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelHNChain

open CFSG.KS.SporSch CFSG.KD.LgHNX

theorem tx0 : vecAt TX 0 CFSG.KD.HNChain.V0 = true := by quickRfl
theorem tx1 : vecAt TX 543953 CFSG.KD.HNChain.V1 = true := by quickRfl
theorem tx2 : vecAt TX 147358 CFSG.KD.HNChain.V2 = true := by quickRfl
theorem tx3 : vecAt TX 549971 CFSG.KD.HNChain.V3 = true := by quickRfl

theorem neg_tx1 : Bool.not (vecAt TX 543953 CFSG.KD.HNChain.V2) = true := by quickRfl
theorem neg_tx3 : Bool.not (vecAt TX 549970 CFSG.KD.HNChain.V3) = true := by quickRfl

end CertificateChecks.KernelHNChain

end
