module

public import Certificates.Data.Kernel.OpsLayMcert
public import Certificates.Kernel.TcGen.ON
public import CFSG.RankThree.PartTwo.KFacts.HeringKS12ONData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

namespace CertificateChecks.KernelMC

open CFSG.KC.OpsLayK CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

theorem ks12ON_K : mcertL KernelTc.ON.lay KernelTc.ON.A KernelTc.ON.B
    CFSG.RankThree.PartTwo.KFacts.KS12ON.cert = true := by
  quickRfl

end CertificateChecks.KernelMC

end
