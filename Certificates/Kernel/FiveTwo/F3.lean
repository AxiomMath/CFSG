module

public import Certificates.Data.Kernel.FiveTwoK
public import CFSG.RankThree.Native.FiveTwoData
public import Certificates.Kernel.TcGen.McL
public import Certificates.Kernel.TcGen.Suz
public import Certificates.Kernel.TcGen.ON
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelFT

open CFSG.KC.FiveTwoK CFSG.RankThree.Native

theorem mcl_K : fiveL KernelTc.McL.lay KernelTc.McL.A KernelTc.McL.B mclFiveTwo = true := by
  quickRfl

theorem suz_K : fiveL KernelTc.Suz.lay KernelTc.Suz.A KernelTc.Suz.B suzFiveTwo = true := by
  quickRfl

theorem on_K : fiveL KernelTc.ON.lay KernelTc.ON.A KernelTc.ON.B onFiveTwo = true := by
  quickRfl

end CertificateChecks.KernelFT

end
