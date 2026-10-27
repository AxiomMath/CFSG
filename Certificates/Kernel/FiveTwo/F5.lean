module

public import Certificates.Data.Kernel.FiveTwoK
public import CFSG.RankThree.Native.FiveTwoData
public import Certificates.Kernel.TcGen.HN
public import Certificates.Kernel.MatCert.Ly
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelFT

open CFSG.KC.FiveTwoK CFSG.RankThree.Native

theorem hn_K : fiveN KernelTc.HN.O5 KernelTc.HN.A KernelTc.HN.B hnFiveTwo = true := by
  quickRfl

theorem ly_K : fiveN KernelMC.OL KernelSporSch.LyBS.A KernelSporSch.LyBS.B lyFiveTwo = true := by
  quickRfl

end CertificateChecks.KernelFT

end
