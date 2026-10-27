module

public import Certificates.Data.Kernel.OpsCubN
public import Certificates.Data.CFSGNative.CTP.StrongP
public import Certificates.Kernel.MatCert.Ly
public import Certificates.Kernel.TcGen.HN
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 100

namespace CertificateChecks.KernelMC.StrongPF5

open CFSG.SectionRank.Native CFSG.KC.OpsCubN CertificateChecks.KernelMC
open CertificateChecks.KernelSporSch CertificateChecks.KernelTc

theorem ly_K : cubicN OL LyBS.A LyBS.B lySylow5Data = true := by
  quickRfl

theorem hn_K : cubicN HN.O5 HN.A HN.B hnSylow5Data = true := by
  quickRfl

theorem ly_neg_seed : (!cubicN OL LyBS.B LyBS.A lySylow5Data) = true := by
  quickRfl

theorem ly_neg_r : (!cubicN OL LyBS.A LyBS.B { lySylow5Data with r := 4 }) = true := by
  quickRfl

theorem hn_neg_seed : (!cubicN HN.O5 HN.B HN.A hnSylow5Data) = true := by
  quickRfl

end CertificateChecks.KernelMC.StrongPF5

end
