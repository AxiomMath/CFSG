module

public import Certificates.Data.Kernel.LyModel.Range
public import Certificates.Kernel.LyBenes.Data

set_option profiler true
set_option profiler.threshold 100

public section

namespace CertificateChecks.KernelLyModel

open CFSG.KC.LyModel CertificateChecks.KernelLyB

theorem ly6110_range0 : rangeOK 66825 (NS 0) = true := by decide +kernel

theorem ly6110_range1 : rangeOK 66825 (NS 1) = true := by decide +kernel

end CertificateChecks.KernelLyModel

end
