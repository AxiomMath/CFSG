module

public import Certificates.Kernel.Fi22Twist.LvBlocks
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22Twist

theorem ch431009tf2 : ch431009tf2_ = true := by quickRfl

theorem ch431009rt : ch431009rt_ = true := by quickRfl

end CertificateChecks.KernelFi22Twist

#kc_each CertificateChecks.KernelFi22Twist.ch431009lv_ 0 120

#kc_each CertificateChecks.KernelFi22Twist.ch431009tp_ 0 14

#kc_each CertificateChecks.KernelFi22Twist.ch431009nd_ 0 212

end
