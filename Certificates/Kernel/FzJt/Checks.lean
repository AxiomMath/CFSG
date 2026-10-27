module

public import Certificates.Data.Kernel.FzJt.Codes
import CFSG.Certificates.Kernel.Common.Eval
import CFSG.Certificates.Kernel.Common.Harness
meta import Certificates.Data.Kernel.FzJt.Twin

public section

namespace CertificateChecks.KernelFzJt

open Certificates.FzJt.K

#kc_eval CertificateChecks.KernelFzJt U64 Certificates.FzJt.Twin.f2 64
#kc_eval CertificateChecks.KernelFzJt U256 Certificates.FzJt.Twin.f2 256
#kc_eval CertificateChecks.KernelFzJt U338 Certificates.FzJt.Twin.f2 338
#kc_eval CertificateChecks.KernelFzJt U9 Certificates.FzJt.Twin.f2 9
#kc_eval CertificateChecks.KernelFzJt A64 Certificates.FzJt.Twin.f3 64
#kc_eval CertificateChecks.KernelFzJt A82 Certificates.FzJt.Twin.f3 82
#kc_eval CertificateChecks.KernelFzJt A256 Certificates.FzJt.Twin.f3 256
#kc_eval CertificateChecks.KernelFzJt A320 Certificates.FzJt.Twin.f3 320
#kc_eval CertificateChecks.KernelFzJt A274 Certificates.FzJt.Twin.f3 274
#kc_eval CertificateChecks.KernelFzJt A338 Certificates.FzJt.Twin.f3 338
#kc_eval CertificateChecks.KernelFzJt W Certificates.FzJt.Twin.f4

theorem ch441783f2_64 : f2B 64 U64.C U64.S U64.SV = true := by quickRfl
theorem ch441783f2_256 : f2B 256 U256.C U256.S U256.SV = true := by quickRfl
theorem ch441783f2_338 : f2B 338 U338.C U338.S U338.SV = true := by quickRfl
theorem ch441783f3_64 : f3B 64 A64.L = true := by quickRfl
theorem ch441783f3_82 : f3B 82 A82.L = true := by quickRfl
theorem ch441783f3_256 : f3B 256 A256.L = true := by quickRfl
theorem ch441783f3_320 : f3B 320 A320.L = true := by quickRfl
theorem ch441783f3_274 : f3B 274 A274.L = true := by quickRfl
theorem ch441783f3_338 : f3B 338 A338.L = true := by quickRfl
theorem ch441783f4 : f4B W.W = true := by quickRfl

theorem ch441783neg_f2J : f2B 9 U9.C U9.S U9.SV = false := by decide +kernel
theorem ch441783neg_f2rows : f2B 64 U64.C U64.S U64.SV.tail = false := by decide +kernel
theorem ch441783neg_f3 : f3L [592, 777] = false := by decide +kernel
theorem ch441783neg_f3list : f3B 64 A256.L = false := by decide +kernel
theorem ch441783neg_f4dom : f4B W.W.tail = false := by decide +kernel
theorem ch441783neg_f4wit : f4B (List.cons 0 W.W) = false := by decide +kernel

end CertificateChecks.KernelFzJt
