module

public import Certificates.Kernel.Sporadic.Fi24P7.Pt
import Certificates.Kernel.Sporadic.Fi24P7.O

public section

namespace CertificateChecks.KernelFi24P7

open CFSG.KC.Fi24FixS CFSG.KD.Fi24P7

theorem ok0_spec : ∀ j < 3159, ok0 j = true := chunk_spec O0.all (by norm_num)

theorem pr2_spec : ∀ k < 5670, pr2 k = true := chunk_spec Q2.all (by norm_num)

theorem pr4_spec : ∀ k < 44226, pr4 k = true := chunk_spec Q4.all (by norm_num)

theorem pt2_spec : ∀ j < 378, pt2 j = true := fun j hj => allBelow_spec P2.all (by norm_num) j hj

theorem pt4_spec : ∀ j < 351, pt4 j = true := fun j hj => allBelow_spec P4.all (by norm_num) j hj

end CertificateChecks.KernelFi24P7

end
