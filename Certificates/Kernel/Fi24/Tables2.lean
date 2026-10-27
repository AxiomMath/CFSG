module

public import Certificates.Kernel.Fi24.Chain
import Certificates.Kernel.Co2.Intro
import Certificates.Kernel.Fi24.FactsF2
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Fi24.Slices.Bind
import CFSG.Certificates.Kernel.Fi24.Slices.Head2

public section

namespace CertificateChecks.KernelFi24

open CFSG.KC CFSG.KC.LceS CFSG.Certificates CFSG.Certificates.LCE CertificateChecks.KernelCo2

theorem s2 : Tab cg2 CFSG.KD.F2.selST (nat_lit 9) (nat_lit 20) (nat_lit 825792) :=
  lceOk_sound (lceOk_intro CFSG.KD.F2.sH1 CFSG.KD.F2.sH0 CFSG.KD.Fi24B.bHF2 CFSG.KD.F2.sH2
    CFSG.KD.F2.sH3 (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)
    F2facts (by quickRfl) (by quickRfl) F2cover (by quickRfl)) cg2 r2

end CertificateChecks.KernelFi24

end
