module

public import Certificates.Kernel.Fi24.Chain
import Certificates.Kernel.Co2.Intro
import Certificates.Kernel.Fi24.FactsF1
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Fi24.Slices.Bind
import CFSG.Certificates.Kernel.Fi24.Slices.Head1

public section

namespace CertificateChecks.KernelFi24

open CFSG.KC CFSG.KC.LceS CFSG.Certificates CFSG.Certificates.LCE CertificateChecks.KernelCo2

theorem s1 : Tab g0 CFSG.KD.F1.selST (nat_lit 10) (nat_lit 24) (nat_lit 306936) :=
  lceOk_sound (lceOk_intro CFSG.KD.F1.sH1 CFSG.KD.F1.sH0 CFSG.KD.Fi24B.bHF1 CFSG.KD.F1.sH2
    CFSG.KD.F1.sH3 (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)
    F1facts (by quickRfl) (by quickRfl) F1cover (by quickRfl)) g0 r1

end CertificateChecks.KernelFi24

end
