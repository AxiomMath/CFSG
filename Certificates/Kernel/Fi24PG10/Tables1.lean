module

public import Certificates.Kernel.Fi24PG10.Tables
import Certificates.Kernel.Co2.Intro
import Certificates.Kernel.Fi24PG10.Facts1
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Fi24.PG10.Slices.Head1

public section

namespace CertificateChecks.KernelPG10

open CFSG.KC CFSG.KC.LceS CFSG.Certificates CFSG.Certificates.LCE CertificateChecks.KernelCo2

theorem t1 : Tab (gen A1) CFSG.KD.PG10P1.selST (nat_lit 9) (nat_lit 20) (nat_lit 825792) :=
  lceOk_sound (lceOk_intro CFSG.KD.PG10P1.sH1 CFSG.KD.PG10P1.sH0 (by quickRfl) CFSG.KD.PG10P1.sH2
    CFSG.KD.PG10P1.sH3 (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)
    P1facts (by quickRfl) (by quickRfl) P1cover (by quickRfl)) (gen A1) r1

end CertificateChecks.KernelPG10

end
