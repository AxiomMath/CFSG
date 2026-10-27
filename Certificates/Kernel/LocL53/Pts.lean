module

public import Certificates.Kernel.LocL53.Data
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kc_each CertificateChecks.KernelLocL53.l53Pt 0 16

#kc_each CertificateChecks.KernelLocL53.l53Fl 0 16

namespace CertificateChecks.KernelLocL53

open CFSG.KD.LocLn

theorem kit5 : kitOK k5 = true := by quickRfl

theorem o8B : ((List.range 1024).filter (fun i => Nat.beq (Nat.mod (F i) 2) 1) ==
    (List.range 416).map O8) = true := by
  quickRfl

theorem o2B : ((List.range 1024).filter (fun i => Nat.beq (Nat.div (F i) 2) 1) ==
    (List.range 167).map O2) = true := by
  quickRfl

end CertificateChecks.KernelLocL53

end
