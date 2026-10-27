module

public import Certificates.Data.Kernel.Misc.RuScanL
public import Certificates.Kernel.Misc.RuScan.Data
public import Certificates.Kernel.Misc.RuScan.DataW
public import Certificates.Kernel.Misc.RuScan.DataL
public import Certificates.Kernel.SporSch.Ru.LChain
public import Certificates.Kernel.SporSch.Ru.Text4060
import CFSG.Certificates.Kernel.Common.Each

public section

set_option Elab.async false

namespace CertificateChecks.KernelMisc.RuScan

open CFSG.KC.Misc.RuScan CertificateChecks.KernelSporSch

@[expose] noncomputable def ch7230l8_ (q : Nat) : Bool :=
  chkL2 RuLS.LR RuLS.TR W8 K8 V8 (HP 9) (RuT4060.L 0) (Nat.mul 4160 q) 4160 (V8 (Nat.succ q))
    (V8 q)

end CertificateChecks.KernelMisc.RuScan

#kc_each CertificateChecks.KernelMisc.RuScan.ch7230l8_ 0 28

end
