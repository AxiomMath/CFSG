module

public import Certificates.Data.Kernel.Misc.RuScanL
public import Certificates.Kernel.Misc.RuScan.Data
public import Certificates.Kernel.Misc.RuScan.DataW
public import Certificates.Kernel.Misc.RuScan.DataL
public import Certificates.Kernel.SporSch.Ru.CData
import CFSG.Certificates.Kernel.Common.Each

public section

set_option Elab.async false

namespace CertificateChecks.KernelMisc.RuScan

open CFSG.KC.Misc.RuScan CertificateChecks.KernelSporSch

@[expose] noncomputable def ch7230l0_ (q : Nat) : Bool :=
  chkL3 RuCS.LR RuCS.TR W0 K0 V0 (HP 1) (HP 0) (Nat.mul 4096 q) 4096 (V0 (Nat.succ q)) (V0 q)

end CertificateChecks.KernelMisc.RuScan

#kc_each CertificateChecks.KernelMisc.RuScan.ch7230l0_ 0 60

end
