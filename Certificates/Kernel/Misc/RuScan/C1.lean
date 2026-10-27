module

public import Certificates.Data.Kernel.Misc.RuScanD
public import Certificates.Kernel.Misc.RuScan.Data
public import Certificates.Kernel.Misc.RuScan.DataW
public import Certificates.Kernel.SporSch.Ru.CData
import CFSG.Certificates.Kernel.Common.Each

public section

set_option Elab.async false

namespace CertificateChecks.KernelMisc.RuScan

open CFSG.KC.Misc.RuScan CertificateChecks.KernelSporSch

@[expose] noncomputable def ch7230c1_ (q : Nat) : Bool :=
  chk3D RuCS.LR RuCS.TR W1 (HP 2) (HP 0) (Nat.mul 4096 q) 4096

end CertificateChecks.KernelMisc.RuScan

#kc_each CertificateChecks.KernelMisc.RuScan.ch7230c1_ 0 60

end
