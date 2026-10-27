module

public import Certificates.Data.Kernel.Misc.RuScan
public import Certificates.Kernel.Misc.RuScan.Data
public import Certificates.Kernel.SporSch.Ru.LChain
public import Certificates.Kernel.SporSch.Ru.Text4060
import CFSG.Certificates.Kernel.Common.Each

public section

set_option Elab.async false

namespace CertificateChecks.KernelMisc.RuScan

open CFSG.KC.Misc.RuScan CertificateChecks.KernelSporSch

@[expose] noncomputable def ch7230c6_ (q : Nat) : Bool :=
  chk2 RuLS.LR RuLS.TR W6 (HP 7) (RuT4060.L 0) (Nat.mul 4160 q) 4160

end CertificateChecks.KernelMisc.RuScan

#kc_each CertificateChecks.KernelMisc.RuScan.ch7230c6_ 0 28

end
