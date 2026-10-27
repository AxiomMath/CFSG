module

public import Certificates.Data.Kernel.Misc.RuBigZ
public import Certificates.Kernel.Misc.RuBigZ.Data
public import Certificates.Kernel.SporSch.Ru.CData
import CFSG.Certificates.Kernel.Common.Each

public section

set_option Elab.async false

namespace CertificateChecks.KernelMisc.RuBigZ

open CFSG.KC.Misc.RuBigZ CertificateChecks.KernelSporSch

@[expose] noncomputable def ch7233l0_ (q : Nat) : Bool :=
  l0Chk RuCS.LR RuCS.TR R L (Nat.mul 480 q) 480

end CertificateChecks.KernelMisc.RuBigZ

#kc_each CertificateChecks.KernelMisc.RuBigZ.ch7233l0_ 0 4

end
