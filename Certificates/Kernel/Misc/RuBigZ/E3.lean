module

public import Certificates.Data.Kernel.Misc.RuBigZE
public import Certificates.Kernel.Misc.RuBigZ.Data
public import Certificates.Kernel.Misc.RuBigZ.DataE
public import Certificates.Kernel.SporSch.Ru.CData
import CFSG.Certificates.Kernel.Common.Each

public section

set_option Elab.async false

namespace CertificateChecks.KernelMisc.RuBigZ

open CFSG.KC.Misc.RuBigZ CertificateChecks.KernelSporSch

@[expose] noncomputable def ch7233e3_ (q : Nat) : Bool :=
  elChk RuCS.LR RuCS.TR R Q AL3 EL3 3 (Nat.mul 32 q) 32

@[expose] noncomputable def ch7233e4_ (q : Nat) : Bool :=
  elChk RuCS.LR RuCS.TR R Q AL4 EL4 4 (Nat.mul 32 q) 32

end CertificateChecks.KernelMisc.RuBigZ

#kc_each CertificateChecks.KernelMisc.RuBigZ.ch7233e3_ 0 4
#kc_each CertificateChecks.KernelMisc.RuBigZ.ch7233e4_ 0 2

end
