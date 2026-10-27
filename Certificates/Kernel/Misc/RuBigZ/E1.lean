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

@[expose] noncomputable def ch7233e1_ (q : Nat) : Bool :=
  elChk RuCS.LR RuCS.TR R Q AL1 EL1 1 (Nat.mul 32 q) 32

@[expose] noncomputable def ch7233e2_ (q : Nat) : Bool :=
  elChk RuCS.LR RuCS.TR R Q AL2 EL2 2 (Nat.mul 32 q) 32

end CertificateChecks.KernelMisc.RuBigZ

#kc_each CertificateChecks.KernelMisc.RuBigZ.ch7233e1_ 0 2
#kc_each CertificateChecks.KernelMisc.RuBigZ.ch7233e2_ 0 4

end
