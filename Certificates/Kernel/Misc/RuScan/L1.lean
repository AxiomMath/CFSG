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

@[expose] noncomputable def ch7230l1_ (q : Nat) : Bool :=
  chkL3 RuCS.LR RuCS.TR W1 K1 V1 (HP 2) (HP 0) (Nat.mul 4096 q) 4096 (V1 (Nat.succ q)) (V1 q)

@[expose] noncomputable def ch7230l2_ (q : Nat) : Bool :=
  chkL3 RuCS.LR RuCS.TR W2 K2 V2 (HP 3) (HP 0) (Nat.mul 4096 q) 4096 (V2 (Nat.succ q)) (V2 q)

@[expose] noncomputable def ch7230l3_ (q : Nat) : Bool :=
  chkL3 RuCS.LR RuCS.TR W3 K3 V3 (HP 4) (HP 0) (Nat.mul 4096 q) 4096 (V3 (Nat.succ q)) (V3 q)

end CertificateChecks.KernelMisc.RuScan

#kc_each CertificateChecks.KernelMisc.RuScan.ch7230l1_ 0 60
#kc_each CertificateChecks.KernelMisc.RuScan.ch7230l2_ 0 60
#kc_each CertificateChecks.KernelMisc.RuScan.ch7230l3_ 0 60

end
