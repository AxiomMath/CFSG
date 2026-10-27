module

public import Certificates.Data.Kernel.Misc.RuScanB
public import Certificates.Kernel.Misc.RuScan.DataL
import CFSG.Certificates.Kernel.Common.Each

public section

set_option Elab.async false

namespace CertificateChecks.KernelMisc.RuScan

open CFSG.KC.Misc.RuScan

@[expose] noncomputable def ch7230k0_ (q : Nat) : Bool := kbndK K0 (Nat.mul 8192 q) 8192
@[expose] noncomputable def ch7230k1_ (q : Nat) : Bool := kbndK K1 (Nat.mul 8192 q) 8192
@[expose] noncomputable def ch7230k2_ (q : Nat) : Bool := kbndK K2 (Nat.mul 8192 q) 8192
@[expose] noncomputable def ch7230k3_ (q : Nat) : Bool := kbndK K3 (Nat.mul 8192 q) 8192
@[expose] noncomputable def ch7230k8_ (q : Nat) : Bool := kbndK K8 (Nat.mul 8192 q) 8192

end CertificateChecks.KernelMisc.RuScan

#kc_each CertificateChecks.KernelMisc.RuScan.ch7230k0_ 0 96
#kc_each CertificateChecks.KernelMisc.RuScan.ch7230k1_ 0 34
#kc_each CertificateChecks.KernelMisc.RuScan.ch7230k2_ 0 2
#kc_each CertificateChecks.KernelMisc.RuScan.ch7230k3_ 0 12
#kc_each CertificateChecks.KernelMisc.RuScan.ch7230k8_ 0 3

end
