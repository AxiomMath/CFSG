module

public import Certificates.Data.Kernel.Misc.RuScanB
public import Certificates.Kernel.Misc.RuScan.Data
public import Certificates.Kernel.Misc.RuScan.DataW
import CFSG.Certificates.Kernel.Common.Each

public section

set_option Elab.async false

namespace CertificateChecks.KernelMisc.RuScan

open CFSG.KC.Misc.RuScan

@[expose] noncomputable def ch7230b0_ (q : Nat) : Bool := bndK W0 (Nat.mul 16384 q) 16384
@[expose] noncomputable def ch7230b1_ (q : Nat) : Bool := bndK W1 (Nat.mul 16384 q) 16384
@[expose] noncomputable def ch7230b2_ (q : Nat) : Bool := bndK W2 (Nat.mul 16384 q) 16384
@[expose] noncomputable def ch7230b3_ (q : Nat) : Bool := bndK W3 (Nat.mul 16384 q) 16384
@[expose] noncomputable def ch7230b6_ (q : Nat) : Bool := bndK W6 (Nat.mul 16640 q) 16640
@[expose] noncomputable def ch7230b7_ (q : Nat) : Bool := bndK W7 (Nat.mul 16640 q) 16640
@[expose] noncomputable def ch7230b8_ (q : Nat) : Bool := bndK W8 (Nat.mul 16640 q) 16640

end CertificateChecks.KernelMisc.RuScan

#kc_each CertificateChecks.KernelMisc.RuScan.ch7230b0_ 0 15
#kc_each CertificateChecks.KernelMisc.RuScan.ch7230b1_ 0 15
#kc_each CertificateChecks.KernelMisc.RuScan.ch7230b2_ 0 15
#kc_each CertificateChecks.KernelMisc.RuScan.ch7230b3_ 0 15
#kc_each CertificateChecks.KernelMisc.RuScan.ch7230b6_ 0 7
#kc_each CertificateChecks.KernelMisc.RuScan.ch7230b7_ 0 7
#kc_each CertificateChecks.KernelMisc.RuScan.ch7230b8_ 0 7

end
