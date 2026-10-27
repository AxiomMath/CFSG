module

public import Certificates.Data.Kernel.E8Seven
public import Certificates.Kernel.E8Seven.Data
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CertificateChecks.E8SevenK

open Certificates.E8Seven.K CFSG.KD.E8Seven

@[expose] noncomputable def c14972e2 (a : Nat) : Bool := chk t2 a

@[expose] noncomputable def c14972e4 (a : Nat) : Bool := chk t4 a

#kc_each c14972e2 0 7
#kc_each c14972e4 0 7

theorem c14972_neg2 : bN (chk t2.tail 1) = true := by quickRfl

theorem c14972_neg4 : bN (chk (t4.head! :: t4) 1) = true := by quickRfl

end CertificateChecks.E8SevenK
