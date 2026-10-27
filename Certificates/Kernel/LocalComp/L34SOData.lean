module

public import Certificates.Kernel.LocalComp.L34SOGen
public import Certificates.Kernel.LocalComp.L34SData
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.LocalComp.BfsGen
meta import Certificates.Kernel.LocalComp.L34SOGen
meta import Certificates.Data.S1277Kt

namespace CertificateChecks.KernelLC.K589Gen

meta def e1G : List (Array Nat) := Certificates.Data.S1277Kt.ktGenE1.toList

meta def e2G : List (Array Nat) := Certificates.Data.S1277Kt.ktGenE2.toList

end CertificateChecks.KernelLC.K589Gen

public section

set_option maxRecDepth 400000

#kmisc_packarrs CertificateChecks.KernelLC.L34SO.TP CertificateChecks.KernelLC.L34SOGen.oST 252
#kmisc_packarrs CertificateChecks.KernelLC.L34SO.EP CertificateChecks.KernelLC.L34SOGen.oSE 33
#kmisc_packarrs CertificateChecks.KernelLC.L34SO.SP CertificateChecks.KernelLC.L34SOGen.oSS 18
#kmisc_packarrs CertificateChecks.KernelLC.L34SO.SIP CertificateChecks.KernelLC.L34SOGen.oSSI 18

#lc_bfs CertificateChecks.KernelLC.K589E1 CertificateChecks.KernelLC.K589Gen.e1G 42 6
#lc_bfs CertificateChecks.KernelLC.K589E2 CertificateChecks.KernelLC.K589Gen.e2G 42 6

namespace CertificateChecks.KernelLC

open CertificateChecks.KernelLC.L34X

@[expose] noncomputable def L34SO.T (i : Nat) : Nat := at8 L34SO.TP (nat_lit 252) i
@[expose] noncomputable def L34SO.E (i : Nat) : Nat := at16 L34SO.EP (nat_lit 33) i
@[expose] noncomputable def L34SO.S (i : Nat) : Nat := at16 L34SO.SP (nat_lit 18) i
@[expose] noncomputable def L34SO.SI (i : Nat) : Nat := at16 L34SO.SIP (nat_lit 18) i

end CertificateChecks.KernelLC

end
