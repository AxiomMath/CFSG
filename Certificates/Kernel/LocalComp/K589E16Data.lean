module

public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.LocalComp.BfsGen
meta import Certificates.Data.S1277Kt
meta import Certificates.Kernel.Sporadic.RawGen

namespace CertificateChecks.KernelLC.K589Gen

meta def b1G : List (Array Nat) := Certificates.Data.S1277Kt.ktGenB1.toList

meta def b2G : List (Array Nat) := Certificates.Data.S1277Kt.ktGenB2.toList

meta def k1P : Array (Array Nat) :=
  (Certificates.Data.S1277Kt.ktKs1 ()).map fun t => #[CFSG.KS.RawGen.pack 6 t]

meta def k2P : Array (Array Nat) :=
  (Certificates.Data.S1277Kt.ktKs2 ()).map fun t => #[CFSG.KS.RawGen.pack 6 t]

end CertificateChecks.KernelLC.K589Gen

public section

set_option maxRecDepth 400000

#lc_bfs CertificateChecks.KernelLC.K589B1 CertificateChecks.KernelLC.K589Gen.b1G 42 6
#lc_bfs CertificateChecks.KernelLC.K589B2 CertificateChecks.KernelLC.K589Gen.b2G 42 6

#kmisc_packarrs CertificateChecks.KernelLC.K589K1 CertificateChecks.KernelLC.K589Gen.k1P 8
#kmisc_packarrs CertificateChecks.KernelLC.K589K2 CertificateChecks.KernelLC.K589Gen.k2P 8

end
