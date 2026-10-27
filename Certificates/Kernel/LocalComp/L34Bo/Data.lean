module

public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public import Certificates.Data.L34Borel
meta import Certificates.Data.L34Borel

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34BoG

open CFSG.PSL3Four.Native Certificates.L34Borel

meta def s0 : Array (Array Nat) := sylGens[0]!
meta def s1 : Array (Array Nat) := sylGens[1]!
meta def s2 : Array (Array Nat) := sylGens[2]!
meta def s3 : Array (Array Nat) := sylGens[3]!
meta def s4 : Array (Array Nat) := sylGens[4]!
meta def s5 : Array (Array Nat) := sylGens[5]!

meta def idM : Array Nat := idTab 42

meta def fixM : List Nat :=
  ((List.range 6).map fun j =>
    let T := (sylEnum j).tabs
    ((List.range 42).filter fun p => T.all fun t => t[p]! == p).take 2).flatten

end CertificateChecks.KernelLC.L34BoG

#knatlist CertificateChecks.KernelLC.L34BoG.FX CertificateChecks.KernelLC.L34BoG.fixM

#kpenum CertificateChecks.KernelLC.SY0 42 6 false CertificateChecks.KernelLC.L34BoG.s0
  CertificateChecks.KernelLC.L34BoG.s0 CertificateChecks.KernelLC.L34BoG.idM 64
#kpenum CertificateChecks.KernelLC.SY1 42 6 false CertificateChecks.KernelLC.L34BoG.s1
  CertificateChecks.KernelLC.L34BoG.s1 CertificateChecks.KernelLC.L34BoG.idM 64
#kpenum CertificateChecks.KernelLC.SY2 42 6 false CertificateChecks.KernelLC.L34BoG.s2
  CertificateChecks.KernelLC.L34BoG.s2 CertificateChecks.KernelLC.L34BoG.idM 64
#kpenum CertificateChecks.KernelLC.SY3 42 6 false CertificateChecks.KernelLC.L34BoG.s3
  CertificateChecks.KernelLC.L34BoG.s3 CertificateChecks.KernelLC.L34BoG.idM 64
#kpenum CertificateChecks.KernelLC.SY4 42 6 false CertificateChecks.KernelLC.L34BoG.s4
  CertificateChecks.KernelLC.L34BoG.s4 CertificateChecks.KernelLC.L34BoG.idM 64
#kpenum CertificateChecks.KernelLC.SY5 42 6 false CertificateChecks.KernelLC.L34BoG.s5
  CertificateChecks.KernelLC.L34BoG.s5 CertificateChecks.KernelLC.L34BoG.idM 64

end
