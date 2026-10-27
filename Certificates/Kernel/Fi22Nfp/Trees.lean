module

public import Certificates.Kernel.Sporadic.OddCore.TBfsCmd
public import Certificates.Data.Kernel.Fi22.Orb
public meta import Certificates.Data.Kernel.Fi22.Orb
public meta import Certificates.Data.CFSGNative.Fi22.Nfp

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22N

open CFSG.Sporadic.Fi22.Native CFSG.Perm.Native CFSG.F3.Native CFSG.Sporadic.Th.Native

meta def orbT4 : COrbit := ⟨#[], orbTab 0, orbTab 1, orbTab 2, orbTab 3⟩

meta def tbM : Array Table := nfpBase.map (tabOf orbT4)

meta def lv1M : Array Nat := Array.range 1
meta def lv2M : Array Nat := Array.range 2
meta def lv3M : Array Nat := Array.range 3
meta def lv4M : Array Nat := Array.range 4
meta def lv5M : Array Nat := Array.range 5
meta def lv6M : Array Nat := Array.range 6

end CertificateChecks.KernelFi22N

#ktbfs CertificateChecks.KernelFi22N.NT1 3510 641 CertificateChecks.KernelFi22N.tbM
  CertificateChecks.KernelFi22N.lv1M
#ktbfs CertificateChecks.KernelFi22N.NT2 3510 641 CertificateChecks.KernelFi22N.tbM
  CertificateChecks.KernelFi22N.lv2M
#ktbfs CertificateChecks.KernelFi22N.NT3 3510 641 CertificateChecks.KernelFi22N.tbM
  CertificateChecks.KernelFi22N.lv3M
#ktbfs CertificateChecks.KernelFi22N.NT4 3510 641 CertificateChecks.KernelFi22N.tbM
  CertificateChecks.KernelFi22N.lv4M
#ktbfs CertificateChecks.KernelFi22N.NT5 3510 641 CertificateChecks.KernelFi22N.tbM
  CertificateChecks.KernelFi22N.lv5M
#ktbfs CertificateChecks.KernelFi22N.NT6 3510 641 CertificateChecks.KernelFi22N.tbM
  CertificateChecks.KernelFi22N.lv6M

end
