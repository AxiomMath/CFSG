module

public import Certificates.Kernel.Sporadic.OddCore.TBfsCmd
public import Certificates.Data.Kernel.Fi22.Orb
public meta import Certificates.Data.Kernel.Fi22.Orb

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22C

open CFSG.Sporadic.Fi22.Native CFSG.Perm.Native CFSG.F3.Native CFSG.Sporadic.Th.Native

meta def orbT4 : COrbit := ⟨#[], orbTab 0, orbTab 1, orbTab 2, orbTab 3⟩

meta def lettersM : Array Table := chainLetters orbT4

meta def lv0M : Array Nat := levelLetters lettersM chainBase 0
meta def lv1M : Array Nat := levelLetters lettersM chainBase 1
meta def lv2M : Array Nat := levelLetters lettersM chainBase 2
meta def lv3M : Array Nat := levelLetters lettersM chainBase 3
meta def lv4M : Array Nat := levelLetters lettersM chainBase 4

end CertificateChecks.KernelFi22C

#ktbfs CertificateChecks.KernelFi22C.CT0 3510 0 CertificateChecks.KernelFi22C.lettersM
  CertificateChecks.KernelFi22C.lv0M
#ktbfs CertificateChecks.KernelFi22C.CT1 3510 1 CertificateChecks.KernelFi22C.lettersM
  CertificateChecks.KernelFi22C.lv1M
#ktbfs CertificateChecks.KernelFi22C.CT2 3510 6 CertificateChecks.KernelFi22C.lettersM
  CertificateChecks.KernelFi22C.lv2M
#ktbfs CertificateChecks.KernelFi22C.CT3 3510 11 CertificateChecks.KernelFi22C.lettersM
  CertificateChecks.KernelFi22C.lv3M
#ktbfs CertificateChecks.KernelFi22C.CT4 3510 3 CertificateChecks.KernelFi22C.lettersM
  CertificateChecks.KernelFi22C.lv4M
#ktbfs CertificateChecks.KernelFi22C.T2 3510 8 CertificateChecks.KernelFi22C.lettersM
  CertificateChecks.KernelFi22C.lv1M

end
