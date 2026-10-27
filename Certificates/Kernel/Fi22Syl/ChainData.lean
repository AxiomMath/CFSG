module

public import Certificates.Kernel.Sporadic.OddCore.TBfsCmd
public import Certificates.Data.Kernel.Fi22.Orb
public meta import Certificates.Data.Kernel.Fi22.Orb
public meta import Certificates.Data.CFSGNative.Fi22.Classes

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22S

open CFSG.Sporadic.Fi22.Native CFSG.Perm.Native CFSG.F3.Native CFSG.Sporadic.Th.Native

meta def orbT4 : COrbit := ⟨#[], orbTab 0, orbTab 1, orbTab 2, orbTab 3⟩

meta def lettersM : Array Table := sylLetters (chainLetters orbT4)

meta def lv0M : Array Nat := levelLetters lettersM sylBase 0
meta def lv1M : Array Nat := levelLetters lettersM sylBase 1

end CertificateChecks.KernelFi22S

#ktbfs CertificateChecks.KernelFi22S.ST0 3510 0 CertificateChecks.KernelFi22S.lettersM
  CertificateChecks.KernelFi22S.lv0M
#ktbfs CertificateChecks.KernelFi22S.ST1 3510 3 CertificateChecks.KernelFi22S.lettersM
  CertificateChecks.KernelFi22S.lv1M

end
