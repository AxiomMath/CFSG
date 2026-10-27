module

public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Data.TabFi22Cent
public meta import Certificates.Data.TabFi22Cent

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.Fi22LT
  CFSG.HardMathSupport.Dickson.I271.TabFi22Cent.hex
#kmisc_hexflat CertificateChecks.KernelSpor.Fi22LT
  CFSG.HardMathSupport.Dickson.I271.TabFi22Cent.hex 3 3510 12 10

namespace CertificateChecks.KernelSpor.Fi22LD

meta def S : Array (Array Nat) := CFSG.HardMathSupport.Dickson.I271.TabFi22Cent.lArrs ()

meta def B : Array Nat := #[19, 2, 3, 0, 1, 6, 4]

@[expose] def D : List (List Int) :=
  CFSG.HardMathSupport.Dickson.I271.TabFi22Cent.lWords.toList.drop 2

end CertificateChecks.KernelSpor.Fi22LD

end
