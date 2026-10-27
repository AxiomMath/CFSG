module

public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24TriData
public import CFSG.Assembly.Defs

public section

namespace CertificateChecks.KernelG24.Tri27206

open CFSG.EvenSporadicStandard.G24Aut CFSG.Monster.B.Co2.Native

meta def srcM : Array (Array Nat) :=
  let es := #[triA 0, triB 0, triA 1, triB 1, triA 2, triB 2, tAa, oa]
  es ++ (es.extract 0 6).map (invCand nn)

end CertificateChecks.KernelG24.Tri27206

#kmisc_packarrs CertificateChecks.KernelG24.Tri27206.PK CertificateChecks.KernelG24.Tri27206.srcM 11

end
