module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
import Certificates.Kernel.Sporadic.OddCore.RowsCmd
import Certificates.Kernel.Sporadic.RowsWCmd
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Data.Kernel.MaxD2.Gen
meta import CFSG.LocalAnalysis.StandardType.TitsThreeOvergroupData
import Certificates.Data.Kernel.MaxD2.Gen
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD

namespace CertificateChecks.KernelTitsOver.Three

open CFSG.KS.MaxD2 Certificates.MaxD2Perm CFSG.StandardType.TitsThree

meta def c0D : Data := lLocalData 0 ()

meta def c0rG : Array (Array Nat) := rGens c0D
meta def c0nG : Array (Array Nat) := nGens c0D
meta def c0idT : Array Nat := CFSG.PSL3Four.Native.idTab 1755

meta def c0preM : Gen.Pre := Gen.pre c0D 11

meta def c0ngiM : Array (Array Nat) := nGensI c0D
meta def c0repM : Array (Array Nat) := c0preM.rep
meta def c0repiM : Array (Array Nat) := c0preM.repi
meta def c0ttM : Array (Array Nat) :=
  #[wT c0D c0D.tW, CFSG.PSL3Four.Native.invTab 1755 (wT c0D c0D.tW)]
meta def c0ptM : Array Nat := c0D.fpPts.toArray
meta def c0fsM : Array Nat := Gen.fpSort c0preM
meta def c0ksM : Array Nat := Gen.fpKeys c0preM
meta def c0rbM : Array Nat := Gen.repImgs c0D c0preM
meta def c0hM : Array Nat := Gen.hints c0D 11 c0preM
meta def c0cnM : Array Nat := Gen.counts c0D 11 c0preM
meta def c0chM : Array Nat := Gen.centHints c0D c0preM
meta def c0nhM : Array Nat := Gen.normHints c0D c0preM
meta def c0lM : Array Nat := Gen.labels c0D
meta def c0mkM : Array Nat := Gen.mkeys c0D 11 c0preM
meta def c0miscM : Array Nat := #[Gen.torusPos c0D c0preM, Gen.numLabels c0D]

end CertificateChecks.KernelTitsOver.Three

public section

#kpenum CertificateChecks.KernelTitsOver.Three.C0RE 1755 11 false CertificateChecks.KernelTitsOver.Three.c0rG
  CertificateChecks.KernelTitsOver.Three.c0rG CertificateChecks.KernelTitsOver.Three.c0idT 9
#kpenum CertificateChecks.KernelTitsOver.Three.C0NE 1755 11 false CertificateChecks.KernelTitsOver.Three.c0nG
  CertificateChecks.KernelTitsOver.Three.c0nG CertificateChecks.KernelTitsOver.Three.c0idT 432
#kmisc_packarrs CertificateChecks.KernelTitsOver.Three.C0NGI
  CertificateChecks.KernelTitsOver.Three.c0ngiM 11
#kmisc_packarrs CertificateChecks.KernelTitsOver.Three.C0REP
  CertificateChecks.KernelTitsOver.Three.c0repM 11
#kmisc_packarrs CertificateChecks.KernelTitsOver.Three.C0REPI
  CertificateChecks.KernelTitsOver.Three.c0repiM 11
#kmisc_packarrs CertificateChecks.KernelTitsOver.Three.C0TT CertificateChecks.KernelTitsOver.Three.c0ttM 11
#krows CertificateChecks.KernelTitsOver.Three.C0PT CertificateChecks.KernelTitsOver.Three.c0ptM
#krows CertificateChecks.KernelTitsOver.Three.C0FS CertificateChecks.KernelTitsOver.Three.c0fsM
#krowsw CertificateChecks.KernelTitsOver.Three.C0KS 11 CertificateChecks.KernelTitsOver.Three.c0ksM
#krows CertificateChecks.KernelTitsOver.Three.C0RB CertificateChecks.KernelTitsOver.Three.c0rbM
#krows CertificateChecks.KernelTitsOver.Three.C0H CertificateChecks.KernelTitsOver.Three.c0hM
#krows CertificateChecks.KernelTitsOver.Three.C0CN CertificateChecks.KernelTitsOver.Three.c0cnM
#krows CertificateChecks.KernelTitsOver.Three.C0CH CertificateChecks.KernelTitsOver.Three.c0chM
#krows CertificateChecks.KernelTitsOver.Three.C0NH CertificateChecks.KernelTitsOver.Three.c0nhM
#krows CertificateChecks.KernelTitsOver.Three.C0L CertificateChecks.KernelTitsOver.Three.c0lM
#krowsw CertificateChecks.KernelTitsOver.Three.C0MK 1024 CertificateChecks.KernelTitsOver.Three.c0mkM
#krows CertificateChecks.KernelTitsOver.Three.C0MISC CertificateChecks.KernelTitsOver.Three.c0miscM

end
