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

meta def c1D : Data := lLocalData 1 ()

meta def c1rG : Array (Array Nat) := rGens c1D
meta def c1nG : Array (Array Nat) := nGens c1D
meta def c1idT : Array Nat := CFSG.PSL3Four.Native.idTab 1755

meta def c1preM : Gen.Pre := Gen.pre c1D 11

meta def c1ngiM : Array (Array Nat) := nGensI c1D
meta def c1repM : Array (Array Nat) := c1preM.rep
meta def c1repiM : Array (Array Nat) := c1preM.repi
meta def c1ttM : Array (Array Nat) :=
  #[wT c1D c1D.tW, CFSG.PSL3Four.Native.invTab 1755 (wT c1D c1D.tW)]
meta def c1ptM : Array Nat := c1D.fpPts.toArray
meta def c1fsM : Array Nat := Gen.fpSort c1preM
meta def c1ksM : Array Nat := Gen.fpKeys c1preM
meta def c1rbM : Array Nat := Gen.repImgs c1D c1preM
meta def c1hM : Array Nat := Gen.hints c1D 11 c1preM
meta def c1cnM : Array Nat := Gen.counts c1D 11 c1preM
meta def c1chM : Array Nat := Gen.centHints c1D c1preM
meta def c1nhM : Array Nat := Gen.normHints c1D c1preM
meta def c1lM : Array Nat := Gen.labels c1D
meta def c1mkM : Array Nat := Gen.mkeys c1D 11 c1preM
meta def c1miscM : Array Nat := #[Gen.torusPos c1D c1preM, Gen.numLabels c1D]

end CertificateChecks.KernelTitsOver.Three

public section

#kpenum CertificateChecks.KernelTitsOver.Three.C1RE 1755 11 false CertificateChecks.KernelTitsOver.Three.c1rG
  CertificateChecks.KernelTitsOver.Three.c1rG CertificateChecks.KernelTitsOver.Three.c1idT 9
#kpenum CertificateChecks.KernelTitsOver.Three.C1NE 1755 11 false CertificateChecks.KernelTitsOver.Three.c1nG
  CertificateChecks.KernelTitsOver.Three.c1nG CertificateChecks.KernelTitsOver.Three.c1idT 432
#kmisc_packarrs CertificateChecks.KernelTitsOver.Three.C1NGI
  CertificateChecks.KernelTitsOver.Three.c1ngiM 11
#kmisc_packarrs CertificateChecks.KernelTitsOver.Three.C1REP
  CertificateChecks.KernelTitsOver.Three.c1repM 11
#kmisc_packarrs CertificateChecks.KernelTitsOver.Three.C1REPI
  CertificateChecks.KernelTitsOver.Three.c1repiM 11
#kmisc_packarrs CertificateChecks.KernelTitsOver.Three.C1TT CertificateChecks.KernelTitsOver.Three.c1ttM 11
#krows CertificateChecks.KernelTitsOver.Three.C1PT CertificateChecks.KernelTitsOver.Three.c1ptM
#krows CertificateChecks.KernelTitsOver.Three.C1FS CertificateChecks.KernelTitsOver.Three.c1fsM
#krowsw CertificateChecks.KernelTitsOver.Three.C1KS 22 CertificateChecks.KernelTitsOver.Three.c1ksM
#krows CertificateChecks.KernelTitsOver.Three.C1RB CertificateChecks.KernelTitsOver.Three.c1rbM
#krows CertificateChecks.KernelTitsOver.Three.C1H CertificateChecks.KernelTitsOver.Three.c1hM
#krows CertificateChecks.KernelTitsOver.Three.C1CN CertificateChecks.KernelTitsOver.Three.c1cnM
#krows CertificateChecks.KernelTitsOver.Three.C1CH CertificateChecks.KernelTitsOver.Three.c1chM
#krows CertificateChecks.KernelTitsOver.Three.C1NH CertificateChecks.KernelTitsOver.Three.c1nhM
#krows CertificateChecks.KernelTitsOver.Three.C1L CertificateChecks.KernelTitsOver.Three.c1lM
#krowsw CertificateChecks.KernelTitsOver.Three.C1MK 1024 CertificateChecks.KernelTitsOver.Three.c1mkM
#krows CertificateChecks.KernelTitsOver.Three.C1MISC CertificateChecks.KernelTitsOver.Three.c1miscM

end
