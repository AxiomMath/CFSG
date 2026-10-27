module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.RowsCmd
import Certificates.Kernel.Sporadic.RowsWCmd
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Data.Kernel.MaxD2.Gen
meta import CFSG.LocalAnalysis.StandardType.TitsFiveOvergroupData
import Certificates.Data.Kernel.MaxD2.Gen
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD

namespace CertificateChecks.KernelTitsOver.Five

open CFSG.KS.MaxD2 Certificates.MaxD2Perm CFSG.StandardType.TitsFive

meta def pD : Data where
  n := 1755
  p := 5
  gT := pairData.gT
  gOrder := pairData.gOrder
  uW := rWords.getD 0 []
  vW := rWords.getD 1 []
  nW := pairData.nW
  nOrder := pairData.nOrder
  fpPts := pairData.fpPts
  repW := pairData.repW
  genW := []
  tW := []
  tm := 0
  tlam := 0
  te := 0

meta def preM : Gen.Pre := Gen.pre pD 11

meta def repM : Array (Array Nat) := preM.rep
meta def repiM : Array (Array Nat) := preM.repi
meta def rbM : Array Nat := Gen.repImgs pD preM
meta def hM : Array Nat := Gen.hints pD 11 preM
meta def cnM : Array Nat := Gen.counts pD 11 preM
meta def mkM : Array Nat := Gen.mkeys pD 11 preM
meta def pgiM : Array (Array Nat) := (rGens pD).map (CFSG.PSL3Four.Native.invTab 1755)

end CertificateChecks.KernelTitsOver.Five

public section

#kmisc_packarrs CertificateChecks.KernelTitsOver.Five.REP CertificateChecks.KernelTitsOver.Five.repM 11
#kmisc_packarrs CertificateChecks.KernelTitsOver.Five.REPI
  CertificateChecks.KernelTitsOver.Five.repiM 11
#krows CertificateChecks.KernelTitsOver.Five.RB CertificateChecks.KernelTitsOver.Five.rbM
#krows CertificateChecks.KernelTitsOver.Five.H CertificateChecks.KernelTitsOver.Five.hM
#krows CertificateChecks.KernelTitsOver.Five.CN CertificateChecks.KernelTitsOver.Five.cnM
#krowsw CertificateChecks.KernelTitsOver.Five.MK 512 CertificateChecks.KernelTitsOver.Five.mkM
#kmisc_packarrs CertificateChecks.KernelTitsOver.Five.PGI CertificateChecks.KernelTitsOver.Five.pgiM 11

end
