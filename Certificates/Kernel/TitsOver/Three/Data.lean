module

public import CFSG.Certificates.Kernel.Common.Loop
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

open CFSG.KS.MaxD2 Certificates.MaxD2Perm CFSG.StandardType.TitsThree CFSG.PSL3Four.Native

meta def pD : Data where
  n := 1755
  p := 3
  gT := pairData.gT
  gOrder := pairData.gOrder
  uW := pWords.getD 0 []
  vW := pWords.getD 1 []
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

meta def ngiM : Array (Array Nat) := nGensI pD
meta def pgiM : Array (Array Nat) :=
  (CFSG.StandardType.TitsOvergroup.pGens pairData).map (invTab 1755)
meta def sgiM (k : Nat) : Array (Array Nat) :=
  (CFSG.StandardType.TitsOvergroup.sideGens pairData k).map (invTab 1755)
meta def sgi0M : Array (Array Nat) := sgiM 0
meta def sgi1M : Array (Array Nat) := sgiM 1
meta def sgi2M : Array (Array Nat) := sgiM 2
meta def sgi3M : Array (Array Nat) := sgiM 3
meta def repM : Array (Array Nat) := preM.rep
meta def repiM : Array (Array Nat) := preM.repi
meta def ptM : Array Nat := pairData.fpPts.toArray
meta def fsM : Array Nat := Gen.fpSort preM
meta def ksM : Array Nat := Gen.fpKeys preM
meta def rbM : Array Nat := Gen.repImgs pD preM
meta def hM : Array Nat := Gen.hints pD 11 preM
meta def cnM : Array Nat := Gen.counts pD 11 preM
meta def lM : Array Nat := Gen.labels pD
meta def mkM : Array Nat := Gen.mkeys pD 11 preM
meta def miscM : Array Nat := #[Gen.numLabels pD]

meta def nhM : Array Nat :=
  let pT := (CFSG.StandardType.TitsOvergroup.pEnum pairData).tabs
  let idx := indexOf pT
  let gs := CFSG.StandardType.TitsOvergroup.nGens pairData
  let gi := gs.map (invTab 1755)
  let ps := CFSG.StandardType.TitsOvergroup.pGens pairData
  ((List.range gs.size).toArray.map fun j => ((List.range ps.size).toArray.map fun i =>
    #[idx.getD (conjTab 1755 gs[j]! gi[j]! ps[i]!) 0,
      idx.getD (conjTab 1755 gi[j]! gs[j]! ps[i]!) 0]).flatten).flatten

meta def sideIdx (k : Nat) : Std.HashMap (Array Nat) Nat :=
  indexOf (CFSG.StandardType.TitsOvergroup.sideEnum pairData k).tabs

meta def smqM : Array Nat :=
  let i2 := sideIdx 2
  let i3 := sideIdx 3
  (List.range pairData.repW.length).toArray.map fun i =>
    let k := pairData.kind[i]!
    if k == 3 then i2.getD preM.rep[i + 1]! 0
    else if k == 4 then i3.getD preM.rep[i + 1]! 0
    else 0

meta def mwqM : Array Nat :=
  let i0 := sideIdx 0
  let i1 := sideIdx 1
  (List.range 8).toArray.map fun c =>
    let k := c / 4
    let wd := (memWords.getD k []).getD (c % 4) []
    let t := CFSG.StandardType.TitsOvergroup.wT pairData wd
    if k == 0 then i0.getD t 0 else i1.getD t 0

end CertificateChecks.KernelTitsOver.Three

public section

#kmisc_packarrs CertificateChecks.KernelTitsOver.Three.NGI CertificateChecks.KernelTitsOver.Three.ngiM 11
#kmisc_packarrs CertificateChecks.KernelTitsOver.Three.PGI CertificateChecks.KernelTitsOver.Three.pgiM 11
#kmisc_packarrs CertificateChecks.KernelTitsOver.Three.SGI0
  CertificateChecks.KernelTitsOver.Three.sgi0M 11
#kmisc_packarrs CertificateChecks.KernelTitsOver.Three.SGI1
  CertificateChecks.KernelTitsOver.Three.sgi1M 11
#kmisc_packarrs CertificateChecks.KernelTitsOver.Three.SGI2
  CertificateChecks.KernelTitsOver.Three.sgi2M 11
#kmisc_packarrs CertificateChecks.KernelTitsOver.Three.SGI3
  CertificateChecks.KernelTitsOver.Three.sgi3M 11
#kmisc_packarrs CertificateChecks.KernelTitsOver.Three.REP CertificateChecks.KernelTitsOver.Three.repM 11
#kmisc_packarrs CertificateChecks.KernelTitsOver.Three.REPI
  CertificateChecks.KernelTitsOver.Three.repiM 11
#krows CertificateChecks.KernelTitsOver.Three.PT CertificateChecks.KernelTitsOver.Three.ptM
#krows CertificateChecks.KernelTitsOver.Three.FS CertificateChecks.KernelTitsOver.Three.fsM
#krowsw CertificateChecks.KernelTitsOver.Three.KS 22 CertificateChecks.KernelTitsOver.Three.ksM
#krows CertificateChecks.KernelTitsOver.Three.RB CertificateChecks.KernelTitsOver.Three.rbM
#krows CertificateChecks.KernelTitsOver.Three.H CertificateChecks.KernelTitsOver.Three.hM
#krows CertificateChecks.KernelTitsOver.Three.CN CertificateChecks.KernelTitsOver.Three.cnM
#krows CertificateChecks.KernelTitsOver.Three.L CertificateChecks.KernelTitsOver.Three.lM
#krowsw CertificateChecks.KernelTitsOver.Three.MK 4096 CertificateChecks.KernelTitsOver.Three.mkM
#krows CertificateChecks.KernelTitsOver.Three.MISC CertificateChecks.KernelTitsOver.Three.miscM
#krows CertificateChecks.KernelTitsOver.Three.NH CertificateChecks.KernelTitsOver.Three.nhM
#krows CertificateChecks.KernelTitsOver.Three.SMQ CertificateChecks.KernelTitsOver.Three.smqM
#krows CertificateChecks.KernelTitsOver.Three.MWQ CertificateChecks.KernelTitsOver.Three.mwqM

end
