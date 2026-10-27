module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public import Certificates.Kernel.Sporadic.OddCore.PEnumFamCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Sporadic.SuzOddCore.CTIChainInputs
meta import CFSG.Sporadic.SuzOddCore.CTIChainInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzCT

open CFSG.PSL3Four.Native CFSG.Sporadic.SuzOddCore

meta def fix0M : List Nat := fixList 0
meta def fix1M : List Nat := fixList 1
meta def k0M : Array (Array Nat) := kGens 0
meta def k0iM : Array (Array Nat) := kInvs 0
meta def k1iM : Array (Array Nat) := kInvs 1
meta def dM : Array (Array Nat) := dGens
meta def diM : Array (Array Nat) := dInvs
meta def qM : Array (Array Nat) := qGens
meta def id42 : Array Nat := idTab 42
meta def id54 : Array Nat := idTab 54
meta def repsM : Array (Array Nat) := (List.range 10).toArray.map classRep
meta def k1SM : Array (Array Nat) := k1Strong
meta def k1BM : Array Nat := k1Base
meta def aSM : Array (Array Nat) := actStrong
meta def aBM : Array Nat := actBase

meta def normPos (n : Nat) (T G GI gs : Array (Array Nat)) (first : Bool) : Array (Array Nat) :=
  let idx := indexOf T
  ((List.range G.size).toArray.map fun j => (List.range gs.size).toArray.map fun i =>
    let x := if first then conjTab n G[j]! GI[j]! gs[i]! else conjTab n GI[j]! G[j]! gs[i]!
    #[idx.getD x 0]).flatten

meta def dTabs : Array (Array Nat) := (enumOf 42 dGens 20160).tabs
meta def np1M : Array (Array Nat) := normPos 42 dTabs (kGens 0) (kInvs 0) dGens true
meta def np2M : Array (Array Nat) := normPos 42 dTabs (kGens 0) (kInvs 0) dGens false
meta def qp1M : Array (Array Nat) := normPos 54 qTabs (kGens 1) (kInvs 1) qGens true
meta def qp2M : Array (Array Nat) := normPos 54 qTabs (kGens 1) (kInvs 1) qGens false

meta def coverM : Array (Array Nat) :=
  let idxs := classOrbits.map fun e => indexOf e.tabs
  dTabs.map fun t =>
    let l := ((List.range 10).find? fun l => (idxs[l]!).contains t).getD 0
    #[65536 * l + (idxs[l]!).getD t 0]

end CertificateChecks.KernelSpor.SuzCT

#knatlist CertificateChecks.KernelSpor.SuzCT.fix0L CertificateChecks.KernelSpor.SuzCT.fix0M
#knatlist CertificateChecks.KernelSpor.SuzCT.fix1L CertificateChecks.KernelSpor.SuzCT.fix1M
#kpenum CertificateChecks.KernelSpor.SuzCT.K0E 42 6 false CertificateChecks.KernelSpor.SuzCT.k0M
  CertificateChecks.KernelSpor.SuzCT.k0M CertificateChecks.KernelSpor.SuzCT.id42 40320
#kmisc_packarrs CertificateChecks.KernelSpor.SuzCT.K0I CertificateChecks.KernelSpor.SuzCT.k0iM 6
#kpenum CertificateChecks.KernelSpor.SuzCT.DE 42 6 false CertificateChecks.KernelSpor.SuzCT.dM
  CertificateChecks.KernelSpor.SuzCT.dM CertificateChecks.KernelSpor.SuzCT.id42 20160
#kmisc_packarrs CertificateChecks.KernelSpor.SuzCT.DI CertificateChecks.KernelSpor.SuzCT.diM 6
#kpenumfam CertificateChecks.KernelSpor.SuzCT.OF 42 6 true CertificateChecks.KernelSpor.SuzCT.dM
  CertificateChecks.KernelSpor.SuzCT.diM CertificateChecks.KernelSpor.SuzCT.repsM 5000
#kpenum CertificateChecks.KernelSpor.SuzCT.QE 54 6 false CertificateChecks.KernelSpor.SuzCT.qM
  CertificateChecks.KernelSpor.SuzCT.qM CertificateChecks.KernelSpor.SuzCT.id54 64
#kmisc_packarrs CertificateChecks.KernelSpor.SuzCT.K1I CertificateChecks.KernelSpor.SuzCT.k1iM 6
#kmisc_packarrs CertificateChecks.KernelSpor.SuzCT.NP1 CertificateChecks.KernelSpor.SuzCT.np1M 32
#kmisc_packarrs CertificateChecks.KernelSpor.SuzCT.NP2 CertificateChecks.KernelSpor.SuzCT.np2M 32
#kmisc_packarrs CertificateChecks.KernelSpor.SuzCT.QP1 CertificateChecks.KernelSpor.SuzCT.qp1M 32
#kmisc_packarrs CertificateChecks.KernelSpor.SuzCT.QP2 CertificateChecks.KernelSpor.SuzCT.qp2M 32
#kmisc_packarrs CertificateChecks.KernelSpor.SuzCT.COV CertificateChecks.KernelSpor.SuzCT.coverM 32
#ks_rawchain CertificateChecks.KernelSpor.SuzCT.K1C 54 6 54 CertificateChecks.KernelSpor.SuzCT.k1SM
  CertificateChecks.KernelSpor.SuzCT.k1BM 10 CFSG.Sporadic.SuzOddCore.k1Words
#ks_rawchain CertificateChecks.KernelSpor.SuzCT.AC 64 7 64 CertificateChecks.KernelSpor.SuzCT.aSM
  CertificateChecks.KernelSpor.SuzCT.aBM 10 CFSG.Sporadic.SuzOddCore.actWords

end
