module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.SporSch.Th.GenV4
public import Certificates.Kernel.LocalComp.BfsGen
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicHNData
meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicHNOTests
meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicHNData
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Assembly.Defs

namespace CertificateChecks.KernelSpor.HNAO

open CFSG.ComponentClassification.RankTwoSporadic.HN CFSG.Sporadic.HNOddCore.Native

meta def progN : List Nat := (parseNatsHN hnAProgStr).toList
meta def poolN : List Nat := (parseNatsHN hnAPoolStr).toList
meta def witN : List Nat := (parseNatsHN hnAWitStr).toList

meta def regs : Array (Array Nat) := regsA 1100 om0Gens (decodePairsO hnAProgStr)

meta def egens : Array (Array Nat) := (hnAPregs.map fun i => regs[i]!).toArray

meta def comms : Array (Array Nat) :=
  (decodePairsO hnAPoolStr).toArray.map fun gh =>
    CFSG.RankThree.Native.commutatorA 1100 regs[gh.1]! regs[gh.2]!

meta def run : Array (Array Nat) × Array (Array Nat) := CFSG.KC.BfsGen.search 1100 11 egens

meta def pts : Array (Array Nat) := run.1

meta def rows : Array (Array Nat) := run.2

meta def order : Array (Array Nat) :=
  let tv := pts.map (CFSG.KS.RawGen.pack 11)
  ((Array.range tv.size).qsort fun a b => tv[a]! < tv[b]!).map fun i => #[i]

meta def counts : Array (Array Nat) :=
  (Array.range 33).map fun s =>
    #[((rows.extract 0 (32 * s)).foldl (fun m r => r.foldl max m) 0 + 1)]

meta def keyOf (a : Array Nat) : Nat := a[0]! + 1100 * a[1]!

meta def keyOrder : List Nat :=
  ((Array.range pts.size).qsort fun a b => keyOf pts[a]! < keyOf pts[b]!).toList

meta def wits : List AWit := (decodeAO hnAWitStr).toList

meta def witC : List Nat := wits.map fun | .skip => 0 | .ord4 _ _ => 1
meta def witF : List Nat := wits.map fun | .skip => 0 | .ord4 fs _ => fs.headD 0
meta def witM : List Nat := wits.map fun | .skip => 0 | .ord4 _ m => m

end CertificateChecks.KernelSpor.HNAO

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.HNAT.Prog
  CFSG.ComponentClassification.RankTwoSporadic.HN.hnAProgStr
#ks_chars CertificateChecks.KernelSpor.HNAT.Pool
  CFSG.ComponentClassification.RankTwoSporadic.HN.hnAPoolStr
#ks_chars CertificateChecks.KernelSpor.HNAT.Wit
  CFSG.ComponentClassification.RankTwoSporadic.HN.hnAWitStr
#kss_natlist CertificateChecks.KernelSpor.HNAT.PN CertificateChecks.KernelSpor.HNAO.progN
#kss_natlist CertificateChecks.KernelSpor.HNAT.QN CertificateChecks.KernelSpor.HNAO.poolN
#kss_natlist CertificateChecks.KernelSpor.HNAT.WN CertificateChecks.KernelSpor.HNAO.witN

#kmisc_packarrs CertificateChecks.KernelSpor.HNAR.X CertificateChecks.KernelSpor.HNAO.regs 11
#kmisc_packarrs CertificateChecks.KernelSpor.HNAC.C CertificateChecks.KernelSpor.HNAO.comms 11

#kmisc_packarrs CertificateChecks.KernelSpor.HNAE.G CertificateChecks.KernelSpor.HNAO.egens 11
#kmisc_packarrs CertificateChecks.KernelSpor.HNAE.T CertificateChecks.KernelSpor.HNAO.pts 11
#kmisc_packarrs CertificateChecks.KernelSpor.HNAE.E CertificateChecks.KernelSpor.HNAO.rows 16
#kmisc_packarrs CertificateChecks.KernelSpor.HNAE.S CertificateChecks.KernelSpor.HNAO.order 32
#kmisc_packarrs CertificateChecks.KernelSpor.HNAE.C CertificateChecks.KernelSpor.HNAO.counts 32
#kss_natlist CertificateChecks.KernelSpor.HNAE.SKT CertificateChecks.KernelSpor.HNAO.keyOrder

#kss_natlist CertificateChecks.KernelSpor.HNAW.C CertificateChecks.KernelSpor.HNAO.witC
#kss_natlist CertificateChecks.KernelSpor.HNAW.F CertificateChecks.KernelSpor.HNAO.witF
#kss_natlist CertificateChecks.KernelSpor.HNAW.M CertificateChecks.KernelSpor.HNAO.witM

end
