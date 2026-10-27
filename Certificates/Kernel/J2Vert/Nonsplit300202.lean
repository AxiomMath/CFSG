module

public import Certificates.Data.Kernel.J2VertK
public import CFSG.Quasithin.Background.Harris.R1.J2VertCheck
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutData
public import CFSG.Certificates.Kernel.LocalCompUnpack
public import Certificates.Data.Kernel.Spor.Prim
public import Certificates.Kernel.Misc.Perm.HexCmd
meta import CFSG.Quasithin.Background.Harris.R1.J2VertCheck
meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutData
meta import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.Quasithin.Background.Harris.R1.J2VertTables
meta import CFSG.Quasithin.Background.Harris.R1.J2VertTables

namespace CertificateChecks.KernelJ2Vert.Nonsplit

open CFSG.Quasithin.Background.Harris.R1.J2Vert CFSG.ComponentClassification.J2Cover
open CFSG.Monster.B.Co2.Native

meta def bM : Array (Array Nat) := #[autStrong[0]!, autStrong[1]!, outerArr]

meta def gM : Array (Array Nat) := rGenArrs 315 bM

meta def gIM : Array (Array Nat) := gM.map (invCand 315)

meta def eM : Array (Array Nat) := (buildTab 315 gM tabR).toArray

meta def sM : Array (Array Nat) :=
  let P := eM.map (CFSG.KS.RawGen.pack 9)
  #[(List.range eM.size).toArray.qsort (fun a b => decide (P[a]! < P[b]!))]

end CertificateChecks.KernelJ2Vert.Nonsplit

public section

#kmisc_packarrs CertificateChecks.KernelJ2Vert.Nonsplit.NB CertificateChecks.KernelJ2Vert.Nonsplit.bM 9
#kmisc_packarrs CertificateChecks.KernelJ2Vert.Nonsplit.NG CertificateChecks.KernelJ2Vert.Nonsplit.gM 9
#kmisc_packarrs CertificateChecks.KernelJ2Vert.Nonsplit.NGI CertificateChecks.KernelJ2Vert.Nonsplit.gIM 9
#kmisc_packarrs CertificateChecks.KernelJ2Vert.Nonsplit.NE CertificateChecks.KernelJ2Vert.Nonsplit.eM 9
#kmisc_packarrs CertificateChecks.KernelJ2Vert.Nonsplit.NS CertificateChecks.KernelJ2Vert.Nonsplit.sM 12

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Vert.Nonsplit

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.J2VertK
open CFSG.Quasithin.Background.Harris.R1.J2Vert CFSG.ComponentClassification.J2Cover

noncomputable abbrev cn (p : Nat) : Bool := canonK 315 9 (mask 9) (315 * 9) p

noncomputable abbrev one : Nat := pidn 315 9

theorem kId : bAnd(cn one, idK 315 9 (mask 9)) = true := by quickRfl

theorem kBind : bAnd(bindArrK autStrong[0]! 315 9 (NB 0), bAnd(bindArrK autStrong[1]! 315 9 (NB 1),
    bindArrK outerArr 315 9 (NB 2))) = true := by
  quickRfl

theorem kCanonB : allN 3 (fun k => cn (NB k)) = true := by quickRfl

theorem kWords : allN 8 (fun i => Nat.beq (NG i) (evalK 315 9 NB (rWords.getD i []))) = true := by
  quickRfl

theorem kGen : allN 8 (fun i => bAnd(invEqK 315 9 (mask 9) (315 * 9) (NG i) (NGI i),
    bAnd(cn (NG i), cn (NGI i)))) = true := by
  quickRfl

theorem kRel : allL (vRels true) (fun r => Nat.beq (relK 315 9 NG NGI r) one) = true := by
  quickRfl

theorem kTree : bAnd(Nat.beq (NE 0) one, treeK 315 9 8 NG NE tabR 0) = true := by
  quickRfl

theorem kSort : sortK 3840 NE (NS 0) 12 = true := by
  quickRfl

end CertificateChecks.KernelJ2Vert.Nonsplit

end
