module

public import Certificates.Data.Kernel.J2VertK
public import CFSG.Quasithin.Background.Harris.R1.J2VertCheck
public import CFSG.Certificates.Kernel.LocalCompUnpack
public import Certificates.Data.Kernel.Spor.Prim
public import Certificates.Kernel.Misc.Perm.HexCmd
meta import CFSG.Quasithin.Background.Harris.R1.J2VertCheck
meta import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.Quasithin.Background.Harris.R1.J2VertTables
meta import CFSG.Quasithin.Background.Harris.R1.J2VertTables

namespace CertificateChecks.KernelJ2Vert.Split

open CFSG.Quasithin.Background.Harris.R1.J2Vert CFSG.Monster.B.Co2.Native

meta def sM : Array (Array Nat) := sArrs

meta def sIM : Array (Array Nat) := sArrs.map (invCand 64)

meta def tM : Array (Array Nat) := tsArrs

meta def tIM : Array (Array Nat) := tsArrs.map (invCand 64)

meta def eSM : Array (Array Nat) := (buildTab 64 sArrs tabS).toArray

meta def eTM : Array (Array Nat) := (buildTab 64 tsArrs tabTs).toArray

meta def eQM : Array (Array Nat) := (buildTab 64 (sArrs.extract 0 5) tabQs).toArray

meta def sortM (E : Array (Array Nat)) : Array (Array Nat) :=
  let P := E.map (CFSG.KS.RawGen.pack 7)
  #[(List.range E.size).toArray.qsort (fun a b => decide (P[a]! < P[b]!))]

meta def sSM : Array (Array Nat) := sortM eSM

meta def sTM : Array (Array Nat) := sortM eTM

end CertificateChecks.KernelJ2Vert.Split

public section

#kmisc_packarrs CertificateChecks.KernelJ2Vert.Split.SG CertificateChecks.KernelJ2Vert.Split.sM 7
#kmisc_packarrs CertificateChecks.KernelJ2Vert.Split.SGI CertificateChecks.KernelJ2Vert.Split.sIM 7
#kmisc_packarrs CertificateChecks.KernelJ2Vert.Split.TG CertificateChecks.KernelJ2Vert.Split.tM 7
#kmisc_packarrs CertificateChecks.KernelJ2Vert.Split.TGI CertificateChecks.KernelJ2Vert.Split.tIM 7
#kmisc_packarrs CertificateChecks.KernelJ2Vert.Split.ES CertificateChecks.KernelJ2Vert.Split.eSM 7
#kmisc_packarrs CertificateChecks.KernelJ2Vert.Split.ET CertificateChecks.KernelJ2Vert.Split.eTM 7
#kmisc_packarrs CertificateChecks.KernelJ2Vert.Split.EQ CertificateChecks.KernelJ2Vert.Split.eQM 7
#kmisc_packarrs CertificateChecks.KernelJ2Vert.Split.SS CertificateChecks.KernelJ2Vert.Split.sSM 12
#kmisc_packarrs CertificateChecks.KernelJ2Vert.Split.ST CertificateChecks.KernelJ2Vert.Split.sTM 12

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Vert.Split

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.J2VertK
open CFSG.Quasithin.Background.Harris.R1.J2Vert

noncomputable abbrev cn (p : Nat) : Bool := canonK 64 7 (mask 7) (64 * 7) p

noncomputable abbrev pc (p q : Nat) : Nat := pcomp 64 7 (mask 7) p q

noncomputable abbrev one : Nat := pidn 64 7

theorem kId : bAnd(cn one, idK 64 7 (mask 7)) = true := by quickRfl

theorem kBindS : bAnd(Nat.beq sArrs.size 8, allN 8 (fun k => bindArrK sArrs[k]! 64 7 (SG k))) =
    true := by
  quickRfl

theorem kBindT : bAnd(Nat.beq tsArrs.size 3, allN 3 (fun k => bindArrK tsArrs[k]! 64 7 (TG k))) =
    true := by
  quickRfl

theorem kGenS : allN 8 (fun i => bAnd(invEqK 64 7 (mask 7) (64 * 7) (SG i) (SGI i),
    bAnd(cn (SG i), cn (SGI i)))) = true := by
  quickRfl

theorem kGenT : allN 3 (fun i => bAnd(invEqK 64 7 (mask 7) (64 * 7) (TG i) (TGI i),
    bAnd(cn (TG i), cn (TGI i)))) = true := by
  quickRfl

theorem kRel : allL (vRels false) (fun r => Nat.beq (relK 64 7 SG SGI r) one) = true := by
  quickRfl

theorem kTreeS : bAnd(Nat.beq (ES 0) one, treeK 64 7 8 SG ES tabS 0) = true := by
  quickRfl

theorem kSortS : sortK 3840 ES (SS 0) 12 = true := by
  quickRfl

theorem kTreeT : bAnd(Nat.beq (ET 0) one, treeK 64 7 3 TG ET tabTs 0) = true := by
  quickRfl

theorem kSortT : sortK 256 ET (ST 0) 12 = true := by
  quickRfl

theorem kTreeQ : bAnd(Nat.beq (EQ 0) one, treeK 64 7 5 SG EQ tabQs 0) = true := by
  quickRfl

theorem kMem : allN 3 (fun i => anyN 3840 (fun j => Nat.beq (ES j) (TG i))) = true := by
  quickRfl

theorem kClosedT : allN 256 (fun x => allN 3 (fun i =>
    bAnd(anyN 256 (fun j => Nat.beq (ET j) (pc (ET x) (TG i))),
      anyN 256 (fun j => Nat.beq (ET j) (pc (ET x) (TGI i)))))) = true := by
  quickRfl

theorem kClosedQ : allN 32 (fun x => allN 5 (fun i =>
    bAnd(anyN 32 (fun j => Nat.beq (EQ j) (pc (EQ x) (SG i))),
      anyN 32 (fun j => Nat.beq (EQ j) (pc (EQ x) (SGI i)))))) = true := by
  quickRfl

@[expose] noncomputable def lineK (v : Nat) : Bool :=
  !(Nat.beq (pc v v) one) || Nat.beq v one || Nat.beq v (SG 0) ||
    !(allN 3 fun j => Nat.beq (pc (pc (TG j) v) (TGI j)) v ||
      Nat.beq (pc (pc (TG j) v) (TGI j)) (pc (SG 0) v)) ||
    Nat.beq v (SG 1) || Nat.beq v (pc (SG 0) (SG 1))

theorem kLine : allN 32 (fun k => lineK (EQ k)) = true := by
  quickRfl

theorem kCent : Nat.beq (countN 256 (fun k => Nat.beq (pc (ET k) (SG 1)) (pc (SG 1) (ET k)))) 128 =
    true := by
  quickRfl

@[expose] noncomputable def rootK (x s y : Nat) : Bool :=
  Nat.beq (pc y x) (pc x y) && Nat.beq (pc y y) s

theorem kRoot0 : Nat.beq (countN 256 (fun k => rootK (SG 1) (SG 0) (ET k))) 28 = true := by
  quickRfl

theorem kRoot1 : Nat.beq (countN 256 (fun k => rootK (SG 1) (SG 1) (ET k))) 12 = true := by
  quickRfl

theorem kRoot2 : Nat.beq (countN 256 (fun k => rootK (SG 1) (pc (SG 0) (SG 1)) (ET k))) 12 =
    true := by
  quickRfl

end CertificateChecks.KernelJ2Vert.Split

end
