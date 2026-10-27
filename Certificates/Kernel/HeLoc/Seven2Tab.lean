module

public import Certificates.Kernel.HeLoc.Seven2Chain
public import Certificates.Kernel.HeLoc.MemDefs
public import Certificates.Kernel.Sporadic.He.Chain2112
public import Certificates.Kernel.SporSch.PairJ3.GenClT
public import Certificates.Kernel.SporSch.Ru.RowsGen
public import CFSG.Certificates.Kernel.SporSch.PairJ3CntSound
public meta import CFSG.RankThree.PartOne.KS.HeSevenCheckDefs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHeLoc.Seven

meta def levels2M : Array CFSG.Monster.B.Co2.Native.Level :=
  CFSG.Certificates.Native.rawLevels 8330 CFSG.RankThree.PartOne.heSevenCase2Arrs
    CFSG.RankThree.PartOne.heSevenCase2BaseArr

meta def bs2M : List Nat := CFSG.RankThree.PartOne.heSevenCase2Base.map Fin.val

meta def cl2M : List (List (Array Nat) × Array (Array Nat) × Array Nat × Array Nat) :=
  [([], #[(Array.range 7).map fun _ => 0], #[0], #[0])]

end CertificateChecks.KernelHeLoc.Seven

#kss_cltdata CertificateChecks.KernelHeLoc.T72 8330 14 7 CFSG.RankThree.PartOne.heSevenCase2Arrs
  CertificateChecks.KernelHeLoc.Seven.base2M CertificateChecks.KernelHeLoc.Seven.levels2M
  CertificateChecks.KernelHeLoc.Seven.bs2M CertificateChecks.KernelHeLoc.Seven.cl2M 32 8 64

namespace CertificateChecks.KernelHeLoc.Seven

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CertificateChecks.KernelSpor
open CertificateChecks.KernelHeLoc

theorem k2Bind : allN 10 (fun j => Nat.beq (S72T.F j) (S72.S j)) = true := by quickRfl

theorem k2Perm : allN 10 (fun j => permOK 8330 14 (mask 14) (8330 * 14) (S72.S j) (S72.SI j)) =
    true := by quickRfl

theorem k2Gen : bAnd(Nat.beq (S72.S 0) (HeC.S 0), Nat.beq (S72.S 1) (HeC.S 1)) = true := by
  quickRfl

@[expose] noncomputable def u2B (c : Nat) : Bool :=
  CFSG.KC.Misc.Clos.allR (Nat.mul 833 c) 833 fun x =>
    bIf(Nat.blt x 8330, Nat.beq (pg 14 (mask 14) (S72.S 2) x) (uM x), true)

theorem k2U : allN 10 u2B = true := by quickRfl

theorem k2Base : allN 7 (fun t => Nat.beq CFSG.RankThree.PartOne.heSevenCase2BaseArr[t]!
    (pg 14 (mask 14) S72.BP t)) = true := by quickRfl

theorem k2Prod : Nat.beq (((List.range 7).map fun i => rcnt (S72.LR i)).prod) 8060774400 =
    true := by quickRfl

@[expose] noncomputable def ts2B (i : Nat) : Bool :=
  Nat.beq (T72.Ts i) (stepsAt 8330 14 S72.S 10 S72.BP i)

@[expose] noncomputable def lt2B (s : Nat) : Bool :=
  allBlk (Nat.mul s 1024) (ltOKT 8330 14 10 T72.NR S72.S S72.SI T72.LT) 1024

@[expose] noncomputable def pt2B (i s : Nat) : Bool :=
  allBlk (Nat.mul s 1024) (ptOKT 8330 14 T72.NR S72.LR T72.Ts T72.PT i) 1024

@[expose] noncomputable def qt2B (i s : Nat) : Bool :=
  allBlk (Nat.mul s 1024) (qtOKT 8330 14 T72.NR S72.LR T72.QT i) 1024

end CertificateChecks.KernelHeLoc.Seven

#kss_each CertificateChecks.KernelHeLoc.Seven.TS2 CertificateChecks.KernelHeLoc.Seven.ts2B 7
#kss_each CertificateChecks.KernelHeLoc.Seven.LT2 CertificateChecks.KernelHeLoc.Seven.lt2B 163
#kss_b2 CertificateChecks.KernelHeLoc.Seven CertificateChecks.KernelHeLoc.Seven.pt2B 0 7 9
#kss_b2all CertificateChecks.KernelHeLoc.Seven CertificateChecks.KernelHeLoc.Seven.pt2B 7 9
#kss_b2 CertificateChecks.KernelHeLoc.Seven CertificateChecks.KernelHeLoc.Seven.qt2B 0 7 9
#kss_b2all CertificateChecks.KernelHeLoc.Seven CertificateChecks.KernelHeLoc.Seven.qt2B 7 9

end
