module

public import Certificates.Kernel.HeLoc.Seven1Chain
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

meta def levels1M : Array CFSG.Monster.B.Co2.Native.Level :=
  CFSG.Certificates.Native.rawLevels 8330 CFSG.RankThree.PartOne.heSevenCase1Arrs
    CFSG.RankThree.PartOne.heSevenCase1BaseArr

meta def bs1M : List Nat := CFSG.RankThree.PartOne.heSevenCase1Base.map Fin.val

meta def cl1M : List (List (Array Nat) × Array (Array Nat) × Array Nat × Array Nat) :=
  [([], #[(Array.range 10).map fun _ => 0], #[0], #[0])]

end CertificateChecks.KernelHeLoc.Seven

#kss_cltdata CertificateChecks.KernelHeLoc.T71 8330 14 10 CFSG.RankThree.PartOne.heSevenCase1Arrs
  CertificateChecks.KernelHeLoc.Seven.base1M CertificateChecks.KernelHeLoc.Seven.levels1M
  CertificateChecks.KernelHeLoc.Seven.bs1M CertificateChecks.KernelHeLoc.Seven.cl1M 32 8 64

namespace CertificateChecks.KernelHeLoc.Seven

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CertificateChecks.KernelSpor
open CertificateChecks.KernelHeLoc

theorem k1Bind : allN 11 (fun j => Nat.beq (S71T.F j) (S71.S j)) = true := by quickRfl

theorem k1Perm : allN 11 (fun j => permOK 8330 14 (mask 14) (8330 * 14) (S71.S j) (S71.SI j)) =
    true := by quickRfl

theorem k1Gen : bAnd(Nat.beq (S71.S 0) (HeC.S 0), Nat.beq (S71.S 1) (HeC.S 1)) = true := by
  quickRfl

@[expose] noncomputable def u1B (c : Nat) : Bool :=
  CFSG.KC.Misc.Clos.allR (Nat.mul 833 c) 833 fun x =>
    bIf(Nat.blt x 8330, Nat.beq (pg 14 (mask 14) (S71.S 2) x) (uM x), true)

theorem k1U : allN 10 u1B = true := by quickRfl

theorem k1Base : allN 10 (fun t => Nat.beq CFSG.RankThree.PartOne.heSevenCase1BaseArr[t]!
    (pg 14 (mask 14) S71.BP t)) = true := by quickRfl

theorem k1Prod : Nat.beq (((List.range 10).map fun i => rcnt (S71.LR i)).prod) 8060774400 =
    true := by quickRfl

@[expose] noncomputable def ts1B (i : Nat) : Bool :=
  Nat.beq (T71.Ts i) (stepsAt 8330 14 S71.S 11 S71.BP i)

@[expose] noncomputable def lt1B (s : Nat) : Bool :=
  allBlk (Nat.mul s 1024) (ltOKT 8330 14 11 T71.NR S71.S S71.SI T71.LT) 1024

@[expose] noncomputable def pt1B (i s : Nat) : Bool :=
  allBlk (Nat.mul s 1024) (ptOKT 8330 14 T71.NR S71.LR T71.Ts T71.PT i) 1024

@[expose] noncomputable def qt1B (i s : Nat) : Bool :=
  allBlk (Nat.mul s 1024) (qtOKT 8330 14 T71.NR S71.LR T71.QT i) 1024

end CertificateChecks.KernelHeLoc.Seven

#kss_each CertificateChecks.KernelHeLoc.Seven.TS1 CertificateChecks.KernelHeLoc.Seven.ts1B 10
#kss_each CertificateChecks.KernelHeLoc.Seven.LT1 CertificateChecks.KernelHeLoc.Seven.lt1B 179
#kss_b2 CertificateChecks.KernelHeLoc.Seven CertificateChecks.KernelHeLoc.Seven.pt1B 0 10 9
#kss_b2all CertificateChecks.KernelHeLoc.Seven CertificateChecks.KernelHeLoc.Seven.pt1B 10 9
#kss_b2 CertificateChecks.KernelHeLoc.Seven CertificateChecks.KernelHeLoc.Seven.qt1B 0 10 9
#kss_b2all CertificateChecks.KernelHeLoc.Seven CertificateChecks.KernelHeLoc.Seven.qt1B 10 9

end
