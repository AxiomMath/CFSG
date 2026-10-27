module

public import Certificates.Kernel.HeLoc.FiveChain
public import Certificates.Kernel.HeLoc.MemDefs
public import Certificates.Kernel.Sporadic.He.Chain2112
public import Certificates.Kernel.SporSch.PairJ3.GenClT
public import Certificates.Kernel.SporSch.Ru.RowsGen
public import CFSG.Certificates.Kernel.SporSch.PairJ3CntSound
public meta import CFSG.RankThree.PartOne.KS.HeFiveCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHeLoc.FiveL

meta def levels0M : Array CFSG.Monster.B.Co2.Native.Level :=
  CFSG.Certificates.Native.rawLevels 8330 CFSG.RankThree.PartOne.heFiveCase0Arrs
    CFSG.RankThree.PartOne.heFiveCase0BaseArr

meta def bs0M : List Nat := CFSG.RankThree.PartOne.heFiveCase0Base.map Fin.val

meta def cl0M : List (List (Array Nat) × Array (Array Nat) × Array Nat × Array Nat) :=
  [([], #[(Array.range 9).map fun _ => 0], #[0], #[0])]

end CertificateChecks.KernelHeLoc.FiveL

#kss_cltdata CertificateChecks.KernelHeLoc.T50 8330 14 9 CFSG.RankThree.PartOne.heFiveCase0Arrs
  CertificateChecks.KernelHeLoc.FiveL.base0M CertificateChecks.KernelHeLoc.FiveL.levels0M
  CertificateChecks.KernelHeLoc.FiveL.bs0M CertificateChecks.KernelHeLoc.FiveL.cl0M 32 8 64

namespace CertificateChecks.KernelHeLoc.FiveL

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CertificateChecks.KernelSpor
open CertificateChecks.KernelHeLoc

theorem k5Bind : allN 11 (fun j => Nat.beq (S50T.F j) (S50.S j)) = true := by quickRfl

theorem k5Perm : allN 11 (fun j => permOK 8330 14 (mask 14) (8330 * 14) (S50.S j) (S50.SI j)) =
    true := by quickRfl

theorem k5Gen : bAnd(Nat.beq (S50.S 0) (HeC.S 0), Nat.beq (S50.S 1) (HeC.S 1)) = true := by
  quickRfl

@[expose] noncomputable def u5B (c : Nat) : Bool :=
  CFSG.KC.Misc.Clos.allR (Nat.mul 833 c) 833 fun x =>
    bIf(Nat.blt x 8330, Nat.beq (pg 14 (mask 14) (S50.S 2) x) (uM x), true)

theorem k5U : allN 10 u5B = true := by quickRfl

theorem k5Base : allN 9 (fun t => Nat.beq CFSG.RankThree.PartOne.heFiveCase0BaseArr[t]!
    (pg 14 (mask 14) S50.BP t)) = true := by quickRfl

theorem k5Prod : Nat.beq (((List.range 9).map fun i => rcnt (S50.LR i)).prod) 8060774400 =
    true := by quickRfl

@[expose] noncomputable def ts5B (i : Nat) : Bool :=
  Nat.beq (T50.Ts i) (stepsAt 8330 14 S50.S 11 S50.BP i)

@[expose] noncomputable def lt5B (s : Nat) : Bool :=
  allBlk (Nat.mul s 1024) (ltOKT 8330 14 11 T50.NR S50.S S50.SI T50.LT) 1024

@[expose] noncomputable def pt5B (i s : Nat) : Bool :=
  allBlk (Nat.mul s 1024) (ptOKT 8330 14 T50.NR S50.LR T50.Ts T50.PT i) 1024

@[expose] noncomputable def qt5B (i s : Nat) : Bool :=
  allBlk (Nat.mul s 1024) (qtOKT 8330 14 T50.NR S50.LR T50.QT i) 1024

end CertificateChecks.KernelHeLoc.FiveL

#kss_each CertificateChecks.KernelHeLoc.FiveL.TS5 CertificateChecks.KernelHeLoc.FiveL.ts5B 9
#kss_each CertificateChecks.KernelHeLoc.FiveL.LT5 CertificateChecks.KernelHeLoc.FiveL.lt5B 179
#kss_b2 CertificateChecks.KernelHeLoc.FiveL CertificateChecks.KernelHeLoc.FiveL.pt5B 0 9 9
#kss_b2all CertificateChecks.KernelHeLoc.FiveL CertificateChecks.KernelHeLoc.FiveL.pt5B 9 9
#kss_b2 CertificateChecks.KernelHeLoc.FiveL CertificateChecks.KernelHeLoc.FiveL.qt5B 0 9 9
#kss_b2all CertificateChecks.KernelHeLoc.FiveL CertificateChecks.KernelHeLoc.FiveL.qt5B 9 9

end
