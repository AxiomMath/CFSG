module

public import Certificates.Kernel.RuFive.Chain
public import Certificates.Kernel.SporSch.PairJ3.GenClT
public import Certificates.Kernel.SporSch.Ru.RowsGen
public import CFSG.Certificates.Kernel.SporSch.PairJ3CntSound
public meta import CFSG.RankThree.PartOne.KS.RuFiveCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.SporSch.PairClTSound
public import CFSG.Certificates.Kernel.SporSch.PairKSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelRuFive

meta def levels0M : Array CFSG.Monster.B.Co2.Native.Level := CFSG.RankThree.PartOne.ruPLevels

meta def levels1M : Array CFSG.Monster.B.Co2.Native.Level :=
  CFSG.Certificates.Native.rawLevels 4060 CFSG.RankThree.PartOne.ruCase1Arrs
    CFSG.RankThree.PartOne.ruCase1BaseArr

meta def bs0M : List Nat := CFSG.RankThree.PartOne.ruFiveKeys

meta def bs1M : List Nat := CFSG.RankThree.PartOne.ruCase1BaseArr.toList

meta def clM : List (List (Array Nat) × Array (Array Nat) × Array Nat × Array Nat) :=
  [([], #[(Array.range 9).map fun _ => 0], #[0], #[0])]

meta def cl1M : List (List (Array Nat) × Array (Array Nat) × Array Nat × Array Nat) :=
  [([], #[(Array.range 5).map fun _ => 0], #[0], #[0])]

end CertificateChecks.KernelRuFive

#kss_cltdata CertificateChecks.KernelRuFive.T50 4060 12 9 CFSG.RankThree.PartOne.ruCase0Arrs
  CertificateChecks.KernelRuFive.base0M CertificateChecks.KernelRuFive.levels0M
  CertificateChecks.KernelRuFive.bs0M CertificateChecks.KernelRuFive.clM 32 8 64
#kss_cltdata CertificateChecks.KernelRuFive.T51 4060 12 5 CFSG.RankThree.PartOne.ruCase1Arrs
  CertificateChecks.KernelRuFive.base1M CertificateChecks.KernelRuFive.levels1M
  CertificateChecks.KernelRuFive.bs1M CertificateChecks.KernelRuFive.cl1M 32 8 64

namespace CertificateChecks.KernelRuFive

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch

@[expose] noncomputable def ts0B (i : Nat) : Bool :=
  Nat.beq (T50.Ts i) (stepsAt 4060 12 S50.S 8 S50.BP i)

@[expose] noncomputable def lt0B (s : Nat) : Bool :=
  allBlk (Nat.mul s 1024) (ltOKT 4060 12 8 T50.NR S50.S S50.SI T50.LT) 1024

@[expose] noncomputable def pt0B (i s : Nat) : Bool :=
  allBlk (Nat.mul s 1024) (ptOKT 4060 12 T50.NR S50.LR T50.Ts T50.PT i) 1024

@[expose] noncomputable def qt0B (i s : Nat) : Bool :=
  allBlk (Nat.mul s 1024) (qtOKT 4060 12 T50.NR S50.LR T50.QT i) 1024

@[expose] noncomputable def ts1B (i : Nat) : Bool :=
  Nat.beq (T51.Ts i) (stepsAt 4060 12 S51.S 10 S51.BP i)

@[expose] noncomputable def lt1B (s : Nat) : Bool :=
  allBlk (Nat.mul s 1024) (ltOKT 4060 12 10 T51.NR S51.S S51.SI T51.LT) 1024

@[expose] noncomputable def pt1B (i s : Nat) : Bool :=
  allBlk (Nat.mul s 1024) (ptOKT 4060 12 T51.NR S51.LR T51.Ts T51.PT i) 1024

@[expose] noncomputable def qt1B (i s : Nat) : Bool :=
  allBlk (Nat.mul s 1024) (qtOKT 4060 12 T51.NR S51.LR T51.QT i) 1024

end CertificateChecks.KernelRuFive

#kss_each CertificateChecks.KernelRuFive.TS0 CertificateChecks.KernelRuFive.ts0B 9
#kss_each CertificateChecks.KernelRuFive.LT0 CertificateChecks.KernelRuFive.lt0B 64
#kss_b2 CertificateChecks.KernelRuFive CertificateChecks.KernelRuFive.pt0B 0 9 4
#kss_b2all CertificateChecks.KernelRuFive CertificateChecks.KernelRuFive.pt0B 9 4
#kss_b2 CertificateChecks.KernelRuFive CertificateChecks.KernelRuFive.qt0B 0 9 4
#kss_b2all CertificateChecks.KernelRuFive CertificateChecks.KernelRuFive.qt0B 9 4
#kss_each CertificateChecks.KernelRuFive.TS1 CertificateChecks.KernelRuFive.ts1B 5
#kss_each CertificateChecks.KernelRuFive.LT1 CertificateChecks.KernelRuFive.lt1B 80
#kss_b2 CertificateChecks.KernelRuFive CertificateChecks.KernelRuFive.pt1B 0 5 4
#kss_b2all CertificateChecks.KernelRuFive CertificateChecks.KernelRuFive.pt1B 5 4
#kss_b2 CertificateChecks.KernelRuFive CertificateChecks.KernelRuFive.qt1B 0 5 4
#kss_b2all CertificateChecks.KernelRuFive CertificateChecks.KernelRuFive.qt1B 5 4

end
