module

public import Certificates.Kernel.RuThree.Chain
public import Certificates.Kernel.SporSch.PairJ3.GenClT
public import Certificates.Kernel.SporSch.Ru.RowsGen
public import CFSG.Certificates.Kernel.SporSch.PairJ3CntSound
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuThreeInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.SporSch.PairClTSound
public import CFSG.Certificates.Kernel.SporSch.PairKSound
public import CFSG.Sporadic.Schreier.ImagePairs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelRuThree

meta def levelsM : Array CFSG.Monster.B.Co2.Native.Level :=
  CFSG.EvenSporadicStandard.RuStd.S2.ruThreeLevels

meta def bsM : List Nat := CFSG.EvenSporadicStandard.RuStd.S2.ruThreeKeys

meta def clM : List (List (Array Nat) × Array (Array Nat) × Array Nat × Array Nat) :=
  [([], #[(Array.range 7).map fun _ => 0], #[0], #[0])]

end CertificateChecks.KernelRuThree

#kss_cltdata CertificateChecks.KernelRuThree.T3R 4060 12 7 CFSG.EvenSporadicStandard.RuStd.S2.ruThreeArrs
  CertificateChecks.KernelRuThree.baseM CertificateChecks.KernelRuThree.levelsM
  CertificateChecks.KernelRuThree.bsM CertificateChecks.KernelRuThree.clM 32 8 64

namespace CertificateChecks.KernelRuThree

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch

@[expose] noncomputable def tsB (i : Nat) : Bool :=
  Nat.beq (T3R.Ts i) (stepsAt 4060 12 S3R.S 11 S3R.BP i)

@[expose] noncomputable def ltB (s : Nat) : Bool :=
  allBlk (Nat.mul s 1024) (ltOKT 4060 12 11 T3R.NR S3R.S S3R.SI T3R.LT) 1024

@[expose] noncomputable def ptB (i s : Nat) : Bool :=
  allBlk (Nat.mul s 1024) (ptOKT 4060 12 T3R.NR S3R.LR T3R.Ts T3R.PT i) 1024

@[expose] noncomputable def qtB (i s : Nat) : Bool :=
  allBlk (Nat.mul s 1024) (qtOKT 4060 12 T3R.NR S3R.LR T3R.QT i) 1024

end CertificateChecks.KernelRuThree

#kss_each CertificateChecks.KernelRuThree.TS CertificateChecks.KernelRuThree.tsB 7
#kss_each CertificateChecks.KernelRuThree.LT CertificateChecks.KernelRuThree.ltB 88
#kss_b2 CertificateChecks.KernelRuThree CertificateChecks.KernelRuThree.ptB 0 7 4
#kss_b2all CertificateChecks.KernelRuThree CertificateChecks.KernelRuThree.ptB 7 4
#kss_b2 CertificateChecks.KernelRuThree CertificateChecks.KernelRuThree.qtB 0 7 4
#kss_b2all CertificateChecks.KernelRuThree CertificateChecks.KernelRuThree.qtB 7 4

end
