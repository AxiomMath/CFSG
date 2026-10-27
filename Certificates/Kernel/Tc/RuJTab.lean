module

public import Certificates.Kernel.SporSch.Ru.JOrb
public import Certificates.Kernel.SporSch.PairJ3.GenClT
public import Certificates.Kernel.SporSch.Ru.RowsGen
public import CFSG.Sporadic.Schreier.RuCheckChainsInputs
public meta import CFSG.Sporadic.Schreier.RuCheckChainsInputs
public meta import Certificates.Data.CFSGNative.Schreier.Check
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTc.RuJ

meta def strongM : Array (Array Nat) := CFSG.Sporadic.RuSchreier.ruField4060 3

meta def baseM : Array Nat :=
  CFSG.Sporadic.RuSchreier.ruBaseArr 4060 CFSG.Sporadic.RuSchreier.ruJoinBase

meta def levelsM : Array CFSG.Monster.B.Co2.Native.Level :=
  CFSG.Certificates.Native.rawLevels 4060 strongM baseM

meta def bsM : List Nat := [0, 1, 2, 3]

meta def clM : List (List (Array Nat) × Array (Array Nat) × Array Nat × Array Nat) :=
  [([], #[(Array.range 4).map fun _ => 0], #[0], #[0])]

end CertificateChecks.KernelTc.RuJ

#kss_cltdata CertificateChecks.KernelTc.RuJT 4060 12 4 CertificateChecks.KernelTc.RuJ.strongM
  CertificateChecks.KernelTc.RuJ.baseM CertificateChecks.KernelTc.RuJ.levelsM
  CertificateChecks.KernelTc.RuJ.bsM CertificateChecks.KernelTc.RuJ.clM 32 8 64

namespace CertificateChecks.KernelTc.RuJ

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CertificateChecks.KernelSporSch
  CertificateChecks.KernelTc

@[expose] noncomputable def tsB (i : Nat) : Bool :=
  Nat.beq (RuJT.Ts i) (stepsAt 4060 12 RuJO.S 18 RuJO.BP i)

@[expose] noncomputable def ltB (s : Nat) : Bool :=
  allBlk (Nat.mul s 1024) (ltOKT 4060 12 18 RuJT.NR RuJO.S RuJO.SI RuJT.LT) 1024

@[expose] noncomputable def ptB (i s : Nat) : Bool :=
  allBlk (Nat.mul s 1024) (ptOKT 4060 12 RuJT.NR RuJO.LR RuJT.Ts RuJT.PT i) 1024

@[expose] noncomputable def qtB (i s : Nat) : Bool :=
  allBlk (Nat.mul s 1024) (qtOKT 4060 12 RuJT.NR RuJO.LR RuJT.QT i) 1024

end CertificateChecks.KernelTc.RuJ

#kss_each CertificateChecks.KernelTc.RuJ.TS CertificateChecks.KernelTc.RuJ.tsB 4
#kss_each CertificateChecks.KernelTc.RuJ.LT CertificateChecks.KernelTc.RuJ.ltB 143
#kss_b2 CertificateChecks.KernelTc.RuJ CertificateChecks.KernelTc.RuJ.ptB 0 4 4
#kss_b2all CertificateChecks.KernelTc.RuJ CertificateChecks.KernelTc.RuJ.ptB 4 4
#kss_b2 CertificateChecks.KernelTc.RuJ CertificateChecks.KernelTc.RuJ.qtB 0 4 4
#kss_b2all CertificateChecks.KernelTc.RuJ CertificateChecks.KernelTc.RuJ.qtB 4 4

end
