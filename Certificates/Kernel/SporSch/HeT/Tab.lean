module

public import Certificates.Kernel.Sporadic.He.Bind2112
public import Certificates.Kernel.Sporadic.He.Canon2112
public import Certificates.Kernel.SporSch.PairJ3.GenClT
public import Certificates.Kernel.SporSch.Ru.RowsGen
public import CFSG.Certificates.Kernel.SporSch.PairJ3CntSound
public meta import CFSG.Sporadic.HeldB.HeBlocks
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.SporSch.PairClTSound
public import CFSG.Certificates.Kernel.SporSch.PairKSound
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.Sporadic.Schreier.ImagePairs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HeTc

meta def baseM : Array Nat := CFSG.Sporadic.HeldB.heBase.toArray

meta def levelsM : Array CFSG.Monster.B.Co2.Native.Level := CFSG.Sporadic.HeldB.heLevels

meta def bsM : List Nat := CFSG.Sporadic.HeldB.heBase

meta def clM : List (List (Array Nat) × Array (Array Nat) × Array Nat × Array Nat) :=
  [([], #[#[0, 0, 0, 0, 0]], #[0], #[0])]

end CertificateChecks.KernelSporSch.HeTc

#kss_cltdata CertificateChecks.KernelSporSch.HeTb 8330 14 5 CFSG.Sporadic.HeldB.heStrongArrs
  CertificateChecks.KernelSporSch.HeTc.baseM CertificateChecks.KernelSporSch.HeTc.levelsM
  CertificateChecks.KernelSporSch.HeTc.bsM CertificateChecks.KernelSporSch.HeTc.clM 32 8 64

namespace CertificateChecks.KernelSporSch.HeTc

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CertificateChecks.KernelSporSch
open CertificateChecks.KernelSpor

@[expose] noncomputable def tsB (i : Nat) : Bool :=
  Nat.beq (HeTb.Ts i) (stepsAt 8330 14 HeC.S 9 HeC.BP i)

@[expose] noncomputable def ltB (s : Nat) : Bool :=
  allBlk (Nat.mul s 1024) (ltOKT 8330 14 9 HeTb.NR HeC.S HeC.SI HeTb.LT) 1024

@[expose] noncomputable def ptB (i s : Nat) : Bool :=
  allBlk (Nat.mul s 1024) (ptOKT 8330 14 HeTb.NR HeC.LR HeTb.Ts HeTb.PT i) 1024

@[expose] noncomputable def qtB (i s : Nat) : Bool :=
  allBlk (Nat.mul s 1024) (qtOKT 8330 14 HeTb.NR HeC.LR HeTb.QT i) 1024

end CertificateChecks.KernelSporSch.HeTc

#kss_each CertificateChecks.KernelSporSch.HeTc.TS CertificateChecks.KernelSporSch.HeTc.tsB 5
#kss_each CertificateChecks.KernelSporSch.HeTc.LTc CertificateChecks.KernelSporSch.HeTc.ltB 147
#kss_b2 CertificateChecks.KernelSporSch.HeTc CertificateChecks.KernelSporSch.HeTc.ptB 0 5 9
#kss_b2all CertificateChecks.KernelSporSch.HeTc CertificateChecks.KernelSporSch.HeTc.ptB 5 9
#kss_b2 CertificateChecks.KernelSporSch.HeTc CertificateChecks.KernelSporSch.HeTc.qtB 0 5 9
#kss_b2all CertificateChecks.KernelSporSch.HeTc CertificateChecks.KernelSporSch.HeTc.qtB 5 9

namespace CertificateChecks.KernelSporSch.HeTc

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CertificateChecks.KernelSporSch
open CertificateChecks.KernelSpor

theorem tabs : TabsT 8330 14 9 5 HeC.BP HeTb.NR HeTb.NR HeC.S HeC.SI HeC.LR HeTb.Ts HeTb.LT
    HeTb.PT HeTb.QT 147 1024 9 1024 :=
  ⟨by decide, by decide, by decide, by decide, TS.all, LTc.all, ptB_all, qtB_all⟩

theorem tc : TabChain 8330 14 9 5 HeC.BP 131 64 HeTb.NR HeTb.NR 147 1024 9 1024 HeC.S HeC.SI
    HeC.LR HeTb.Ts HeTb.LT HeTb.PT HeTb.QT CFSG.Sporadic.HeldB.heStrongArrs
    CFSG.Sporadic.HeldB.heBase.toArray CFSG.Sporadic.HeldB.heBase :=
  ⟨He2112.binds, He2112.perm, HeC.ho, by decide, tabs, rfl⟩

@[expose] noncomputable def nfp (F x : Nat) : Nat := nfPtT 14 HeTb.NR HeTb.NR HeTb.LT HeTb.PT 5 F x

end CertificateChecks.KernelSporSch.HeTc

end
