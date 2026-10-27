module

public import Certificates.Kernel.HeLoc.Seven0Chain
public import Certificates.Kernel.SporSch.PairJ3.GenClT
public import Certificates.Kernel.SporSch.Ru.RowsGen
public import CFSG.Certificates.Kernel.SporSch.PairJ3CntSound
public meta import CFSG.RankThree.PartOne.KS.HeSevenCheckDefs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.SporSch.PairClTSound
public import CFSG.Certificates.Kernel.SporSch.PairKSound
public import CFSG.Sporadic.Schreier.ImagePairs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHeLoc.Seven

meta def levels0M : Array CFSG.Monster.B.Co2.Native.Level := CFSG.RankThree.PartOne.heSevenRLevels

meta def bs0M : List Nat := CFSG.RankThree.PartOne.heSevenKeys

meta def clM : List (List (Array Nat) × Array (Array Nat) × Array Nat × Array Nat) :=
  [([], #[(Array.range 14).map fun _ => 0], #[0], #[0])]

end CertificateChecks.KernelHeLoc.Seven

#kss_cltdata CertificateChecks.KernelHeLoc.T70 8330 14 14 CFSG.RankThree.PartOne.heSevenCase0Arrs
  CertificateChecks.KernelHeLoc.Seven.base0M CertificateChecks.KernelHeLoc.Seven.levels0M
  CertificateChecks.KernelHeLoc.Seven.bs0M CertificateChecks.KernelHeLoc.Seven.clM 32 8 64

namespace CertificateChecks.KernelHeLoc.Seven

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CertificateChecks.KernelHeLoc

@[expose] noncomputable def ts0B (i : Nat) : Bool :=
  Nat.beq (T70.Ts i) (stepsAt 8330 14 S70.S 10 S70.BP i)

@[expose] noncomputable def lt0B (s : Nat) : Bool :=
  allBlk (Nat.mul s 1024) (ltOKT 8330 14 10 T70.NR S70.S S70.SI T70.LT) 1024

@[expose] noncomputable def pt0B (i s : Nat) : Bool :=
  allBlk (Nat.mul s 1024) (ptOKT 8330 14 T70.NR S70.LR T70.Ts T70.PT i) 1024

@[expose] noncomputable def qt0B (i s : Nat) : Bool :=
  allBlk (Nat.mul s 1024) (qtOKT 8330 14 T70.NR S70.LR T70.QT i) 1024

end CertificateChecks.KernelHeLoc.Seven

#kss_each CertificateChecks.KernelHeLoc.Seven.TS0 CertificateChecks.KernelHeLoc.Seven.ts0B 14
#kss_each CertificateChecks.KernelHeLoc.Seven.LT0 CertificateChecks.KernelHeLoc.Seven.lt0B 163
#kss_b2 CertificateChecks.KernelHeLoc.Seven CertificateChecks.KernelHeLoc.Seven.pt0B 0 14 9
#kss_b2all CertificateChecks.KernelHeLoc.Seven CertificateChecks.KernelHeLoc.Seven.pt0B 14 9
#kss_b2 CertificateChecks.KernelHeLoc.Seven CertificateChecks.KernelHeLoc.Seven.qt0B 0 14 9
#kss_b2all CertificateChecks.KernelHeLoc.Seven CertificateChecks.KernelHeLoc.Seven.qt0B 14 9

end
