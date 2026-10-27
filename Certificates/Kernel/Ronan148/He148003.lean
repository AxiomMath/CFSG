module

public import Certificates.Kernel.LocalComp.HeFix
public import Certificates.Data.Kernel.Spor.Prim
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RHeInputs
import Certificates.Kernel.Misc.Perm.HexCmd
meta import CFSG.RankThree.PartTwo.Sec4.Ronan148RHeInputs
import CFSG.Certificates.Kernel.Common.Harness

namespace CertificateChecks.KernelRonan148.He148003

open CFSG.RankThree.PartTwo.Sec4.Ronan148R CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He

meta def arrsM : Array (Array Nat) := #[heThreeArr heN0W, heThreeBA]

meta def invsM : Array (Array Nat) := #[CFSG.Monster.B.Co2.Native.invCand 8330 (heThreeArr heN0W)]

end CertificateChecks.KernelRonan148.He148003

public section

#kmisc_packarrs CertificateChecks.KernelRonan148.He148003.HN
  CertificateChecks.KernelRonan148.He148003.arrsM 14

#kmisc_packarrs CertificateChecks.KernelRonan148.He148003.HNI
  CertificateChecks.KernelRonan148.He148003.invsM 14

set_option maxRecDepth 400000

namespace CertificateChecks.KernelRonan148.He148003

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw
open CFSG.RankThree.PartTwo.Sec4.Ronan148R CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He
open CertificateChecks.KernelLC.HeFix

@[expose] noncomputable def relK (N NI X : Nat) : Bool :=
  Nat.beq (pcomp 8330 14 (mask 14) (pcomp 8330 14 (mask 14) N (pcomp 8330 14 (mask 14) X NI)) X)
      (pcomp 8330 14 (mask 14) X (pcomp 8330 14 (mask 14) N (pcomp 8330 14 (mask 14) X NI))) &&
    !(Nat.beq (pcomp 8330 14 (mask 14) N (pcomp 8330 14 (mask 14) X NI)) (pidn 8330 14)) &&
    !(Nat.beq (pcomp 8330 14 (mask 14) N (pcomp 8330 14 (mask 14) X NI)) X) &&
    !(Nat.beq (pcomp 8330 14 (mask 14) N (pcomp 8330 14 (mask 14) X NI))
      (pcomp 8330 14 (mask 14) X X)) &&
    Nat.beq (pcomp 8330 14 (mask 14) N (pcomp 8330 14 (mask 14)
        (pcomp 8330 14 (mask 14) N (pcomp 8330 14 (mask 14) X NI)) NI))
      (pcomp 8330 14 (mask 14) X (pcomp 8330 14 (mask 14) N (pcomp 8330 14 (mask 14) X NI)))

theorem kW : wordEqK 8330 14 (mask 14) (pidn 8330 14) L2 L2I 2 heN0W (HN 0) = true := by
  quickRfl

theorem kX : wordEqK 8330 14 (mask 14) (pidn 8330 14) L2 L2I 2 (heThreeWordsA.getD 0 [])
    (HN 1) = true := by
  quickRfl

theorem kI : invEqK 8330 14 (mask 14) (8330 * 14) (HN 0) (HNI 0) = true := by
  quickRfl

theorem kC : (cn (HN 0) && cn (HNI 0) && cn (HN 1)) = true := by
  quickRfl

theorem kR : relK (HN 0) (HNI 0) (HN 1) = true := by
  quickRfl

theorem kRNeg : (!relK (pidn 8330 14) (pidn 8330 14) (HN 1)) = true := by
  quickRfl

end CertificateChecks.KernelRonan148.He148003

end
