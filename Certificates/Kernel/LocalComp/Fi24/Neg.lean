module

public import Certificates.Kernel.LocalComp.Fi24.Parts
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelLC.F24

open CFSG.KC.LQT CFSG.KC.LocalComp.ElemParts CFSG.KC.LocalComp.Replay CFSG.SectionRank.Native
open CFSG.KD.LC.F24 (lay V P N)

theorem neg_replay_shift : Bool.not (replayOK lay V P (fun s => TT (s + 1)) N fi24primeData TO
    (fun _ => 0)) = true := by quickRfl

theorem neg_replay_outs : Bool.not (replayOK lay V P TT N fi24primeData (fun _ => 2)
    (fun _ => 0)) = true := by quickRfl

theorem neg_cube : Bool.not (cubeK lay V P N (TO 0) (sqI 0) (sqI 0)) = true := by quickRfl

theorem neg_pair : Bool.not (pairK V P N (TO 1) (TO 0) (ppI 0 1) (ppI 1 0)) = true := by quickRfl

theorem neg_ker : Bool.not (kerK lay V (fun _ => 2) (fun _ => 0) 4 0 10) = true := by quickRfl

end CertificateChecks.KernelLC.F24
