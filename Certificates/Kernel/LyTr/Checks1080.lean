module

public import Certificates.Kernel.LyTr.Defs1080
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.LyTr.Defs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLyTr

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim
open CFSG.Sporadic.Recognition.LyonsSims

theorem k_y0 : bAnd(c11 (SH.F 0), bAnd(i11 (SH.F 0) (SH.F 0),
    bAnd(Nat.beq (p11 (SH.F 0) (SH.F 0)) id11,
      allN 5 (fun j => bAnd(c11 (R1I j), i11 (R1.GI j) (R1I j)))))) = true := by
  quickRfl

theorem k_erel : allN 4 (fun i => Nat.beq (p11 (p11 (SH.F 0) (UH.F i)) (SH.F 0))
    (wK 1080 11 LU (Ly1080.erelWords.getD i []))) = true := by
  quickRfl

theorem k_gen : bAnd(Nat.beq (UH.F 1) (wK 1080 11 LAB (Ly1080.genWords.getD 0 [])),
    Nat.beq (UH.F 2) (wK 1080 11 LAB (Ly1080.genWords.getD 1 []))) = true := by
  quickRfl

theorem k_sigt : allN 5 (fun j => Nat.beq (p11 (p11 (SH.F 0) (R1.GI j)) (SH.F 0))
    (wK 1080 11 LY (Ly1080.sigmaTxyWords.getD j []))) = true := by
  quickRfl

end CertificateChecks.KernelLyTr

end
