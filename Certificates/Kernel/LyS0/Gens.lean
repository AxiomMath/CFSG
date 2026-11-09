module

public import Certificates.Kernel.LyS0.Data
public import Certificates.Kernel.SporSch.Ly.BSData
public import Certificates.Data.Kernel.LyS0.Check
public import Certificates.Kernel.LyS0.GensRun
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.LyS0.GensCmd

public section

set_option maxRecDepth 400000

#lys0_envs CertificateChecks.KernelLyS0.GE [150, 300, 450, 600]

namespace CertificateChecks.KernelLyS0

open CFSG.KD.LyS0

theorem gp0 : pieceK T [(0, CertificateChecks.KernelSporSch.LyBS.A),
    (1, CertificateChecks.KernelSporSch.LyBS.B)] 0 150 GE.E1 = true := by quickRfl

theorem gp1 : pieceK T GE.E1 150 150 ((201, GI 0) :: GE.E2) = true := by quickRfl

theorem gp2 : pieceK T GE.E2 300 150 ((362, GI 1) :: GE.E3) = true := by quickRfl

theorem gp3 : pieceK T GE.E3 450 150 ((467, GI 2) :: GE.E4) = true := by quickRfl

theorem gp4 : pieceK T GE.E4 600 145 [(637, GI 3), (746, GI 4)] = true := by quickRfl

theorem gensC : gensK CertificateChecks.KernelSporSch.LyBS.A CertificateChecks.KernelSporSch.LyBS.B
    T GI = true := by
  have g0 := pieceK_good (good_start CertificateChecks.KernelSporSch.LyBS.A
    CertificateChecks.KernelSporSch.LyBS.B T) gp0
  have g1 := pieceK_good g0 gp1
  have g2 := pieceK_good (good_tail g1) gp2
  have g3 := pieceK_good (good_tail g2) gp3
  have g4 := pieceK_good (good_tail g3) gp4
  exact gensK_of (good_head g1) (good_head g2) (good_head g3) (good_head g4)
    (good_head (good_tail g4))

end CertificateChecks.KernelLyS0

end
