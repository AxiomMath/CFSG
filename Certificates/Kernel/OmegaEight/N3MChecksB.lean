module

public import Certificates.Kernel.OmegaEight.N3MW
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Stage2
  CFSG.EvenSmallLie.OmegaEight.N3Split
  CFSG.EvenSmallLie.OmegaEight.N3Split.MinusW

theorem bray2_okN3M : brayChk2 wN3M = true := by
  simp only [brayChk2, brayCheck, wN3M, runK_eq, mulK_eq, idK_eq, contains_decE_eq, gensOK,
    invPair, ← Array.all_toList, N3Split.Minus.base, N3Split.Minus.cGens, N3Split.Minus.tGens,
    splitCGens, splitTGens, kronK_eq]
  quickRfl

theorem x0_okN3M : N3Split.Minus.x0Chk = true := by
  simp only [N3Split.Minus.x0Chk, runK_eq, mulK_eq, idK_eq, gensOK, invPair, ← Array.all_toList,
    N3Split.Minus.base, N3Split.Minus.cGens, N3Split.Minus.tGens, splitCGens, splitTGens,
    kronK_eq]
  quickRfl

theorem z_okN3M : N3Split.Minus.zChk = true := by
  simp only [N3Split.Minus.zChk, runK_eq, mulK_eq, idK_eq, fpowK_eq, gensOK, invPair,
    ← Array.all_toList, N3Split.Minus.base, N3Split.Minus.cGens, N3Split.Minus.tGens,
    splitCGens, splitTGens, kronK_eq]
  quickRfl

end CertificateChecks.KernelO8
