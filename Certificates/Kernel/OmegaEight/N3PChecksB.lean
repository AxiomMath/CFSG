module

public import Certificates.Kernel.OmegaEight.N3PW
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Stage2
  CFSG.EvenSmallLie.OmegaEight.N3Split
  CFSG.EvenSmallLie.OmegaEight.N3Split.PlusW

theorem bray2_okN3P : brayChk wN3P 2 N3Split.Plus.brayProg2 N3Split.Plus.brayOut2 = true := by
  simp only [brayChk, brayCheck, wN3P, runK_eq, mulK_eq, idK_eq, contains_decE_eq, gensOK,
    invPair, ← Array.all_toList, N3Split.Plus.base, N3Split.Plus.cGens, N3Split.Plus.tGens,
    splitCGens, splitTGens, kronK_eq]
  quickRfl

theorem bray3_okN3P : brayChk wN3P 3 N3Split.Plus.brayProg3 N3Split.Plus.brayOut3 = true := by
  simp only [brayChk, brayCheck, wN3P, runK_eq, mulK_eq, idK_eq, contains_decE_eq, gensOK,
    invPair, ← Array.all_toList, N3Split.Plus.base, N3Split.Plus.cGens, N3Split.Plus.tGens,
    splitCGens, splitTGens, kronK_eq]
  quickRfl

theorem x0_okN3P : N3Split.Plus.x0Chk = true := by
  simp only [N3Split.Plus.x0Chk, runK_eq, mulK_eq, idK_eq, gensOK, invPair, ← Array.all_toList,
    N3Split.Plus.base, N3Split.Plus.cGens, N3Split.Plus.tGens, splitCGens, splitTGens, kronK_eq]
  quickRfl

theorem z_okN3P : N3Split.Plus.zChk = true := by
  simp only [N3Split.Plus.zChk, runK_eq, mulK_eq, idK_eq, fpowK_eq, gensOK, invPair,
    ← Array.all_toList, N3Split.Plus.base, N3Split.Plus.cGens, N3Split.Plus.tGens, splitCGens,
    splitTGens, kronK_eq]
  quickRfl

end CertificateChecks.KernelO8
