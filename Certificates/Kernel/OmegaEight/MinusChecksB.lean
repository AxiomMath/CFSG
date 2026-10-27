module

public import Certificates.Kernel.OmegaEight.MinusW
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight.Stage2 CFSG.EvenSmallLie.OmegaEight.Stage2.MinusW

theorem bray2_okM : brayChk wM 2 Minus.brayProg2 Minus.brayOut2 = true := by
  simp only [brayChk, brayCheck, wM, runK_eq, mulK_eq, idK_eq, contains_decE_eq, gensOK,
    invPair, ← Array.all_toList]
  quickRfl

theorem bray3_okM : brayChk wM 3 Minus.brayProg3 Minus.brayOut3 = true := by
  simp only [brayChk, brayCheck, wM, runK_eq, mulK_eq, idK_eq, contains_decE_eq, gensOK,
    invPair, ← Array.all_toList]
  quickRfl

theorem bray4_okM : brayChk wM 4 Minus.brayProg4 Minus.brayOut4 = true := by
  simp only [brayChk, brayCheck, wM, runK_eq, mulK_eq, idK_eq, contains_decE_eq, gensOK,
    invPair, ← Array.all_toList]
  quickRfl

theorem bray5_okM : brayChk wM 5 Minus.brayProg5 Minus.brayOut5 = true := by
  simp only [brayChk, brayCheck, wM, runK_eq, mulK_eq, idK_eq, contains_decE_eq, gensOK,
    invPair, ← Array.all_toList]
  quickRfl

theorem bray6_okM : brayChk wM 6 Minus.brayProg6 Minus.brayOut6 = true := by
  simp only [brayChk, brayCheck, wM, runK_eq, mulK_eq, idK_eq, contains_decE_eq, gensOK,
    invPair, ← Array.all_toList]
  quickRfl

end CertificateChecks.KernelO8
