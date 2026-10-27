module

public import Certificates.Kernel.OmegaEight.PlusW
public import CFSG.Certificates.Kernel.O8PlusSound
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight.Stage2 CFSG.EvenSmallLie.OmegaEight.Stage2.PlusW

theorem c2_okP : c2Check wP = true := by
  have hsC : sortedK (decE EnCP.D EnCP.m).keys = true := (Enum.of_enumOK cE_ok).2.1
  have hs2 : sortedK (decE EnC2.D EnC2.m).keys = true := (Enum.of_enumOK c2E_ok).2.1
  simp only [c2Check, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨c2E_ok, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · simp only [wP, decE_keys_size]
    decide +kernel
  · simp only [wP, gensIn, memK_decE_eq hsC (by decide +kernel), ← Array.all_toList]
    quickRfl
  · simp only [commGens, mulK_eq, ← Array.all_toList]
    quickRfl
  · simp only [commGens, mulK_eq, ← Array.all_toList]
    quickRfl
  · simp only [wP, centInCheck, mulK_eq, memK_decE_eq hs2 (by decide +kernel),
      ← Array.all_toList, decE_toList]
    quickRfl

theorem bray0_okP : brayChk wP 0 Plus.brayProg0 Plus.brayOut0 = true := by
  simp only [brayChk, brayCheck, wP, runK_eq, mulK_eq, idK_eq, contains_decE_eq, gensOK,
    invPair, ← Array.all_toList]
  quickRfl

theorem bray1_okP : brayChk wP 1 Plus.brayProg1 Plus.brayOut1 = true := by
  simp only [brayChk, brayCheck, wP, runK_eq, mulK_eq, idK_eq, contains_decE_eq, gensOK,
    invPair, ← Array.all_toList]
  quickRfl

theorem bray2_okP : brayChk wP 2 Plus.brayProg2 Plus.brayOut2 = true := by
  simp only [brayChk, brayCheck, wP, runK_eq, mulK_eq, idK_eq, contains_decE_eq, gensOK,
    invPair, ← Array.all_toList]
  quickRfl

theorem bray3_okP : brayChk wP 3 Plus.brayProg3 Plus.brayOut3 = true := by
  simp only [brayChk, brayCheck, wP, runK_eq, mulK_eq, idK_eq, contains_decE_eq, gensOK,
    invPair, ← Array.all_toList]
  quickRfl

theorem bray6_okP : brayChk wP 6 Plus.brayProg6 Plus.brayOut6 = true := by
  simp only [brayChk, brayCheck, wP, runK_eq, mulK_eq, idK_eq, contains_decE_eq, gensOK,
    invPair, ← Array.all_toList]
  quickRfl

theorem bray7_okP : brayChk wP 7 Plus.brayProg7 Plus.brayOut7 = true := by
  simp only [brayChk, brayCheck, wP, runK_eq, mulK_eq, idK_eq, contains_decE_eq, gensOK,
    invPair, ← Array.all_toList]
  quickRfl

end CertificateChecks.KernelO8
