module

public import Certificates.Data.Kernel.O8.Til
public import Certificates.Kernel.OmegaEight.TilData
public import Certificates.Kernel.OmegaEight.S0Data
public import Certificates.Kernel.OmegaEight.OrthGens
public import Certificates.Kernel.OmegaEight.CorrGens
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitTilData
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitConeData
public import Mathlib

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight.Chain

theorem kXP' : xOK 10837449240524681216 12 GPlus CPlus TilXP (reflWords .plus) = true := by quickRfl
theorem kXM' : xOK 11067126980204625904 4 GMinus CMinus TilXM (reflWords .minus) = true := by quickRfl
theorem kTabP :
    tabOK GPlus CPlus UPlus TilXP (uWords .plus) TilLP TilMTP TilXIP TilUIP = true := by
  quickRfl
theorem kTabM :
    tabOK GMinus CMinus UMinus TilXM (uWords .minus) TilLM TilMTM TilXIM TilUIM = true := by
  quickRfl
theorem kZP :
    zOK GPlus CPlus TilXP (uWords .plus) TilLP TilMTP TilTRP 4 17 TilZAP TilSWP TilWMP = true := by
  quickRfl
theorem kZM :
    zOK GMinus CMinus TilXM (uWords .minus) TilLM TilMTM TilTRM 1 16 TilZAM TilSWM TilWMM = true := by
  quickRfl

theorem kTilCloseP : ∀ c < 16, closeOK TilLP TilMTP c = true := by
  intro c hc
  interval_cases c <;> quickRfl

theorem kTilCloseM : ∀ c < 16, closeOK TilLM TilMTM c = true := by
  intro c hc
  interval_cases c <;> quickRfl

theorem kTilInvP_0 : invOK TilLP TilMTP 4 0 = true := by quickRfl
theorem kTilInvP_1 : invOK TilLP TilMTP 4 1 = true := by quickRfl
theorem kTilInvP_2 : invOK TilLP TilMTP 4 2 = true := by quickRfl
theorem kTilInvP_3 : invOK TilLP TilMTP 4 3 = true := by quickRfl
theorem kTilInvP_4 : invOK TilLP TilMTP 4 4 = true := by quickRfl
theorem kTilInvP_5 : invOK TilLP TilMTP 4 5 = true := by quickRfl
theorem kTilInvP_6 : invOK TilLP TilMTP 4 6 = true := by quickRfl
theorem kTilInvP_7 : invOK TilLP TilMTP 4 7 = true := by quickRfl
theorem kTilInvP_8 : invOK TilLP TilMTP 4 8 = true := by quickRfl
theorem kTilInvP_9 : invOK TilLP TilMTP 4 9 = true := by quickRfl
theorem kTilInvP_10 : invOK TilLP TilMTP 4 10 = true := by quickRfl
theorem kTilInvP_11 : invOK TilLP TilMTP 4 11 = true := by quickRfl
theorem kTilInvP_12 : invOK TilLP TilMTP 4 12 = true := by quickRfl
theorem kTilInvP_13 : invOK TilLP TilMTP 4 13 = true := by quickRfl
theorem kTilInvP_14 : invOK TilLP TilMTP 4 14 = true := by quickRfl
theorem kTilInvP_15 : invOK TilLP TilMTP 4 15 = true := by quickRfl
theorem kTilInvP : ∀ c < 16, invOK TilLP TilMTP 4 c = true := by
  intro c hc
  interval_cases c
  exacts [kTilInvP_0, kTilInvP_1, kTilInvP_2, kTilInvP_3, kTilInvP_4, kTilInvP_5, kTilInvP_6,
    kTilInvP_7, kTilInvP_8, kTilInvP_9, kTilInvP_10, kTilInvP_11, kTilInvP_12, kTilInvP_13,
    kTilInvP_14, kTilInvP_15]

theorem kTilInvM_0 : invOK TilLM TilMTM 1 0 = true := by quickRfl
theorem kTilInvM_1 : invOK TilLM TilMTM 1 1 = true := by quickRfl
theorem kTilInvM_2 : invOK TilLM TilMTM 1 2 = true := by quickRfl
theorem kTilInvM_3 : invOK TilLM TilMTM 1 3 = true := by quickRfl
theorem kTilInvM_4 : invOK TilLM TilMTM 1 4 = true := by quickRfl
theorem kTilInvM_5 : invOK TilLM TilMTM 1 5 = true := by quickRfl
theorem kTilInvM_6 : invOK TilLM TilMTM 1 6 = true := by quickRfl
theorem kTilInvM_7 : invOK TilLM TilMTM 1 7 = true := by quickRfl
theorem kTilInvM_8 : invOK TilLM TilMTM 1 8 = true := by quickRfl
theorem kTilInvM_9 : invOK TilLM TilMTM 1 9 = true := by quickRfl
theorem kTilInvM_10 : invOK TilLM TilMTM 1 10 = true := by quickRfl
theorem kTilInvM_11 : invOK TilLM TilMTM 1 11 = true := by quickRfl
theorem kTilInvM_12 : invOK TilLM TilMTM 1 12 = true := by quickRfl
theorem kTilInvM_13 : invOK TilLM TilMTM 1 13 = true := by quickRfl
theorem kTilInvM_14 : invOK TilLM TilMTM 1 14 = true := by quickRfl
theorem kTilInvM_15 : invOK TilLM TilMTM 1 15 = true := by quickRfl
theorem kTilInvM : ∀ c < 16, invOK TilLM TilMTM 1 c = true := by
  intro c hc
  interval_cases c
  exacts [kTilInvM_0, kTilInvM_1, kTilInvM_2, kTilInvM_3, kTilInvM_4, kTilInvM_5, kTilInvM_6,
    kTilInvM_7, kTilInvM_8, kTilInvM_9, kTilInvM_10, kTilInvM_11, kTilInvM_12, kTilInvM_13,
    kTilInvM_14, kTilInvM_15]

theorem kTilZFinP : ∀ c < 16, zFinOK TilLP 4 TilZAP TilWMP c = true := by
  intro c hc
  interval_cases c <;> quickRfl

theorem kTilZFinM : ∀ c < 16, zFinOK TilLM 1 TilZAM TilWMM c = true := by
  intro c hc
  interval_cases c <;> quickRfl

end CertificateChecks.KernelO8

end
