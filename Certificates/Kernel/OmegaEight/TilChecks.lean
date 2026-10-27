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

theorem kTilInvP : ∀ c < 16, invOK TilLP TilMTP 4 c = true := by
  intro c hc
  interval_cases c <;> quickRfl

theorem kTilInvM : ∀ c < 16, invOK TilLM TilMTM 1 c = true := by
  intro c hc
  interval_cases c <;> quickRfl

theorem kTilZFinP : ∀ c < 16, zFinOK TilLP 4 TilZAP TilWMP c = true := by
  intro c hc
  interval_cases c <;> quickRfl

theorem kTilZFinM : ∀ c < 16, zFinOK TilLM 1 TilZAM TilWMM c = true := by
  intro c hc
  interval_cases c <;> quickRfl

end CertificateChecks.KernelO8

end
