module

public import Certificates.Kernel.LocalComp.PairE6Sound
public import Certificates.Kernel.Misc.E6SlpGens
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalStep83PairE6Tests
meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalStep83PairE6Tests
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelLC.PairE6

open CFSG.KC.Misc CFSG.KC.Misc.E6Std CFSG.KC.TwistedE6Two
open CFSG.LieType.Chevalley.C2E6Std.MatrixModel CFSG.Monster.B.Classical.E6Adjoint
open CFSG.ComponentClassification.RankTwoExcHypII.TwistedE6Two
open CFSG.ComponentClassification.RankTwoExceptional.PairE6

#e6_slp_gens PE progP nGensP

theorem kG : gensOK bracketCodes formBits rhoIdx PE.V 0 = true := by quickRfl

theorem kW : gensWOK bracketCodes formBits rhoIdx PE.V 72 = true := by quickRfl

theorem kU : pairUK bracketCodes formBits PE.V (nthV PE.V 62) 162 witsU bools = true := by
  quickRfl

theorem kV : pairVK bracketCodes formBits PE.V (mulB (nthV PE.V 48) (nthV PE.V 66)) 162 witsV
    bools = true := by
  quickRfl

theorem len_progP : lenLL progP = 18 := rfl

theorem hG : RepAll PE.V nGensP 144 := repAll_nGensP kG kW

theorem hV : RepAll PE.V nValsP 162 := by
  have h := repAll_run (V := PE.V) (prog := progP) (by rw [size_nGensP]; exact hG)
    (by rw [size_nGensP]; exact PE.lines)
  rwa [size_nGensP, len_progP] at h

theorem hU : Rep (nthV PE.V 62) (toMat nU) := by
  have h := hG 62 (by norm_num)
  rwa [nGensP_getD_lt (by norm_num)] at h

theorem hVv : Rep (mulB (nthV PE.V 48) (nthV PE.V 66)) (toMat nV) := by
  have h48 := hG 48 (by norm_num)
  have h66 := hG 66 (by norm_num)
  rw [nGensP_getD_lt (by norm_num)] at h48 h66
  exact rep_mul h48 h66

open Certificates in
open CFSG in
theorem cert15074 : CFSG.ComponentClassification.RankTwoExceptional.PairE6.pairCheckU = true ∧
    CFSG.ComponentClassification.RankTwoExceptional.PairE6.pairCheckV = true :=
  ⟨pairU_of_pairUK hV hU kU, pairV_of_pairVK hV hVv kV⟩

end CertificateChecks.KernelLC.PairE6

end
