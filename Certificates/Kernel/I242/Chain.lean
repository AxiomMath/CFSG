module

public import Certificates.Kernel.I242.Gens
public import Certificates.Kernel.I242.YChain
public import CFSG.HardMathSupport.Solomon.Coordinator.I24_2Inputs
import Mathlib.Tactic.IntervalCases
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelI242

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.EvenSmallLie.OmegaEight (pushWords wordsOf)

theorem bindsY : Binds 3510 12 Y.S 17 7 Y.BP i242S ((i242Base.map Fin.val).toArray) := by
  obtain ⟨hs, he⟩ := pushWords_eq yArrs Y.head
  refine ⟨by norm_num, by norm_num, by norm_num, hs, he, rfl, fun t ht => ?_⟩
  interval_cases t <;> rfl

theorem chain_k : i242ChainCheck = true := by
  unfold i242ChainCheck
  rw [Bool.and_eq_true, wordsOf_eq]
  refine ⟨rawChainPK_sound (chunks := 4) (NS := 3510) (CH := 1) bindsY Y.head Y.hl
    (by norm_num) YP.spAll, ?_⟩
  rw [rawOrbitSizesK_sound bindsY permY Y.hl]
  decide +kernel

open Certificates in
theorem cert13506 : CFSG.HardMathSupport.Solomon.Coordinator.i242ChainCheck = true := chain_k

end CertificateChecks.KernelI242

end
