module

public import Certificates.Kernel.Sporadic.ON3.U
public import CFSG.Certificates.Kernel.Spor.ChainFKProof
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON3

open CFSG.KC.Enum CFSG.KS CFSG.KS.CB CFSG.KS.CH CFSG.KS.PW CFSG.ONSchreier CFSG.ONSchreier.Native

theorem psl_sizes : Data.PSL120Chain.strongGenerators.size = 12 ∧
    Data.PSL120Chain.strongGenerators.all (fun g => g.size == 120) = true :=
  ⟨rfl, by rw [← Array.all_toList]; quickRfl⟩

theorem u_facts_proved :
    pisInv 120 Data.quotientConjugator (pinvCand 120 Data.quotientConjugator) = true ∧
    allBelowN 2 (fun j => memFull 120
      (cLevels 120 Data.PSL120Chain.base (allSteps Data.PSL120Chain.strongGenerators
        (pinvs 120 Data.PSL120Chain.strongGenerators) Data.PSL120Chain.base))
      (allInvSteps Data.PSL120Chain.strongGenerators
        (pinvs 120 Data.PSL120Chain.strongGenerators) Data.PSL120Chain.base)
      Data.PSL120Chain.base (pcomp 120 Data.quotientConjugator
        (pcomp 120 (bTab (wordArrs Data.LWords)[j]!)
          (pinvCand 120 Data.quotientConjugator)))) = true := by
  obtain ⟨hF, hu, hlev, hs⟩ := psl_parts
  refine ⟨?_, allBelowN_iff.2 fun j hj => ?_⟩
  · unfold pisInv
    refine allBelowN_iff.2 fun x hx => ?_
    obtain ⟨u1, u2⟩ := hu x hx
    rw [uinv_get u1, u2]
    simp [u1]
  · have hj' : j < 2 := hj
    have hSz : ∀ j < 12, Data.PSL120Chain.strongGenerators[j]!.size = 120 := by
      intro j hj
      have h := Array.all_eq_true.1 psl_sizes.2 j (by rw [psl_sizes.1]; exact hj)
      rw [getElem!_pos _ j (by rw [psl_sizes.1]; exact hj)]
      exact beq_iff_eq.1 h
    have hqs : Data.quotientConjugator.size = 120 := rfl
    have hG : ∀ y < 120, uG j y < 120 := by
      intro y _
      unfold uG
      by_cases h : (bL[j]!)[uI y]! < 120
      · exact (hu _ h).1
      · rw [getElem!_neg _ _ (by rw [hqs]; exact h)]
        decide
    rw [(b_parts.2 j hj').2]
    refine memFull3_proved (s := 12) (F := pF) (FI := pFI) (B := pB) (G := uG j) (IDX := pIDX)
      (LEN := pLEN) (Mr := pMr) (PTS := pPTS) (POS := pPOS) (PAR := pPAR) (LAB := pLAB) rfl hSz
      (fun j' hj' x hx => hF j' hj' x hx) rfl (fun k hk => ?_) (fun y hy => ?_) hG
      (fun i hi => ?_)
      (fun i hi => (hlev i hi).1) (fun i hi => (hlev i hi).2.1) (fun i hi => (hlev i hi).2.2.1)
      (fun i hi => (hlev i hi).2.2.2) (hs j hj')
    · interval_cases k <;> exact ⟨rfl, by decide⟩
    · rw [pcomp_get' hy, pcomp_get' hy, uinv_get hy]
      rfl
    · interval_cases i <;> decide

end CertificateChecks.KernelSpor.ON3

end
