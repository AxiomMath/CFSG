
module

public import Certificates.Kernel.Sporadic.ON5.Final
public import CFSG.Certificates.Kernel.Spor.ChainFKProof
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON5K

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.CB CFSG.KS.CH CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum
open CFSG.KC.BfsPin CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.PSL3Four.Native
open CertificateChecks.KernelSpor.ON3 (allBelowN_iff)

theorem m120_strong_sizes :
    Data.M120Chain.strongGenerators.all (fun g => g.size == 120) = true := by
  rw [← Array.all_toList]
  quickRfl

theorem m120_part_proved : Data.M120Chain.generators.all (fun g => g.size == 120) = true ∧
    Data.D120Generators.all (fun g => g.size == 120) = true ∧
    Data.D120Generators.size = 4 ∧
    allBelowN 4 (fun j => pisInv 120 Data.D120Generators[j]!
      (pinvCand 120 Data.D120Generators[j]!)) = true ∧
    enumOK 120 Data.M120Chain.generators m120Enum = true ∧ m120Enum.tabs.size = 40320 ∧
    (m120Enum.tabs.filter fun x => Data.D120Generators.all fun g =>
      comp 120 x g == comp 120 g x).size = 2 ∧
    allBelowN 4 (fun j => memFull 120
      (cLevels 120 Data.M120Chain.base (allSteps Data.M120Chain.strongGenerators
        (pinvs 120 Data.M120Chain.strongGenerators) Data.M120Chain.base))
      (allInvSteps Data.M120Chain.strongGenerators
        (pinvs 120 Data.M120Chain.strongGenerators) Data.M120Chain.base)
      Data.M120Chain.base Data.D120Generators[j]!) = true := by
  obtain ⟨hD, hS, -, hlev, hsift⟩ := small_parts
  have me : m120Enum = penumRec 120 7 ON5M.cnt ON5M.T ON5M.PL := m120_sound.1
  refine ⟨by rw [← Array.all_toList]; quickRfl, by rw [← Array.all_toList]; quickRfl, rfl,
    allBelowN_iff.2 fun j hj => pisInv_of (f := dF j) (fi := dFI j)
      (by have hj' : j < 4 := hj; interval_cases j <;> rfl)
      (fun x hx => (hD j hj x hx).1.symm) fun x hx => ⟨(hD j hj x hx).2.1, (hD j hj x hx).2.2.2⟩,
    by rw [me]; exact m120_sound.2, by rw [me]; simp [penumRec]; rfl, ?_,
    allBelowN_iff.2 fun j hj => ?_⟩
  · rw [me]
    simp only [penumRec]
    rw [filter_ofFn (m := ON5M.cnt) (f := fun i => unpack 120 7 (ON5M.T i)), List.size_toArray,
      List.length_map]
    have hcnt : ON5M.cnt = 2016 * 20 := rfl
    have e : ((List.range ON5M.cnt).filter fun i => Data.D120Generators.all fun g =>
        comp 120 (unpack 120 7 (ON5M.T i)) g == comp 120 g (unpack 120 7 (ON5M.T i))) =
        (List.range ON5M.cnt).filter qD := by
      apply List.filter_congr
      intro i hi
      have hi' : i < ON5M.cnt := List.mem_range.1 hi
      rw [all_comm (gensOK_of d_gens) (penumPt_canon (m_pt hi'))]
      unfold qD
      rw [strictB_app']
    rw [e, hcnt, blocks_eq qD 2016 selIn 20 fun s hs => by
      have h := selFrom_spec qD 2016 _ _ (dSelAll s hs)
      have e2 : Nat.mul s 2016 = 2016 * s := Nat.mul_comm s 2016
      rw [e2] at h
      exact h]
    have hd : ((List.range 20).flatMap selIn).length = 2 := by decide +kernel
    exact hd
  · have hSz : ∀ j < Data.M120Chain.strongGenerators.size,
        Data.M120Chain.strongGenerators[j]!.size = 120 := by
      intro j hj
      rw [getElem!_pos _ j hj]
      exact beq_iff_eq.1 (Array.all_eq_true.1 m120_strong_sizes j hj)
    exact memFull3_proved (n := 120) (F := sF) (FI := sFI) (B := sB) (G := dF j) (IDX := sIDX)
      (LEN := sLEN) (Mr := sMr) (PTS := sPTS) (POS := sPOS) (PAR := sPAR) (LAB := sLAB) rfl hSz
      (fun j' hj' x hx => ⟨(hS j' hj' x hx).1.symm, (hS j' hj' x hx).2⟩) rfl
      (fun k hk => ⟨rfl, by interval_cases k <;> decide⟩) (fun y hy => (hD j hj y hy).1.symm)
      (fun y hy => (hD j hj y hy).2.1) (fun i hi => by interval_cases i <;> decide)
      (fun i hi => (hlev i hi).1) (fun i hi => (hlev i hi).2.1) (fun i hi => (hlev i hi).2.2.1)
      (fun i hi => (hlev i hi).2.2.2) (hsift j hj)

end CertificateChecks.KernelSpor.ON5K

end
