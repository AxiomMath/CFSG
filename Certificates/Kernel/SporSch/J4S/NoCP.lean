
module

public import Certificates.Kernel.SporSch.J4S.NoCPBase

public import Certificates.Kernel.SporSch.J4S.NoCK
public import Certificates.Kernel.SporSch.J4S.Form
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.SporSch.J4SBfsProved
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.J4NoCP

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.C11 CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KS.SporSch.J4B
open CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4Schreier.NoComp CFSG.Sporadic.SmallF2.Native
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.J4Eta
open CertificateChecks.KernelSporSch.J4NoCK CertificateChecks.KernelSporSch.J4InvP

theorem facts : (∀ l < 7,
      ((Finset.range 2048).filter fun a => NoComp.etaV unMats repVecs[l]! a = repVecs[l]!).card =
        repCounts[l]! ∧
      ∀ a < 2048, NoComp.etaV unMats repVecs[l]! a = repVecs[l]! ∨
        O.vne (NoComp.etaV unMats repVecs[l]! a) repVecs[l]! = true)
    ∧ (bilB rootBits repVecs[2]! = true ∧ bilB rootBits repVecs[3]! = false)
    ∧ (outsideOK unMats NoComp.conjTab = true)
    ∧ ((∀ a ∈ dList, a < 2048) ∧ (∀ a ∈ dList, ∀ b ∈ dList, a ^^^ b ∈ dList) ∧
      (∀ i < 276, ∀ i' < 276, orb14.1[i]! ^^^ 1 = orb14.1[i']! → orb14.1[i]! ∈ dList) ∧
      (∀ j < 7, 1 ≤ j → ((List.range 276).any fun i => orb14.1[i]! == chainBase[j]!) = true ∧
        ((List.range 276).any fun i => orb14.1[i]! == chainBase[j]! ^^^ 1) = true) ∧
      ∀ l < 7, 1 ≤ l → ∀ i < 276, orb14.1[i]! ∉ dSets[l]!)
    ∧ ((∀ e ∈ kdData, app11W e.2.2 1 = e.1 ∧ ∀ a ∈ dList,
        NoComp.etaV unMats repVecs[e.2.1]! (app11W e.2.2 a) = repVecs[e.2.1]!) ∧
      ∀ l ∈ [5, 6], ∀ dd ∈ dSets[l]!, (kdData.any fun e => e.1 == dd && e.2.1 == l) = true)
    ∧ chainP (swApp sTab) := by
  have ho : orb14.1 = tabA 276 J4O14.PT := by
    rw [orb14, (bfsK_sound_proved J4Orbits.xy_bind J4Orbits.b14).1]
  have hpt : ∀ i < 276, orb14.1[i]! = J4O14.PT i := fun i hi => by rw [ho, tabA_get hi]
  refine ⟨fun l hl => fix_ok hl, ⟨?_, ?_⟩, outside_ok, ⟨by decide, ?_, ?_, ?_, ?_⟩, ⟨?_, by decide⟩,
    chain_ok⟩
  · rw [rv_get (by omega)]
    exact bil_ok bil2
  · rw [rv_get (by omega)]
    exact bil_ok bil3
  · intro a ha b hb
    exact memL_iff.1 (allL_iff.1 (allL_iff.1 tdx a ha) b hb)
  · intro i hi i' hi' e
    rw [hpt i hi, hpt i' hi'] at e
    have h := allN_spec (allN_spec tdo i hi) i' hi'
    have e' : Nat.beq (Nat.xor (J4O14.PT i) 1) (J4O14.PT i') = true := beq_iff.2 e
    rw [bIf_t e'] at h
    rw [hpt i hi]
    exact memL_iff.1 h
  · intro j hj hj1
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec tdc (j - 1) (by omega))
    have ej : Nat.succ (j - 1) = j := by omega
    rw [ej, cb_get j hj] at h1 h2
    rw [anyK_eq, List.any_eq_true] at h1 h2
    obtain ⟨i, hi, e1⟩ := h1
    obtain ⟨i', hi', e2⟩ := h2
    rw [List.mem_range] at hi hi'
    refine ⟨List.any_eq_true.2 ⟨i, List.mem_range.2 hi, ?_⟩,
      List.any_eq_true.2 ⟨i', List.mem_range.2 hi', ?_⟩⟩
    · rw [hpt i hi, beq_iff.1 e1]
      simp
    · rw [hpt i' hi', beq_iff.1 e2]
      simp
  · intro l hl hl1 i hi hm
    have h := allN_spec (allN_spec tdd (l - 1) (by omega)) i hi
    have el : Nat.succ (l - 1) = l := by omega
    rw [el, ← dSets_get, ← hpt i hi] at h
    have : memL orb14.1[i]! dSets[l]! = true := memL_iff.2 hm
    rw [this] at h
    exact absurd h (by decide)
  · intro e he
    have hk := recAll (P := fun e => kdC e.1 e.2.1 e.2.2) kd e he
    have hl7 : ∀ e ∈ kdData, e.2.1 < 7 := by decide
    have hl := hl7 e he
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 hk
    rw [rv_get hl, app11W_eq]
    refine ⟨beq_iff.1 h1, fun a ha => ?_⟩
    rw [app11W_eq, etaV_eq]
    exact beq_iff.1 (allL_iff.1 h2 a ha)

end CertificateChecks.KernelSporSch.J4NoCP

end
