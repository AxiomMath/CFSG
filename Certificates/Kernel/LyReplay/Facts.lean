module

public import Certificates.Kernel.LyReplay.Check
public import CFSG.Certificates.Kernel.LyReplay.Sound
import CFSG.Certificates.Kernel.Common.DeepRfl
import all CFSG.Sporadic.Recognition.LyonsFinalDist2Inputs

set_option profiler true
set_option profiler.threshold 100

public section

namespace CertificateChecks.KernelLyReplay

open CFSG.KC.LyReplay CFSG.Sporadic.Recognition.LyonsSims.LyFinal

theorem derivs_eq : dist2Derivs =
    (List.range 11).map fun i => derivOf (starts.getD i []) (steps.getD i []) := by
  deep_rfl 1000000 1024

theorem kR_eq : rulesOf kR = dist2KRules := by decide +kernel

theorem eR_eq : rulesOf eR = dist2ERules := by decide +kernel

theorem tR_eq : rulesOf tR = dist2TRules := by decide +kernel

theorem replay_all : ∀ i < 11, replayAt i = true := by
  intro i hi
  interval_cases i
  exacts [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10]

theorem stepB_mem {i : Nat} (hi : i < 11) {s : Nat × Nat × List Nat × List Nat}
    (hs : s ∈ steps.getD i []) (hk : kindOf s.2.1 = .B) :
    wordOf s.2.2.1 ++ derivInv (wordOf s.2.2.2) ∈ dist2BWords := by
  unfold dist2BWords
  rw [List.mem_eraseDups, List.mem_append]
  right
  refine List.mem_flatMap.2 ⟨derivOf (starts.getD i []) (steps.getD i []), ?_, ?_⟩
  · rw [derivs_eq]
    exact List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩
  · refine List.mem_filterMap.2 ⟨stepOf s, List.mem_map.2 ⟨s, hs, rfl⟩, ?_⟩
    simp only [stepOf, hk, parseWord_strOf]

theorem dist2Replays_true : dist2Replays = true := by
  unfold dist2Replays
  rw [Bool.and_eq_true]
  constructor
  · have e : dist2RelatorStrings = dist2Derivs.map Dist2Deriv.start := rfl
    have e' : dist2Relators = dist2Derivs.map fun d => parseWord d.start := by
      unfold dist2Relators
      rw [e, List.map_map]
      rfl
    rw [e']
    exact beq_self_eq_true _
  · refine List.all_eq_true.2 fun d hd => ?_
    rw [derivs_eq] at hd
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hd
    have hi' := List.mem_range.1 hi
    unfold dist2DerivOK derivOf
    rw [parseWord_strOf]
    refine dist2Replay_of_replayW _ _ _ (fun s hs hk => stepB_mem hi' hs hk) ?_
    have h := replay_all i hi'
    unfold replayAt at h
    rwa [kR_eq, eR_eq, tR_eq] at h

end CertificateChecks.KernelLyReplay

end
