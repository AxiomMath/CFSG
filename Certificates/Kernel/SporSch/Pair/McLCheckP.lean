module

public import Certificates.Kernel.SporSch.Pair.McLCheck
public import CFSG.Certificates.Kernel.SporSch.PairClProof
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSporSch.PMcLCheck

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.Schreier.PairMcL
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CertificateChecks.KernelSporSch

private theorem sum_one {w : List (Array Nat)}
    {C : Array (Array Nat) × Array Nat × Array Nat} {s : Nat} (h : C.1.size = s) :
    ([(w, C)].map fun c => c.2.1.size).sum = s := by
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  exact h

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem facts_proved : (rawChainOK 275 (mclStrongArrs.extract 0 2) mclStrongArrs baseArr mclWords 4 = true ∧
      rawOrbitSizes 275 mclStrongArrs baseArr = [275, 112, 81, 45, 8])
    ∧ (ordB bs wA 2 = true ∧ ordB bs wB 5 = true ∧ ordB bs (patW wA wB [false, true]) 11 = true ∧
      ordB bs (patW wA wB commPat) 5 = true)
    ∧ ((∀ c ∈ cl, ordB bs c.1 2 = true) ∧
      (∀ c ∈ cl, closureOK levels bs gens gensInv c.1 c.2.1 c.2.2.1 c.2.2.2 = true) ∧
      keysDistinctNF 275 levels bs (cl.map fun c => c.2.1) = true ∧
      (cl.map fun c => c.2.1.size).sum = 22275) := by
  have srt := keysK_sound
    (cs := [(PMcLC.c0, nfKeyX 275 9 PMcL.LR PMcL.TR 5 bs PMcLC.XT0 108)]) (by decide) (by decide)
    PMcLC.hsrt
  have hD0 := nodup_of_strictInc_mergeSort srt
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hD0
  have cl0 := ClP.closNF_proved (bs := bs) (rep := wA) binds perm PMcL.hl rfl hg rep0_eq ok0 hD0
  refine ⟨⟨?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [words_eq]
    exact rawChainK_sound (NS := 18) (CH := 16) binds PMcL.head PMcL.hl (by decide) PMcL.hs
  · rw [rawOrbitSizesK_sound binds perm PMcL.hl]
    decide +kernel
  · have e3 : patW [unpack 275 9 (PMcL.S 0)] [unpack 275 9 (PMcL.S 1)] [false, true] =
        [PMcL.S 1, PMcL.S 0].map (unpack 275 9) := rfl
    have e4 : patW [unpack 275 9 (PMcL.S 0)] [unpack 275 9 (PMcL.S 1)] commPat =
        [PMcL.S 1, PMcL.S 1, PMcL.S 1, PMcL.S 1, PMcL.S 0, PMcL.S 1, PMcL.S 0].map (unpack 275 9) :=
      rfl
    have e1 : [unpack 275 9 (PMcL.S 0)] = [PMcL.S 0].map (unpack 275 9) := rfl
    have e2 : [unpack 275 9 (PMcL.S 1)] = [PMcL.S 1].map (unpack 275 9) := rfl
    rw [wA_eq, wB_eq, e3, e4, e1, e2]
    exact ⟨ordWK_sound o1, ordWK_sound o2, ordWK_sound o3, ordWK_sound o4⟩
  · intro c hc
    rw [cl_eq] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    rw [rep0_eq]
    exact ordWK_sound o0
  · intro c hc
    rw [cl_eq] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    exact cl0.1
  · rw [cl_eq]
    unfold keysDistinctNF
    simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [closureOf, PairMcL.levels, cl0.2.2]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at srt
    exact srt
  · rw [cl_eq]
    refine sum_one ?_
    rw [closureOf, PairMcL.levels, cl0.2.1]
    exact Nat.eq_of_beq_eq_true sSz

end CertificateChecks.KernelSporSch.PMcLCheck

end
