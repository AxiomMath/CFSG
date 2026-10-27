module

public import Certificates.Kernel.SporSch.PairHe.ClAll
public import Certificates.Kernel.SporSch.PairHe.Blocks
public import CFSG.Certificates.Kernel.SporSch.PairKSound
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.SporSch.PairClTProof
public import CFSG.Sporadic.Schreier.PairHeCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.Sporadic.Schreier.ImagePairs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.PHeCheck

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.Schreier.PairHe
open CFSG.Sporadic.HeldB CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CertificateChecks.KernelSporSch CertificateChecks.KernelSpor

theorem gen_eq (l : Nat) (hl : l < 2) : heGen l = unpack 8330 14 (HeC.S l) := by
  have h := He2112.gen_eq l hl
  rw [heGenArrs, getElem!_pos _ l (by simpa using hl), Array.getElem_ofFn] at h
  exact h

theorem inv_eq (l : Nat) (hl : l < 2) : invCand 8330 (heGen l) = unpack 8330 14 (HeC.SI l) := by
  rw [gen_eq l hl]
  exact (invEqK_sound (allN_spec He2112.perm l (by omega))).1

theorem letter_eq (l : Nat) (hl : l < 2) : letterK HeC.S HeC.SI 9 (PHeCl.gl l) = HeC.S l ∧
    letterK HeC.S HeC.SI 9 (invL 9 (PHeCl.gl l)) = HeC.SI l := by
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

theorem hg : gens.size = 2 ∧ gensInv.size = 2 ∧
    ∀ l < 2, gens[l]! = unpack 8330 14 (letterK HeC.S HeC.SI 9 (PHeCl.gl l)) ∧
      gensInv[l]! = unpack 8330 14 (letterK HeC.S HeC.SI 9 (invL 9 (PHeCl.gl l))) := by
  refine ⟨rfl, rfl, fun l hl => ?_⟩
  rw [(letter_eq l hl).1, (letter_eq l hl).2, ← gen_eq l hl, ← inv_eq l hl]
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · exact ⟨by simp [gens], by simp [gensInv]⟩
  · exact ⟨by simp [gens], by simp [gensInv]⟩

theorem wA_eq : wA = [unpack 8330 14 (HeC.S 0)] := by
  rw [wA, gen_eq 0 (by omega)]

theorem wB_eq : wB = [unpack 8330 14 (HeC.S 1)] := by
  rw [wB, gen_eq 1 (by omega)]

theorem tabs : TabsT 8330 14 9 5 HeC.BP PHeT.NR PHeT.NR HeC.S HeC.SI HeC.LR PHeT.Ts PHeT.LT
    PHeT.PT PHeT.QT 147 1024 9 1024 :=
  ⟨by decide, by decide, by decide, by decide, PHeCl.TS.all, PHeCl.LTc.all, PHeCl.ptB_all,
    PHeCl.qtB_all⟩

theorem okA : ClosNFT 8330 14 9 5 PHeT.NR PHeT.NR HeC.LR PHeT.LT PHeT.PT PHeT.QT bs 2 PHeCl.gl
    PHeCl.RPA PHeT.c 200000 98 8 32 49 64 PHeCl.XA PHeCl.WA PHeCl.KA PHeT.C PHeCl.SOA
    PHeCl.SOIA :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    PHeCl.canonA, PHeCl.ltbs, PHeCl.stA, PHeCl.kA, PHeCl.recA_all, PHeCl.srtA_all,
    Nat.eq_of_beq_eq_true PHeCl.cA0, Nat.eq_of_beq_eq_true PHeCl.cAN, PHeCl.runA_all⟩

theorem okB : ClosNFT 8330 14 9 5 PHeT.NR PHeT.NR HeC.LR PHeT.LT PHeT.PT PHeT.QT bs 2 PHeCl.gl
    PHeCl.RPB PHeU.c 200000 733 8 32 367 64 PHeCl.XB PHeCl.WB PHeCl.KB PHeU.C PHeCl.SOB
    PHeCl.SOIB :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    PHeCl.canonB, PHeCl.ltbs, PHeCl.stB, PHeCl.kB, PHeCl.recB_all, PHeCl.srtB_all,
    Nat.eq_of_beq_eq_true PHeCl.cB0, Nat.eq_of_beq_eq_true PHeCl.cBN, PHeCl.runB_all⟩

theorem repA_eq : wA = PHeCl.RPA.map (unpack 8330 14) := wA_eq

theorem repB_eq : wT = PHeCl.RPB.map (unpack 8330 14) := by
  rw [wT, wA_eq, wB_eq]
  rfl

theorem cl_eq : cl = [(wA, closureOf wA), (wT, closureOf wT)] := rfl

theorem o1 : ordWK 8330 14 bs [HeC.S 0] 2 = true := by quickRfl
theorem o2 : ordWK 8330 14 bs [HeC.S 1] 7 = true := by quickRfl
theorem o3 : ordWK 8330 14 bs [HeC.S 1, HeC.S 0] 17 = true := by quickRfl
theorem o4 : ordWK 8330 14 bs [HeC.S 1, HeC.S 1, HeC.S 1, HeC.S 1, HeC.S 1, HeC.S 1, HeC.S 0,
    HeC.S 1, HeC.S 0] 6 = true := by
  quickRfl
theorem o5 : ordWK 8330 14 bs [HeC.S 1, HeC.S 1, HeC.S 0] 12 = true := by quickRfl
theorem o6 : ordWK 8330 14 bs [HeC.S 1, HeC.S 1, HeC.S 0, HeC.S 1, HeC.S 0] 15 = true := by
  quickRfl
theorem oT : ordWK 8330 14 bs PHeCl.RPB 2 = true := by quickRfl

set_option maxHeartbeats 4000000 in
theorem facts :
    (ordB bs wA 2 = true ∧ ordB bs wB 7 = true ∧ ordB bs (patW wA wB [false, true]) 17 = true ∧
      ordB bs (patW wA wB commPat) 6 = true ∧ ordB bs (patW wA wB pat12) 12 = true ∧
      ordB bs (patW wA wB pat15) 15 = true)
    ∧ (heBlocks.map Array.size = [8330, 4480, 108])
    ∧ ((∀ c ∈ cl, ordB bs c.1 2 = true) ∧
      (∀ c ∈ cl, closureOK levels bs gens gensInv c.1 c.2.1 c.2.2.1 c.2.2.2 = true) ∧
      keysDistinctNF 8330 levels bs (cl.map fun c => c.2.1) = true ∧
      (cl.map fun c => c.2.1.size) = [24990, 187425]) := by
  have clA := ClTP.closNFT_proved (bs := bs) (rep := wA) He2112.binds He2112.perm HeC.ho (by decide)
    tabs rfl hg repA_eq okA
  have clB := ClTP.closNFT_proved (bs := bs) (rep := wT) He2112.binds He2112.perm HeC.ho (by decide)
    tabs rfl hg repB_eq okB
  have srt := keysK_sound (cs := [(PHeT.c, PHeCl.KA), (PHeU.c, PHeCl.KB)]) (nB := 415) (R := 8)
    (B := 64) (by simp) (by decide) PHeCl.jsrt_all
  have hA : closureOf wA = conjClosureNF 8330 (rawLevels 8330 heStrongArrs heBase.toArray) bs gens
      gensInv (decodeNF (rawLevels 8330 heStrongArrs heBase.toArray) (baseImgs bs wA).toArray)
      200000 := rfl
  have hT : closureOf wT = conjClosureNF 8330 (rawLevels 8330 heStrongArrs heBase.toArray) bs gens
      gensInv (decodeNF (rawLevels 8330 heStrongArrs heBase.toArray) (baseImgs bs wT).toArray)
      200000 := rfl
  have hlv : PairHe.levels = rawLevels 8330 heStrongArrs heBase.toArray := rfl
  have oA : ordB bs wA 2 = true := by
    rw [repA_eq]
    exact ordWK_sound o1
  have oT' : ordB bs wT 2 = true := by
    rw [repB_eq]
    exact ordWK_sound oT
  generalize conjClosureNF 8330 (rawLevels 8330 heStrongArrs heBase.toArray) bs gens gensInv
    (decodeNF (rawLevels 8330 heStrongArrs heBase.toArray) (baseImgs bs wA).toArray) 200000 = EA
    at clA hA
  generalize conjClosureNF 8330 (rawLevels 8330 heStrongArrs heBase.toArray) bs gens gensInv
    (decodeNF (rawLevels 8330 heStrongArrs heBase.toArray) (baseImgs bs wT).toArray) 200000 = EB
    at clB hT
  refine ⟨?_, PHeBlocks.block_sizes, ⟨?_, ?_, ?_, ?_⟩⟩
  · have e2 : [unpack 8330 14 (HeC.S 1)] = [HeC.S 1].map (unpack 8330 14) := rfl
    have e3 : patW [unpack 8330 14 (HeC.S 0)] [unpack 8330 14 (HeC.S 1)] [false, true] =
        [HeC.S 1, HeC.S 0].map (unpack 8330 14) := rfl
    have e4 : patW [unpack 8330 14 (HeC.S 0)] [unpack 8330 14 (HeC.S 1)] commPat =
        [HeC.S 1, HeC.S 1, HeC.S 1, HeC.S 1, HeC.S 1, HeC.S 1, HeC.S 0, HeC.S 1, HeC.S 0].map
          (unpack 8330 14) := rfl
    have e5 : patW [unpack 8330 14 (HeC.S 0)] [unpack 8330 14 (HeC.S 1)] pat12 =
        [HeC.S 1, HeC.S 1, HeC.S 0].map (unpack 8330 14) := rfl
    have e6 : patW [unpack 8330 14 (HeC.S 0)] [unpack 8330 14 (HeC.S 1)] pat15 =
        [HeC.S 1, HeC.S 1, HeC.S 0, HeC.S 1, HeC.S 0].map (unpack 8330 14) := rfl
    refine ⟨oA, ?_, ?_, ?_, ?_, ?_⟩
    · rw [wB_eq, e2]
      exact ordWK_sound o2
    · rw [wA_eq, wB_eq, e3]
      exact ordWK_sound o3
    · rw [wA_eq, wB_eq, e4]
      exact ordWK_sound o4
    · rw [wA_eq, wB_eq, e5]
      exact ordWK_sound o5
    · rw [wA_eq, wB_eq, e6]
      exact ordWK_sound o6
  · intro c hc
    rw [cl_eq] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact oA
    · exact oT'
  · intro c hc
    rw [cl_eq] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · dsimp only
      rw [hA, hlv]
      exact clA.1
    · dsimp only
      rw [hT, hlv]
      exact clB.1
  · rw [cl_eq]
    simp only [List.map_cons, List.map_nil]
    rw [hA, hT, hlv]
    unfold keysDistinctNF
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [clA.2.2, clB.2.2]
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using srt
  · rw [cl_eq]
    simp only [List.map_cons, List.map_nil]
    rw [hA, hT, clA.2.1, clB.2.1, Nat.eq_of_beq_eq_true PHeCl.cASz,
      Nat.eq_of_beq_eq_true PHeCl.cBSz]

end CertificateChecks.KernelSporSch.PHeCheck

end
