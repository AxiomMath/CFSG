module

public import CFSG.Certificates.Kernel.Misc.F42Sound
public import Certificates.Kernel.Misc.F42Data
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 200000

namespace CFSG.KD.Misc.F42

open CFSG.KC.Misc CFSG.KC.Misc.F42 CFSG.LieType.Multipliers.F42 CFSG.Blueprint.Chevalley
open CFSG.KS.PK (pairsSwapChunk)

theorem bA : payloadA = strOf cA := rfl
theorem bB : payloadB = strOf cB := rfl
theorem bS : slpText = strOf cS := rfl
theorem bRefs : liftRefs = LR.map refOfCode := by decide +kernel
theorem bRoots : f4ArtifactRoots = RL.map (List.map fun n : ℕ => (n : ℤ) - 32) := by decide +kernel
theorem fmt : fmtK cS = true := by quickRfl
theorem ints : eqLN (intsK cS) Rc = true := by quickRfl
theorem start : startK cA cB F I = true := by quickRfl
theorem nIeq : 508 = lenN Rc / 2 := by decide +kernel
theorem lenF : Nat.beq (lenN F) (508 + 2) = true := by quickRfl
theorem liftsChk : liftsK F I LR LF LI (508 + 2) = true := by quickRfl
theorem roots : rootsK RL RC = true := by quickRfl
theorem neg : negK LF LI RC 0 35 = true := by quickRfl
theorem ins0 : insChunk F I Rc 508 0 16 = true := by quickRfl
theorem ins1 : insChunk F I Rc 508 16 16 = true := by quickRfl
theorem ins2 : insChunk F I Rc 508 32 16 = true := by quickRfl
theorem ins3 : insChunk F I Rc 508 48 16 = true := by quickRfl
theorem ins4 : insChunk F I Rc 508 64 16 = true := by quickRfl
theorem ins5 : insChunk F I Rc 508 80 16 = true := by quickRfl
theorem ins6 : insChunk F I Rc 508 96 16 = true := by quickRfl
theorem ins7 : insChunk F I Rc 508 112 16 = true := by quickRfl
theorem ins8 : insChunk F I Rc 508 128 16 = true := by quickRfl
theorem ins9 : insChunk F I Rc 508 144 16 = true := by quickRfl
theorem ins10 : insChunk F I Rc 508 160 16 = true := by quickRfl
theorem ins11 : insChunk F I Rc 508 176 16 = true := by quickRfl
theorem ins12 : insChunk F I Rc 508 192 16 = true := by quickRfl
theorem ins13 : insChunk F I Rc 508 208 16 = true := by quickRfl
theorem ins14 : insChunk F I Rc 508 224 16 = true := by quickRfl
theorem ins15 : insChunk F I Rc 508 240 16 = true := by quickRfl
theorem ins16 : insChunk F I Rc 508 256 16 = true := by quickRfl
theorem ins17 : insChunk F I Rc 508 272 16 = true := by quickRfl
theorem ins18 : insChunk F I Rc 508 288 16 = true := by quickRfl
theorem ins19 : insChunk F I Rc 508 304 16 = true := by quickRfl
theorem ins20 : insChunk F I Rc 508 320 16 = true := by quickRfl
theorem ins21 : insChunk F I Rc 508 336 16 = true := by quickRfl
theorem ins22 : insChunk F I Rc 508 352 16 = true := by quickRfl
theorem ins23 : insChunk F I Rc 508 368 16 = true := by quickRfl
theorem ins24 : insChunk F I Rc 508 384 16 = true := by quickRfl
theorem ins25 : insChunk F I Rc 508 400 16 = true := by quickRfl
theorem ins26 : insChunk F I Rc 508 416 16 = true := by quickRfl
theorem ins27 : insChunk F I Rc 508 432 16 = true := by quickRfl
theorem ins28 : insChunk F I Rc 508 448 16 = true := by quickRfl
theorem ins29 : insChunk F I Rc 508 464 16 = true := by quickRfl
theorem ins30 : insChunk F I Rc 508 480 16 = true := by quickRfl
theorem ins31 : insChunk F I Rc 508 496 16 = true := by quickRfl
theorem lift0 : liftK LF LI 0 = true := by quickRfl
theorem lift1 : liftK LF LI 1 = true := by quickRfl
theorem lift2 : liftK LF LI 2 = true := by quickRfl
theorem lift3 : liftK LF LI 3 = true := by quickRfl
theorem lift4 : liftK LF LI 4 = true := by quickRfl
theorem lift5 : liftK LF LI 5 = true := by quickRfl
theorem lift6 : liftK LF LI 6 = true := by quickRfl
theorem lift7 : liftK LF LI 7 = true := by quickRfl
theorem lift8 : liftK LF LI 8 = true := by quickRfl
theorem lift9 : liftK LF LI 9 = true := by quickRfl
theorem lift10 : liftK LF LI 10 = true := by quickRfl
theorem lift11 : liftK LF LI 11 = true := by quickRfl
theorem lift12 : liftK LF LI 12 = true := by quickRfl
theorem lift13 : liftK LF LI 13 = true := by quickRfl
theorem lift14 : liftK LF LI 14 = true := by quickRfl
theorem lift15 : liftK LF LI 15 = true := by quickRfl
theorem lift16 : liftK LF LI 16 = true := by quickRfl
theorem lift17 : liftK LF LI 17 = true := by quickRfl
theorem lift18 : liftK LF LI 18 = true := by quickRfl
theorem lift19 : liftK LF LI 19 = true := by quickRfl
theorem lift20 : liftK LF LI 20 = true := by quickRfl
theorem lift21 : liftK LF LI 21 = true := by quickRfl
theorem lift22 : liftK LF LI 22 = true := by quickRfl
theorem lift23 : liftK LF LI 23 = true := by quickRfl
theorem lift24 : liftK LF LI 24 = true := by quickRfl
theorem lift25 : liftK LF LI 25 = true := by quickRfl
theorem lift26 : liftK LF LI 26 = true := by quickRfl
theorem lift27 : liftK LF LI 27 = true := by quickRfl
theorem lift28 : liftK LF LI 28 = true := by quickRfl
theorem lift29 : liftK LF LI 29 = true := by quickRfl
theorem lift30 : liftK LF LI 30 = true := by quickRfl
theorem lift31 : liftK LF LI 31 = true := by quickRfl
theorem lift32 : liftK LF LI 32 = true := by quickRfl
theorem lift33 : liftK LF LI 33 = true := by quickRfl
theorem lift34 : liftK LF LI 34 = true := by quickRfl
theorem lift35 : liftK LF LI 35 = true := by quickRfl
theorem lift36 : liftK LF LI 36 = true := by quickRfl
theorem lift37 : liftK LF LI 37 = true := by quickRfl
theorem lift38 : liftK LF LI 38 = true := by quickRfl
theorem lift39 : liftK LF LI 39 = true := by quickRfl
theorem lift40 : liftK LF LI 40 = true := by quickRfl
theorem lift41 : liftK LF LI 41 = true := by quickRfl
theorem lift42 : liftK LF LI 42 = true := by quickRfl
theorem lift43 : liftK LF LI 43 = true := by quickRfl
theorem lift44 : liftK LF LI 44 = true := by quickRfl
theorem lift45 : liftK LF LI 45 = true := by quickRfl
theorem lift46 : liftK LF LI 46 = true := by quickRfl
theorem lift47 : liftK LF LI 47 = true := by quickRfl
theorem pairSwap0 : pairsSwapChunk LF RC 0 = true := by quickRfl
theorem pairSwap1 : pairsSwapChunk LF RC 1 = true := by quickRfl
theorem pairSwap2 : pairsSwapChunk LF RC 2 = true := by quickRfl
theorem pairSwap3 : pairsSwapChunk LF RC 3 = true := by quickRfl
theorem pairSwap4 : pairsSwapChunk LF RC 4 = true := by quickRfl
theorem pairSwap5 : pairsSwapChunk LF RC 5 = true := by quickRfl
theorem pairSwap6 : pairsSwapChunk LF RC 6 = true := by quickRfl
theorem pairSwap7 : pairsSwapChunk LF RC 7 = true := by quickRfl
theorem pairSwap8 : pairsSwapChunk LF RC 8 = true := by quickRfl
theorem pairSwap9 : pairsSwapChunk LF RC 9 = true := by quickRfl
theorem pairSwap10 : pairsSwapChunk LF RC 10 = true := by quickRfl
theorem pairSwap11 : pairsSwapChunk LF RC 11 = true := by quickRfl
theorem pairSwap12 : pairsSwapChunk LF RC 12 = true := by quickRfl
theorem pairSwap13 : pairsSwapChunk LF RC 13 = true := by quickRfl
theorem pairSwap14 : pairsSwapChunk LF RC 14 = true := by quickRfl
theorem pairSwap15 : pairsSwapChunk LF RC 15 = true := by quickRfl
theorem pairSwap16 : pairsSwapChunk LF RC 16 = true := by quickRfl
theorem pairSwap17 : pairsSwapChunk LF RC 17 = true := by quickRfl
theorem pairSwap18 : pairsSwapChunk LF RC 18 = true := by quickRfl
theorem pairSwap19 : pairsSwapChunk LF RC 19 = true := by quickRfl
theorem pairSwap20 : pairsSwapChunk LF RC 20 = true := by quickRfl
theorem pairSwap21 : pairsSwapChunk LF RC 21 = true := by quickRfl
theorem pairSwap22 : pairsSwapChunk LF RC 22 = true := by quickRfl
theorem pairSwap23 : pairsSwapChunk LF RC 23 = true := by quickRfl
theorem pairSwap24 : pairsSwapChunk LF RC 24 = true := by quickRfl
theorem pairSwap25 : pairsSwapChunk LF RC 25 = true := by quickRfl
theorem pairSwap26 : pairsSwapChunk LF RC 26 = true := by quickRfl
theorem pairSwap27 : pairsSwapChunk LF RC 27 = true := by quickRfl
theorem pairSwap28 : pairsSwapChunk LF RC 28 = true := by quickRfl
theorem pairSwap29 : pairsSwapChunk LF RC 29 = true := by quickRfl
theorem pairSwap30 : pairsSwapChunk LF RC 30 = true := by quickRfl
theorem pairSwap31 : pairsSwapChunk LF RC 31 = true := by quickRfl
theorem pairSwap32 : pairsSwapChunk LF RC 32 = true := by quickRfl
theorem pairSwap33 : pairsSwapChunk LF RC 33 = true := by quickRfl
theorem pairSwap34 : pairsSwapChunk LF RC 34 = true := by quickRfl
theorem pairSwap35 : pairsSwapChunk LF RC 35 = true := by quickRfl
theorem pairSwap36 : pairsSwapChunk LF RC 36 = true := by quickRfl
theorem pairSwap37 : pairsSwapChunk LF RC 37 = true := by quickRfl
theorem pairSwap38 : pairsSwapChunk LF RC 38 = true := by quickRfl
theorem pairSwap39 : pairsSwapChunk LF RC 39 = true := by quickRfl
theorem pairSwap40 : pairsSwapChunk LF RC 40 = true := by quickRfl
theorem pairSwap41 : pairsSwapChunk LF RC 41 = true := by quickRfl
theorem pairSwap42 : pairsSwapChunk LF RC 42 = true := by quickRfl
theorem pairSwap43 : pairsSwapChunk LF RC 43 = true := by quickRfl
theorem pairSwap44 : pairsSwapChunk LF RC 44 = true := by quickRfl
theorem pairSwap45 : pairsSwapChunk LF RC 45 = true := by quickRfl
theorem pairSwap46 : pairsSwapChunk LF RC 46 = true := by quickRfl
theorem pairSwap47 : pairsSwapChunk LF RC 47 = true := by quickRfl
theorem word0 : wordK LF LI RC 0 (commPairs.getD 0 (0, 0)).1 (commPairs.getD 0 (0, 0)).2 = true := by
  quickRfl
theorem word1 : wordK LF LI RC 1 (commPairs.getD 1 (0, 0)).1 (commPairs.getD 1 (0, 0)).2 = true := by
  quickRfl
theorem word2 : wordK LF LI RC 2 (commPairs.getD 2 (0, 0)).1 (commPairs.getD 2 (0, 0)).2 = true := by
  quickRfl
theorem word3 : wordK LF LI RC 3 (commPairs.getD 3 (0, 0)).1 (commPairs.getD 3 (0, 0)).2 = true := by
  quickRfl
theorem word4 : wordK LF LI RC 4 (commPairs.getD 4 (0, 0)).1 (commPairs.getD 4 (0, 0)).2 = true := by
  quickRfl
theorem word5 : wordK LF LI RC 5 (commPairs.getD 5 (0, 0)).1 (commPairs.getD 5 (0, 0)).2 = true := by
  quickRfl
theorem word6 : wordK LF LI RC 6 (commPairs.getD 6 (0, 0)).1 (commPairs.getD 6 (0, 0)).2 = true := by
  quickRfl
theorem word7 : wordK LF LI RC 7 (commPairs.getD 7 (0, 0)).1 (commPairs.getD 7 (0, 0)).2 = true := by
  quickRfl
theorem word8 : wordK LF LI RC 8 (commPairs.getD 8 (0, 0)).1 (commPairs.getD 8 (0, 0)).2 = true := by
  quickRfl
theorem word9 : wordK LF LI RC 9 (commPairs.getD 9 (0, 0)).1 (commPairs.getD 9 (0, 0)).2 = true := by
  quickRfl
theorem word10 : wordK LF LI RC 10 (commPairs.getD 10 (0, 0)).1 (commPairs.getD 10 (0, 0)).2 = true := by
  quickRfl
theorem word11 : wordK LF LI RC 11 (commPairs.getD 11 (0, 0)).1 (commPairs.getD 11 (0, 0)).2 = true := by
  quickRfl
theorem word12 : wordK LF LI RC 12 (commPairs.getD 12 (0, 0)).1 (commPairs.getD 12 (0, 0)).2 = true := by
  quickRfl
theorem word13 : wordK LF LI RC 13 (commPairs.getD 13 (0, 0)).1 (commPairs.getD 13 (0, 0)).2 = true := by
  quickRfl
theorem word14 : wordK LF LI RC 14 (commPairs.getD 14 (0, 0)).1 (commPairs.getD 14 (0, 0)).2 = true := by
  quickRfl
theorem word15 : wordK LF LI RC 15 (commPairs.getD 15 (0, 0)).1 (commPairs.getD 15 (0, 0)).2 = true := by
  quickRfl
theorem word16 : wordK LF LI RC 16 (commPairs.getD 16 (0, 0)).1 (commPairs.getD 16 (0, 0)).2 = true := by
  quickRfl
theorem word17 : wordK LF LI RC 17 (commPairs.getD 17 (0, 0)).1 (commPairs.getD 17 (0, 0)).2 = true := by
  quickRfl
theorem word18 : wordK LF LI RC 18 (commPairs.getD 18 (0, 0)).1 (commPairs.getD 18 (0, 0)).2 = true := by
  quickRfl
theorem word19 : wordK LF LI RC 19 (commPairs.getD 19 (0, 0)).1 (commPairs.getD 19 (0, 0)).2 = true := by
  quickRfl
theorem word20 : wordK LF LI RC 20 (commPairs.getD 20 (0, 0)).1 (commPairs.getD 20 (0, 0)).2 = true := by
  quickRfl
theorem word21 : wordK LF LI RC 21 (commPairs.getD 21 (0, 0)).1 (commPairs.getD 21 (0, 0)).2 = true := by
  quickRfl
theorem word22 : wordK LF LI RC 22 (commPairs.getD 22 (0, 0)).1 (commPairs.getD 22 (0, 0)).2 = true := by
  quickRfl
theorem word23 : wordK LF LI RC 23 (commPairs.getD 23 (0, 0)).1 (commPairs.getD 23 (0, 0)).2 = true := by
  quickRfl
theorem word24 : wordK LF LI RC 24 (commPairs.getD 24 (0, 0)).1 (commPairs.getD 24 (0, 0)).2 = true := by
  quickRfl
theorem word25 : wordK LF LI RC 25 (commPairs.getD 25 (0, 0)).1 (commPairs.getD 25 (0, 0)).2 = true := by
  quickRfl
theorem word26 : wordK LF LI RC 26 (commPairs.getD 26 (0, 0)).1 (commPairs.getD 26 (0, 0)).2 = true := by
  quickRfl
theorem word27 : wordK LF LI RC 27 (commPairs.getD 27 (0, 0)).1 (commPairs.getD 27 (0, 0)).2 = true := by
  quickRfl
theorem word28 : wordK LF LI RC 28 (commPairs.getD 28 (0, 0)).1 (commPairs.getD 28 (0, 0)).2 = true := by
  quickRfl
theorem word29 : wordK LF LI RC 29 (commPairs.getD 29 (0, 0)).1 (commPairs.getD 29 (0, 0)).2 = true := by
  quickRfl
theorem word30 : wordK LF LI RC 30 (commPairs.getD 30 (0, 0)).1 (commPairs.getD 30 (0, 0)).2 = true := by
  quickRfl
theorem word31 : wordK LF LI RC 31 (commPairs.getD 31 (0, 0)).1 (commPairs.getD 31 (0, 0)).2 = true := by
  quickRfl
theorem word32 : wordK LF LI RC 32 (commPairs.getD 32 (0, 0)).1 (commPairs.getD 32 (0, 0)).2 = true := by
  quickRfl
theorem word33 : wordK LF LI RC 33 (commPairs.getD 33 (0, 0)).1 (commPairs.getD 33 (0, 0)).2 = true := by
  quickRfl
theorem word34 : wordK LF LI RC 34 (commPairs.getD 34 (0, 0)).1 (commPairs.getD 34 (0, 0)).2 = true := by
  quickRfl
theorem word35 : wordK LF LI RC 35 (commPairs.getD 35 (0, 0)).1 (commPairs.getD 35 (0, 0)).2 = true := by
  quickRfl
theorem word36 : wordK LF LI RC 36 (commPairs.getD 36 (0, 0)).1 (commPairs.getD 36 (0, 0)).2 = true := by
  quickRfl
theorem word37 : wordK LF LI RC 37 (commPairs.getD 37 (0, 0)).1 (commPairs.getD 37 (0, 0)).2 = true := by
  quickRfl
theorem word38 : wordK LF LI RC 38 (commPairs.getD 38 (0, 0)).1 (commPairs.getD 38 (0, 0)).2 = true := by
  quickRfl
theorem word39 : wordK LF LI RC 39 (commPairs.getD 39 (0, 0)).1 (commPairs.getD 39 (0, 0)).2 = true := by
  quickRfl
theorem word40 : wordK LF LI RC 40 (commPairs.getD 40 (0, 0)).1 (commPairs.getD 40 (0, 0)).2 = true := by
  quickRfl
theorem word41 : wordK LF LI RC 41 (commPairs.getD 41 (0, 0)).1 (commPairs.getD 41 (0, 0)).2 = true := by
  quickRfl
theorem word42 : wordK LF LI RC 42 (commPairs.getD 42 (0, 0)).1 (commPairs.getD 42 (0, 0)).2 = true := by
  quickRfl
theorem word43 : wordK LF LI RC 43 (commPairs.getD 43 (0, 0)).1 (commPairs.getD 43 (0, 0)).2 = true := by
  quickRfl
theorem word44 : wordK LF LI RC 44 (commPairs.getD 44 (0, 0)).1 (commPairs.getD 44 (0, 0)).2 = true := by
  quickRfl
theorem word45 : wordK LF LI RC 45 (commPairs.getD 45 (0, 0)).1 (commPairs.getD 45 (0, 0)).2 = true := by
  quickRfl
theorem word46 : wordK LF LI RC 46 (commPairs.getD 46 (0, 0)).1 (commPairs.getD 46 (0, 0)).2 = true := by
  quickRfl
theorem word47 : wordK LF LI RC 47 (commPairs.getD 47 (0, 0)).1 (commPairs.getD 47 (0, 0)).2 = true := by
  quickRfl
theorem insAll : ∀ c < 32, insChunk F I Rc 508 (16 * c) 16 = true := by
  intro c hc
  interval_cases c
  exacts [ins0, ins1, ins2, ins3, ins4, ins5, ins6, ins7, ins8, ins9, ins10, ins11, ins12, ins13, ins14, ins15, ins16, ins17, ins18, ins19, ins20, ins21, ins22, ins23, ins24, ins25, ins26, ins27, ins28, ins29, ins30, ins31]
theorem liftAll : ∀ c < 48, liftK LF LI c = true := by
  intro c hc
  interval_cases c
  exacts [lift0, lift1, lift2, lift3, lift4, lift5, lift6, lift7, lift8, lift9, lift10, lift11, lift12, lift13, lift14, lift15, lift16, lift17, lift18, lift19, lift20, lift21, lift22, lift23, lift24, lift25, lift26, lift27, lift28, lift29, lift30, lift31, lift32, lift33, lift34, lift35, lift36, lift37, lift38, lift39, lift40, lift41, lift42, lift43, lift44, lift45, lift46, lift47]
theorem pairSwapAll : ∀ c < 48, pairsSwapChunk LF RC c = true := by
  intro c hc
  interval_cases c
  exacts [pairSwap0, pairSwap1, pairSwap2, pairSwap3, pairSwap4, pairSwap5, pairSwap6, pairSwap7,
    pairSwap8, pairSwap9, pairSwap10, pairSwap11, pairSwap12, pairSwap13, pairSwap14, pairSwap15,
    pairSwap16, pairSwap17, pairSwap18, pairSwap19, pairSwap20, pairSwap21, pairSwap22, pairSwap23,
    pairSwap24, pairSwap25, pairSwap26, pairSwap27, pairSwap28, pairSwap29, pairSwap30, pairSwap31,
    pairSwap32, pairSwap33, pairSwap34, pairSwap35, pairSwap36, pairSwap37, pairSwap38, pairSwap39,
    pairSwap40, pairSwap41, pairSwap42, pairSwap43, pairSwap44, pairSwap45, pairSwap46, pairSwap47]
theorem wordAll : ∀ c < 48, wordK LF LI RC c (commPairs.getD c (0, 0)).1 (commPairs.getD c (0, 0)).2 = true := by
  intro c hc
  interval_cases c
  exacts [word0, word1, word2, word3, word4, word5, word6, word7, word8, word9, word10, word11, word12, word13, word14, word15, word16, word17, word18, word19, word20, word21, word22, word23, word24, word25, word26, word27, word28, word29, word30, word31, word32, word33, word34, word35, word36, word37, word38, word39, word40, word41, word42, word43, word44, word45, word46, word47]

end CFSG.KD.Misc.F42

end
