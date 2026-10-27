module

public import CFSG.Certificates.Kernel.Misc.F42Sound
public import Certificates.Kernel.Misc.F42Data
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 200000

namespace CFSG.KD.Misc.F42

open CFSG.KC.Misc CFSG.KC.Misc.F42 CFSG.LieType.Multipliers.F42 CFSG.Blueprint.Chevalley

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
theorem pair0 : pairsChunk LF LI RC 0 1 = true := by quickRfl
theorem pair1 : pairsChunk LF LI RC 1 1 = true := by quickRfl
theorem pair2 : pairsChunk LF LI RC 2 1 = true := by quickRfl
theorem pair3 : pairsChunk LF LI RC 3 1 = true := by quickRfl
theorem pair4 : pairsChunk LF LI RC 4 1 = true := by quickRfl
theorem pair5 : pairsChunk LF LI RC 5 1 = true := by quickRfl
theorem pair6 : pairsChunk LF LI RC 6 1 = true := by quickRfl
theorem pair7 : pairsChunk LF LI RC 7 1 = true := by quickRfl
theorem pair8 : pairsChunk LF LI RC 8 1 = true := by quickRfl
theorem pair9 : pairsChunk LF LI RC 9 1 = true := by quickRfl
theorem pair10 : pairsChunk LF LI RC 10 1 = true := by quickRfl
theorem pair11 : pairsChunk LF LI RC 11 1 = true := by quickRfl
theorem pair12 : pairsChunk LF LI RC 12 1 = true := by quickRfl
theorem pair13 : pairsChunk LF LI RC 13 1 = true := by quickRfl
theorem pair14 : pairsChunk LF LI RC 14 1 = true := by quickRfl
theorem pair15 : pairsChunk LF LI RC 15 1 = true := by quickRfl
theorem pair16 : pairsChunk LF LI RC 16 1 = true := by quickRfl
theorem pair17 : pairsChunk LF LI RC 17 1 = true := by quickRfl
theorem pair18 : pairsChunk LF LI RC 18 1 = true := by quickRfl
theorem pair19 : pairsChunk LF LI RC 19 1 = true := by quickRfl
theorem pair20 : pairsChunk LF LI RC 20 1 = true := by quickRfl
theorem pair21 : pairsChunk LF LI RC 21 1 = true := by quickRfl
theorem pair22 : pairsChunk LF LI RC 22 1 = true := by quickRfl
theorem pair23 : pairsChunk LF LI RC 23 1 = true := by quickRfl
theorem pair24 : pairsChunk LF LI RC 24 1 = true := by quickRfl
theorem pair25 : pairsChunk LF LI RC 25 1 = true := by quickRfl
theorem pair26 : pairsChunk LF LI RC 26 1 = true := by quickRfl
theorem pair27 : pairsChunk LF LI RC 27 1 = true := by quickRfl
theorem pair28 : pairsChunk LF LI RC 28 1 = true := by quickRfl
theorem pair29 : pairsChunk LF LI RC 29 1 = true := by quickRfl
theorem pair30 : pairsChunk LF LI RC 30 1 = true := by quickRfl
theorem pair31 : pairsChunk LF LI RC 31 1 = true := by quickRfl
theorem pair32 : pairsChunk LF LI RC 32 1 = true := by quickRfl
theorem pair33 : pairsChunk LF LI RC 33 1 = true := by quickRfl
theorem pair34 : pairsChunk LF LI RC 34 1 = true := by quickRfl
theorem pair35 : pairsChunk LF LI RC 35 1 = true := by quickRfl
theorem pair36 : pairsChunk LF LI RC 36 1 = true := by quickRfl
theorem pair37 : pairsChunk LF LI RC 37 1 = true := by quickRfl
theorem pair38 : pairsChunk LF LI RC 38 1 = true := by quickRfl
theorem pair39 : pairsChunk LF LI RC 39 1 = true := by quickRfl
theorem pair40 : pairsChunk LF LI RC 40 1 = true := by quickRfl
theorem pair41 : pairsChunk LF LI RC 41 1 = true := by quickRfl
theorem pair42 : pairsChunk LF LI RC 42 1 = true := by quickRfl
theorem pair43 : pairsChunk LF LI RC 43 1 = true := by quickRfl
theorem pair44 : pairsChunk LF LI RC 44 1 = true := by quickRfl
theorem pair45 : pairsChunk LF LI RC 45 1 = true := by quickRfl
theorem pair46 : pairsChunk LF LI RC 46 1 = true := by quickRfl
theorem pair47 : pairsChunk LF LI RC 47 1 = true := by quickRfl
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
theorem pairAll : ∀ c < 48, pairsChunk LF LI RC c 1 = true := by
  intro c hc
  interval_cases c
  exacts [pair0, pair1, pair2, pair3, pair4, pair5, pair6, pair7, pair8, pair9, pair10, pair11, pair12, pair13, pair14, pair15, pair16, pair17, pair18, pair19, pair20, pair21, pair22, pair23, pair24, pair25, pair26, pair27, pair28, pair29, pair30, pair31, pair32, pair33, pair34, pair35, pair36, pair37, pair38, pair39, pair40, pair41, pair42, pair43, pair44, pair45, pair46, pair47]
theorem wordAll : ∀ c < 48, wordK LF LI RC c (commPairs.getD c (0, 0)).1 (commPairs.getD c (0, 0)).2 = true := by
  intro c hc
  interval_cases c
  exacts [word0, word1, word2, word3, word4, word5, word6, word7, word8, word9, word10, word11, word12, word13, word14, word15, word16, word17, word18, word19, word20, word21, word22, word23, word24, word25, word26, word27, word28, word29, word30, word31, word32, word33, word34, word35, word36, word37, word38, word39, word40, word41, word42, word43, word44, word45, word46, word47]

end CFSG.KD.Misc.F42

end
