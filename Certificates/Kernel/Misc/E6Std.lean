module

public import Certificates.Data.Kernel.Misc.E6Std
public import CFSG.LieType.Chevalley.C2E6StdMatrixModelInputs
public import CFSG.LieType.Chevalley.C2E6StdMatrixData
public import CFSG.Monster.B.Classical.E6AdjointTable
public import Certificates.Data.CFSGNative.Chevalley.C2E6StdMatrix
public import Certificates.Kernel.Misc.E6StdData
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages

public section

set_option maxRecDepth 100000

namespace CFSG.KD.Misc.E6Std

open CFSG.KC.Misc CFSG.KC.Misc.E6Std CFSG.Monster.B.Classical.E6Adjoint CFSG.LieType.Chevalley.C2E6Std.MatrixModel

theorem let0 : Nat.beq (letterB bracketCodes formBits 0) (nthV Fvals 0) = true := by
  quickRfl
theorem let1 : Nat.beq (letterB bracketCodes formBits 1) (nthV Fvals 1) = true := by
  quickRfl
theorem let2 : Nat.beq (letterB bracketCodes formBits 2) (nthV Fvals 2) = true := by
  quickRfl
theorem let3 : Nat.beq (letterB bracketCodes formBits 3) (nthV Fvals 3) = true := by
  quickRfl
theorem let4 : Nat.beq (letterB bracketCodes formBits 4) (nthV Fvals 4) = true := by
  quickRfl
theorem let5 : Nat.beq (letterB bracketCodes formBits 5) (nthV Fvals 5) = true := by
  quickRfl
theorem let6 : Nat.beq (letterB bracketCodes formBits 6) (nthV Fvals 6) = true := by
  quickRfl
theorem let7 : Nat.beq (letterB bracketCodes formBits 7) (nthV Fvals 7) = true := by
  quickRfl
theorem let8 : Nat.beq (letterB bracketCodes formBits 8) (nthV Fvals 8) = true := by
  quickRfl
theorem let9 : Nat.beq (letterB bracketCodes formBits 9) (nthV Fvals 9) = true := by
  quickRfl
theorem let10 : Nat.beq (letterB bracketCodes formBits 10) (nthV Fvals 10) = true := by
  quickRfl
theorem let11 : Nat.beq (letterB bracketCodes formBits 11) (nthV Fvals 11) = true := by
  quickRfl
theorem fwd0 : slpLine Fvals fwdProg 12 0 = true := by quickRfl
theorem fwd1 : slpLine Fvals fwdProg 12 1 = true := by quickRfl
theorem fwd2 : slpLine Fvals fwdProg 12 2 = true := by quickRfl
theorem bwd0 : slpLine Wvals bwdProg 2 0 = true := by quickRfl
theorem bwd1 : slpLine Wvals bwdProg 2 1 = true := by quickRfl
theorem bwd2 : slpLine Wvals bwdProg 2 2 = true := by quickRfl
theorem bwd3 : slpLine Wvals bwdProg 2 3 = true := by quickRfl
theorem bwd4 : slpLine Wvals bwdProg 2 4 = true := by quickRfl
theorem bwd5 : slpLine Wvals bwdProg 2 5 = true := by quickRfl
theorem bwd6 : slpLine Wvals bwdProg 2 6 = true := by quickRfl
theorem bwd7 : slpLine Wvals bwdProg 2 7 = true := by quickRfl
theorem bwd8 : slpLine Wvals bwdProg 2 8 = true := by quickRfl
theorem bwd9 : slpLine Wvals bwdProg 2 9 = true := by quickRfl
theorem bwd10 : slpLine Wvals bwdProg 2 10 = true := by quickRfl
theorem bwd11 : slpLine Wvals bwdProg 2 11 = true := by quickRfl
theorem bwd12 : slpLine Wvals bwdProg 2 12 = true := by quickRfl
theorem bwd13 : slpLine Wvals bwdProg 2 13 = true := by quickRfl
theorem bwd14 : slpLine Wvals bwdProg 2 14 = true := by quickRfl
theorem bwd15 : slpLine Wvals bwdProg 2 15 = true := by quickRfl
theorem bwd16 : slpLine Wvals bwdProg 2 16 = true := by quickRfl
theorem bwd17 : slpLine Wvals bwdProg 2 17 = true := by quickRfl
theorem bwd18 : slpLine Wvals bwdProg 2 18 = true := by quickRfl
theorem bwd19 : slpLine Wvals bwdProg 2 19 = true := by quickRfl
theorem bwd20 : slpLine Wvals bwdProg 2 20 = true := by quickRfl
theorem bwd21 : slpLine Wvals bwdProg 2 21 = true := by quickRfl
theorem bwd22 : slpLine Wvals bwdProg 2 22 = true := by quickRfl
theorem bwd23 : slpLine Wvals bwdProg 2 23 = true := by quickRfl
theorem bwd24 : slpLine Wvals bwdProg 2 24 = true := by quickRfl
theorem bwd25 : slpLine Wvals bwdProg 2 25 = true := by quickRfl
theorem bwd26 : slpLine Wvals bwdProg 2 26 = true := by quickRfl
theorem bwd27 : slpLine Wvals bwdProg 2 27 = true := by quickRfl
theorem bwd28 : slpLine Wvals bwdProg 2 28 = true := by quickRfl
theorem bwd29 : slpLine Wvals bwdProg 2 29 = true := by quickRfl
theorem bwd30 : slpLine Wvals bwdProg 2 30 = true := by quickRfl
theorem bwd31 : slpLine Wvals bwdProg 2 31 = true := by quickRfl
theorem bwd32 : slpLine Wvals bwdProg 2 32 = true := by quickRfl
theorem bwd33 : slpLine Wvals bwdProg 2 33 = true := by quickRfl
theorem bwd34 : slpLine Wvals bwdProg 2 34 = true := by quickRfl
theorem bwd35 : slpLine Wvals bwdProg 2 35 = true := by quickRfl
theorem bwd36 : slpLine Wvals bwdProg 2 36 = true := by quickRfl
theorem bwd37 : slpLine Wvals bwdProg 2 37 = true := by quickRfl
theorem bwd38 : slpLine Wvals bwdProg 2 38 = true := by quickRfl
theorem bwd39 : slpLine Wvals bwdProg 2 39 = true := by quickRfl
theorem bwd40 : slpLine Wvals bwdProg 2 40 = true := by quickRfl
theorem bwd41 : slpLine Wvals bwdProg 2 41 = true := by quickRfl
theorem bwd42 : slpLine Wvals bwdProg 2 42 = true := by quickRfl
theorem bwd43 : slpLine Wvals bwdProg 2 43 = true := by quickRfl
theorem bwd44 : slpLine Wvals bwdProg 2 44 = true := by quickRfl
theorem bwd45 : slpLine Wvals bwdProg 2 45 = true := by quickRfl
theorem bwd46 : slpLine Wvals bwdProg 2 46 = true := by quickRfl
theorem bwd47 : slpLine Wvals bwdProg 2 47 = true := by quickRfl
theorem bwd48 : slpLine Wvals bwdProg 2 48 = true := by quickRfl
theorem bwd49 : slpLine Wvals bwdProg 2 49 = true := by quickRfl
theorem bwd50 : slpLine Wvals bwdProg 2 50 = true := by quickRfl
theorem bwd51 : slpLine Wvals bwdProg 2 51 = true := by quickRfl
theorem bwd52 : slpLine Wvals bwdProg 2 52 = true := by quickRfl
theorem bwd53 : slpLine Wvals bwdProg 2 53 = true := by quickRfl
theorem bwd54 : slpLine Wvals bwdProg 2 54 = true := by quickRfl
theorem bwd55 : slpLine Wvals bwdProg 2 55 = true := by quickRfl
theorem bwd56 : slpLine Wvals bwdProg 2 56 = true := by quickRfl
theorem bwd57 : slpLine Wvals bwdProg 2 57 = true := by quickRfl
theorem bwd58 : slpLine Wvals bwdProg 2 58 = true := by quickRfl
theorem bwd59 : slpLine Wvals bwdProg 2 59 = true := by quickRfl
theorem bwd60 : slpLine Wvals bwdProg 2 60 = true := by quickRfl
theorem bwd61 : slpLine Wvals bwdProg 2 61 = true := by quickRfl
theorem bwd62 : slpLine Wvals bwdProg 2 62 = true := by quickRfl
theorem genA : Nat.beq (nthV Wvals 0) (nthV Fvals idxA) = true := by quickRfl
theorem genB : Nat.beq (nthV Wvals 1) (nthV Fvals idxB) = true := by quickRfl
theorem tgts : tgtOK Fvals Wvals letterIdx = true := by quickRfl
theorem codes : codesOK bracketCodes = true := by quickRfl
theorem iA : Nat.blt idxA (lenN Fvals) = true := by quickRfl
theorem iB : Nat.blt idxB (lenN Fvals) = true := by quickRfl
theorem lenF : Nat.beq (lenN Fvals) (12 + lenLL fwdProg) = true := by quickRfl
theorem lenW : Nat.beq (lenN Wvals) (2 + lenLL bwdProg) = true := by quickRfl
theorem nF : Nat.beq (lenLL fwdProg) 3 = true := by quickRfl
theorem nW : Nat.beq (lenLL bwdProg) 63 = true := by quickRfl
theorem ordA : ordB (nthV Fvals idxA) 2 = true := by quickRfl
theorem ordB3 : ordB (nthV Fvals idxB) 3 = true := by quickRfl
theorem ordAB : ordB (mulB (nthV Fvals idxA) (nthV Fvals idxB)) 19 = true := by quickRfl
theorem ordW : ordB (wordB (nthV Fvals idxA) (nthV Fvals idxB)
    [(0, true), (1, true), (0, true), (1, true), (1, true)]) 5 = true := by quickRfl
theorem lets : ∀ j < 12, Nat.beq (letterB bracketCodes formBits j) (nthV Fvals j) = true := by
  intro j hj
  interval_cases j
  exacts [let0, let1, let2, let3, let4, let5, let6, let7, let8, let9, let10, let11]
theorem fwds : ∀ t < lenLL fwdProg, slpLine Fvals fwdProg 12 t = true := by
  intro t ht
  rw [Nat.eq_of_beq_eq_true nF] at ht
  interval_cases t
  exacts [fwd0, fwd1, fwd2]
theorem bwds : ∀ t < lenLL bwdProg, slpLine Wvals bwdProg 2 t = true := by
  intro t ht
  rw [Nat.eq_of_beq_eq_true nW] at ht
  interval_cases t
  exacts [bwd0, bwd1, bwd2, bwd3, bwd4, bwd5, bwd6, bwd7, bwd8, bwd9, bwd10, bwd11, bwd12, bwd13, bwd14, bwd15, bwd16, bwd17, bwd18, bwd19, bwd20, bwd21, bwd22, bwd23, bwd24, bwd25, bwd26, bwd27, bwd28, bwd29, bwd30, bwd31, bwd32, bwd33, bwd34, bwd35, bwd36, bwd37, bwd38, bwd39, bwd40, bwd41, bwd42, bwd43, bwd44, bwd45, bwd46, bwd47, bwd48, bwd49, bwd50, bwd51, bwd52, bwd53, bwd54, bwd55, bwd56, bwd57, bwd58, bwd59, bwd60, bwd61, bwd62]

end CFSG.KD.Misc.E6Std

end
