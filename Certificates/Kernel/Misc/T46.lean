module

public import CFSG.Certificates.Kernel.Misc.T46Sound
public import Certificates.Kernel.Misc.T46Data
public import Certificates.Kernel.Misc.Unitary
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Misc.KernelRfl
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Misc.O73Sound
public import Mathlib

public section

set_option maxRecDepth 200000

namespace CFSG.KD.Misc.T46

open CFSG.KC.Misc.T46 CFSG.F4.Native CFSG.Sporadic.Fi22.Native

theorem bWS : CFSG.KC.Misc.T46.wordStrings = WC.map CFSG.KC.Misc.O73.strOf := by kernelRfl
theorem bTW : t46TvWords = (TW.map (List.map Int.ofNat)).toArray := by decide +kernel
theorem pts : ptsK CFSG.KD.Misc.Unitary.UL UP = true := by quickRfl
theorem letters : lettersK GP WC LP = true := by quickRfl
theorem trees : treesK LP [0, 1, 3, 9, 45] 11 O1 Pa1 La1 O2 Pa2 La2 = true := by quickRfl
theorem xy : xyK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] = true := by quickRfl
theorem gen0 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 0 1 = true := by quickRfl
theorem gen1 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 1 1 = true := by quickRfl
theorem gen2 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 2 1 = true := by quickRfl
theorem gen3 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 3 1 = true := by quickRfl
theorem gen4 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 4 1 = true := by quickRfl
theorem gen5 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 5 1 = true := by quickRfl
theorem gen6 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 6 1 = true := by quickRfl
theorem gen7 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 7 1 = true := by quickRfl
theorem gen8 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 8 1 = true := by quickRfl
theorem gen9 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 9 1 = true := by quickRfl
theorem gen10 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 10 1 = true := by quickRfl
theorem gen11 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 11 1 = true := by quickRfl
theorem gen12 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 12 1 = true := by quickRfl
theorem gen13 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 13 1 = true := by quickRfl
theorem gen14 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 14 1 = true := by quickRfl
theorem gen15 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 15 1 = true := by quickRfl
theorem gen16 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 16 1 = true := by quickRfl
theorem gen17 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 17 1 = true := by quickRfl
theorem gen18 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 18 1 = true := by quickRfl
theorem gen19 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 19 1 = true := by quickRfl
theorem gen20 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 20 1 = true := by quickRfl
theorem gen21 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 21 1 = true := by quickRfl
theorem gen22 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 22 1 = true := by quickRfl
theorem gen23 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 23 1 = true := by quickRfl
theorem gen24 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 24 1 = true := by quickRfl
theorem gen25 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 25 1 = true := by quickRfl
theorem gen26 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 26 1 = true := by quickRfl
theorem gen27 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 27 1 = true := by quickRfl
theorem gen28 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 28 1 = true := by quickRfl
theorem gen29 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 29 1 = true := by quickRfl
theorem gen30 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 30 1 = true := by quickRfl
theorem gen31 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 31 1 = true := by quickRfl
theorem gen32 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 32 1 = true := by quickRfl
theorem gen33 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 33 1 = true := by quickRfl
theorem gen34 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 34 1 = true := by quickRfl
theorem gen35 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 35 1 = true := by quickRfl
theorem gen36 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 36 1 = true := by quickRfl
theorem gen37 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 37 1 = true := by quickRfl
theorem gen38 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 38 1 = true := by quickRfl
theorem gen39 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 39 1 = true := by quickRfl
theorem gen40 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 40 1 = true := by quickRfl
theorem gen41 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 41 1 = true := by quickRfl
theorem gen42 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 42 1 = true := by quickRfl
theorem gen43 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 43 1 = true := by quickRfl
theorem gen44 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 44 1 = true := by quickRfl
theorem gen45 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 45 1 = true := by quickRfl
theorem tv0 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 0 1 = true := by quickRfl
theorem tv1 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 1 1 = true := by quickRfl
theorem tv2 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 2 1 = true := by quickRfl
theorem tv3 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 3 1 = true := by quickRfl
theorem tv4 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 4 1 = true := by quickRfl
theorem tv5 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 5 1 = true := by quickRfl
theorem tv6 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 6 1 = true := by quickRfl
theorem tv7 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 7 1 = true := by quickRfl
theorem tv8 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 8 1 = true := by quickRfl
theorem tv9 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 9 1 = true := by quickRfl
theorem tv10 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 10 1 = true := by quickRfl
theorem tv11 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 11 1 = true := by quickRfl
theorem tv12 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 12 1 = true := by quickRfl
theorem tv13 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 13 1 = true := by quickRfl
theorem tv14 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 14 1 = true := by quickRfl
theorem tv15 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 15 1 = true := by quickRfl
theorem tv16 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 16 1 = true := by quickRfl
theorem tv17 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 17 1 = true := by quickRfl
theorem tv18 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 18 1 = true := by quickRfl
theorem tv19 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 19 1 = true := by quickRfl
theorem tv20 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 20 1 = true := by quickRfl
theorem tv21 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 21 1 = true := by quickRfl
theorem tv22 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 22 1 = true := by quickRfl
theorem tv23 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 23 1 = true := by quickRfl
theorem tv24 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 24 1 = true := by quickRfl
theorem tv25 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 25 1 = true := by quickRfl
theorem tv26 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 26 1 = true := by quickRfl
theorem tv27 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 27 1 = true := by quickRfl
theorem tv28 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 28 1 = true := by quickRfl
theorem tv29 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 29 1 = true := by quickRfl
theorem tv30 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 30 1 = true := by quickRfl
theorem tv31 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 31 1 = true := by quickRfl
theorem tv32 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 32 1 = true := by quickRfl
theorem tv33 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 33 1 = true := by quickRfl
theorem tv34 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 34 1 = true := by quickRfl
theorem tv35 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 35 1 = true := by quickRfl
theorem tv36 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 36 1 = true := by quickRfl
theorem tv37 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 37 1 = true := by quickRfl
theorem tv38 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 38 1 = true := by quickRfl
theorem tv39 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 39 1 = true := by quickRfl
theorem tv40 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 40 1 = true := by quickRfl
theorem tv41 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 41 1 = true := by quickRfl
theorem tv42 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 42 1 = true := by quickRfl
theorem tv43 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 43 1 = true := by quickRfl
theorem tv44 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 44 1 = true := by quickRfl
theorem tv45 : tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW 45 1 = true := by quickRfl
theorem genAll : ∀ k < 46, gensOK CFSG.KD.Misc.Unitary.UL UP GP k 1 = true := by
  intro k hk
  interval_cases k
  exacts [gen0, gen1, gen2, gen3, gen4, gen5, gen6, gen7, gen8, gen9, gen10, gen11, gen12, gen13, gen14, gen15, gen16, gen17, gen18, gen19, gen20, gen21, gen22, gen23, gen24, gen25, gen26, gen27, gen28, gen29, gen30, gen31, gen32, gen33, gen34, gen35, gen36, gen37, gen38, gen39, gen40, gen41, gen42, gen43, gen44, gen45]
theorem tvAll : ∀ k < 46, tvWordsK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] TW k 1 = true := by
  intro k hk
  interval_cases k
  exacts [tv0, tv1, tv2, tv3, tv4, tv5, tv6, tv7, tv8, tv9, tv10, tv11, tv12, tv13, tv14, tv15, tv16, tv17, tv18, tv19, tv20, tv21, tv22, tv23, tv24, tv25, tv26, tv27, tv28, tv29, tv30, tv31, tv32, tv33, tv34, tv35, tv36, tv37, tv38, tv39, tv40, tv41, tv42, tv43, tv44, tv45]

end CFSG.KD.Misc.T46

end
