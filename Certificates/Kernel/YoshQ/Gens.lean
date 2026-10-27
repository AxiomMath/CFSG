module

public import Certificates.Kernel.YoshQ.DataN
public import Certificates.Kernel.YoshQ.DataW
public import Certificates.Kernel.YoshQ.DataM
public import Certificates.Data.Kernel.YoshQ.Param
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic

public section

namespace CertificateChecks.KernelYoshQ

open CFSG.KC.YoshQ CFSG.EvenSporadicStandard.M12Std.Yosh CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

set_option maxHeartbeats 0

theorem g_y : gensOK 14 5 yGens Y.GS = true := by decide +kernel
theorem g_k : gensOK 14 5 kTabs K.GS = true := by decide +kernel
theorem g_r : gensOK 14 5 rTabs R.GS = true := by decide +kernel
theorem g_eg : gensOK 16 5 eGens EG.GS = true ∧ wordsOK 16 6 eGens relE = true := by
  decide +kernel
theorem g_q00 : gensOK 24 5 (qGens 0 0) Q00.GS = true ∧ wordsOK 24 8 (qGens 0 0) (rel4 0 0) = true :=
  by decide +kernel
theorem g_q01 : gensOK 24 5 (qGens 0 1) Q01.GS = true ∧ wordsOK 24 8 (qGens 0 1) (rel4 0 1) = true :=
  by decide +kernel
theorem g_q10 : gensOK 24 5 (qGens 1 0) Q10.GS = true ∧ wordsOK 24 8 (qGens 1 0) (rel4 1 0) = true :=
  by decide +kernel
theorem g_q11 : gensOK 24 5 (qGens 1 1) Q11.GS = true ∧ wordsOK 24 8 (qGens 1 1) (rel4 1 1) = true :=
  by decide +kernel
theorem g_n00 : gensOK 16 5 (nGens 0 0) N00.GS = true ∧
    wordsOK 16 9 (nGens 0 0) (relN 0 0 0) = true := by decide +kernel
theorem g_n01 : gensOK 16 5 (nGens 0 1) N01.GS = true ∧
    wordsOK 16 9 (nGens 0 1) (relN 0 0 1) = true := by decide +kernel
theorem g_n10 : gensOK 16 5 (nGens 1 0) N10.GS = true ∧
    wordsOK 16 9 (nGens 1 0) (relN 1 1 0) = true := by decide +kernel
theorem g_n11 : gensOK 16 5 (nGens 1 1) N11.GS = true ∧
    wordsOK 16 9 (nGens 1 1) (relN 1 1 1) = true := by decide +kernel
theorem g_ne : gensOK 16 5 (nEGens 0 0) NE00.GS = true ∧ gensOK 16 5 (nEGens 0 1) NE01.GS = true ∧
    gensOK 16 5 (nEGens 1 0) NE10.GS = true ∧ gensOK 16 5 (nEGens 1 1) NE11.GS = true := by
  decide +kernel
theorem g_e : gensOK 16 5 (wgens 0 0 eWords) E00.GS = true ∧
    gensOK 16 5 (wgens 0 1 eWords) E01.GS = true ∧ gensOK 16 5 (wgens 1 0 eWords) E10.GS = true ∧
    gensOK 16 5 (wgens 1 1 eWords) E11.GS = true := by
  decide +kernel
theorem g_s : gensOK 16 5 (wgens 0 0 sWords) S00.GS = true ∧
    gensOK 16 5 (wgens 0 1 sWords) S01.GS = true ∧ gensOK 16 5 (wgens 1 0 sWords) S10.GS = true ∧
    gensOK 16 5 (wgens 1 1 sWords) S11.GS = true := by
  decide +kernel
theorem g_a : gensOK 16 5 (wgens 1 0 aWords) A10.GS = true ∧
    gensOK 16 5 (wgens 1 1 aWords) A11.GS = true := by
  decide +kernel
theorem g_gl : gensOK 28 5 (glueGens (wgens 1 0 sWords) (sylowHomData 0)) GL0.GS = true ∧
    gensOK 28 5 (glueGens (wgens 1 1 sWords) (sylowHomData 1)) GL1.GS = true := by
  decide +kernel
theorem g_ge : (GE10.GS.map (tabN 16 5)).toArray.all
      (fun x => CFSG.Sporadic.SmallOddCore.permOK 16 x) = true ∧
    (GE11.GS.map (tabN 16 5)).toArray.all (fun x => CFSG.Sporadic.SmallOddCore.permOK 16 x) = true :=
  by decide +kernel

end CertificateChecks.KernelYoshQ

end
