module

public import CFSG.LieType.Multipliers.U62BridgeInputs
public import CFSG.Certificates.Kernel.Misc.Coset.T46WordsSound
public import Certificates.Kernel.Misc.T46
public import Certificates.Kernel.Misc.Coset.C10015B
public import Certificates.Kernel.Misc.Coset.XT46W.All
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.LieType.Multipliers.U62Data
import CFSG.LieType.Multipliers.CoverWords
public import CFSG.Assembly.Subnormal
public import CFSG.Certificates.CosetTableCompactColumns
public import CFSG.Fischer.T46Simple
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CertificateChecks.KernelMiscCoset.C10015

open CFSG.KC.MiscCoset CFSG.LieType.Multipliers CFSG.LieType.Multipliers.U62 CFSG.F4.Native

set_option maxRecDepth 100000

theorem bridge_eq : bridgeCheck = T46W.wordsG uPts (relWords.map expand) (expand xWord)
    [30, 33, 16, 12, 9, 39, 39] (expand yWord) [41, 46, 21, 23, 36] := by
  rw [bridgeCheck, T46W.wordsG, List.all_map]
  rfl

theorem hR : relWords.map expand = CFSG.KAct.XT46W.R := by decide +kernel
theorem hX : expand xWord = CFSG.KAct.XT46W.XW := by decide +kernel
theorem hY : expand yWord = CFSG.KAct.XT46W.YW := by decide +kernel

theorem letters : T46W.lettersK CFSG.KAct.XT46W.R CFSG.KAct.XT46W.XW [30, 33, 16, 12, 9, 39, 39]
    CFSG.KAct.XT46W.YW [41, 46, 21, 23, 36] = true := by quickRfl

theorem bridge : bridgeCheck = true := by
  rw [bridge_eq, hR, hX, hY]
  exact T46W.pointK_sound CFSG.KD.Misc.Unitary.hU CFSG.KD.Misc.T46.pts CFSG.KD.Misc.T46.genAll
    letters fun x hx => Act.allR_spec CFSG.KAct.XT46W.all x (Nat.zero_le x) (by omega)

end CertificateChecks.KernelMiscCoset.C10015

end
