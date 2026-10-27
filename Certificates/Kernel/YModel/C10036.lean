module

public import CFSG.Monster.GMS.R433Cover.Y432IdentitiesInputs
public import CFSG.Monster.GMS.R433Cover.Y432Transport
public import CFSG.YGroups.Exact.Y432Inputs
public import CFSG.YGroups.Defs
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Kernel.YModel.Y432
import CFSG.Certificates.Kernel.Common.Harness
public import Mathlib

public section

namespace CertificateChecks.KernelYModel

open CFSG.KC.YModel CFSG.YGroups CFSG.Monster.GMS.R433Cover CFSG.Monster.B.Co2.Native

set_option maxRecDepth 100000

theorem y432_I1 :
    eqA 31673
      (ModelNative.evalW 31673 y432Arrays
      (List.replicate 3 ((List.replicate 5 (spiderWord 4 3)).flatten ++ [0])).flatten)
      (idA 31673) = true := by
  have e : idA 31673 = ModelNative.evalW 31673 y432Arrays [] := rfl
  rw [e, y432_arrays_eq, eqA_of_weqK _ _ y432_let]
  quickRfl

theorem y432_I2 :
    eqA 31673 (ModelNative.evalW 31673 y432Arrays (yConj.reverse ++ [0, 4, 6] ++ yConj))
      (ModelNative.evalW 31673 y432Arrays ([2, 5, 7, 9] ++ f213Word)) = true := by
  rw [y432_arrays_eq, eqA_of_weqK _ _ y432_let]
  quickRfl

theorem c10036_neg :
    (!weqK 15 10 CFSG.KD.YMY432.Nf [0] [] &&
      !weqK 15 10 CFSG.KD.YMY432.Nf (yConj.reverse ++ [0, 4, 6] ++ yConj.dropLast)
        ([2, 5, 7, 9] ++ f213Word)) = true := by
  quickRfl

open CFSG.YGroups CFSG.Monster.GMS.R433Cover CFSG.Monster.B.Co2.Native in
theorem c10036 :
    (eqA 31673
      (ModelNative.evalW 31673 y432Arrays
      (List.replicate 3 ((List.replicate 5 (spiderWord 4 3)).flatten ++ [0])).flatten)
      (idA 31673) = true)
    ∧ (eqA 31673 (ModelNative.evalW 31673 y432Arrays (yConj.reverse ++ [0, 4, 6] ++ yConj))
      (ModelNative.evalW 31673 y432Arrays ([2, 5, 7, 9] ++ f213Word)) = true) := ⟨y432_I1, y432_I2⟩

end CertificateChecks.KernelYModel

end
