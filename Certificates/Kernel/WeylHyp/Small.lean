module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsWeyl

public section

namespace CertificateChecks.KernelWeylHyp

open CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.Native CFSG.Blueprint.Chevalley
  Timmesfeld.Co1Leaf

theorem hypF4 : hypOK .F4 = true := by decide +kernel

theorem std7 : famOK0 (gramL .E7) (rootsN .E7) (simpleL .E7)
    ((simpleL .E7).map fun e => formB (gramL .E7) e e) (stdBasis 7) = true := by decide +kernel

theorem std8 : famOK0 (gramL .E8) (rootsN .E8) (simpleL .E8)
    ((simpleL .E8).map fun e => formB (gramL .E8) e e) (stdBasis 8) = true := by decide +kernel

theorem kerF4 : kerNonemptyOK .F4 = true := by decide +kernel

theorem kerE7 : kerNonemptyOK .E7 = true := by decide +kernel

theorem kerE8 : kerNonemptyOK .E8 = true := by decide +kernel

theorem len7 : (normVecs 3 7).length ≤ 40 * 30 := by decide +kernel

theorem len8 : (normVecs 3 8).length ≤ 40 * 90 := by decide +kernel

end CertificateChecks.KernelWeylHyp

end
