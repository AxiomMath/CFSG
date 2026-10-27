module

public import Certificates.Kernel.MonsterExist.RigidB
public import CFSG.Monster.Existence.Census.TrialityWitnessesInputs

public section

namespace CertificateChecks.MonsterExist.Neg

open CertificateChecks.MonsterExist.RigidB CFSG.Monster.AxisCount CFSG.Monster.Existence.Census

theorem triality_target :
    (!checkB (Native.Gen.tauPow 1 ++ [Native.Gen.sign 3, Native.Gen.perm idArr] ++ Native.Gen.tauPow 2)
      [Native.Gen.rho (false, 3, 0)]) = true := by
  decide +kernel

theorem odd_key : findOdd (keyOdd 600).1 (keyOdd 600).2 = some 600 ∧
    findOdd (keyOdd 600).1 ((keyOdd 600).2 ^^^ 1) = none := by
  decide +kernel

end CertificateChecks.MonsterExist.Neg

end
