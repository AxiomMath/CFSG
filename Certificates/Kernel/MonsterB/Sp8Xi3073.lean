module

public import Certificates.Data.CFSGNative.MonsterB.Sp8Check
public import CFSG.Monster.B.TwoA.Sp8.GenActionData

public section

namespace CertificateChecks.Sp8Xi3073

open CFSG.Monster.B CFSG.Monster.B.TwoA.Sp8

theorem pauli_check : ∀ k < 23,
    Model.conjYN 3 (pauliQs.getD k (false, 0, 0)) =
      Model.Pauli.mul (pauliQs.getD k (false, 0, 0)) (genDiff.getD k (false, 0, 0)) := by
  decide +kernel

theorem xi_labels : ∀ k < 24,
    Model.conjYN 1 (Model.conjXiN (Model.conjYN 3
      (if k < 12 then (false, 2 ^ k, 0) else (false, 0, 2 ^ (k - 12))))) =
    Model.conjYN 3 (Model.conjPauliN (false, 60, 60) (Model.conjYN 1 (Model.conjXiN
      (if k < 12 then (false, 2 ^ k, 0) else (false, 0, 2 ^ (k - 12)))))) := by
  decide +kernel

theorem xi_key : CFSG.Monster.B.Rep4371.Native.Sp8.xiKeyRow (false, 60, 60) false 0 = true := by
  decide +kernel

end CertificateChecks.Sp8Xi3073

end
