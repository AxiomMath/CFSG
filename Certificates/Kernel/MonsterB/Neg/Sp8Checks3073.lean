module

public import Certificates.Data.Kernel.MonsterB.Sp8Span
public import Certificates.Data.CFSGNative.MonsterB.Sp8Check
public import CFSG.Monster.B.Rep4371.Model

public section

namespace CertificateChecks.Sp8Neg3073

open CFSG.KC.Rep4371Row CFSG.KC.Sp8Span CFSG.Monster.B

theorem span_sign : (!spanEqT (eYT 3 :: [4, 1].map eYT) ([4, 1].map eYT ++ [ePauliT 0 63 0, eYT 3]))
    = true := by
  decide +kernel

theorem labels_q : Model.conjYN 1 (Model.conjXiN (Model.conjYN 3 (false, 0, 4))) ≠
    Model.conjYN 3 (Model.conjPauliN (false, 60, 0) (Model.conjYN 1 (Model.conjXiN (false, 0, 4)))) := by
  decide +kernel

theorem key_sign : (!CFSG.Monster.B.Rep4371.Native.Sp8.xiKeyRow (true, 60, 60) false 0) = true := by
  decide +kernel

end CertificateChecks.Sp8Neg3073

end
