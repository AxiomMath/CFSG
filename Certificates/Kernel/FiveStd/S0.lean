module

public import Certificates.Data.Kernel.FiveStdKList
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.FiveStd

open CFSG.KC.FiveStdK

@[expose] def S0gK : List Nat := [409405, 409440, 409504, 412540]

@[expose] def S0c : List Nat :=
  [78876, 409405, 409440, 409504, 412540, 80877, 28629, 79877, 79003, 81126, 28502, 79751, 78795,
    80690, 28230, 79430, 79503, 80251, 25502, 418810, 418855, 419003, 415680, 471370, 471335,
    471751, 470055, 412610, 412580, 413003, 409495, 409627, 412570, 418840, 419254, 415740, 471280,
    471628, 470115, 412879, 409753, 418876, 415753, 471502, 470128, 412751, 412627, 418795, 415879,
    470735, 470705, 471128, 471315, 79254, 19128, 80379, 79127, 18879, 80127, 78855, 18835, 80110,
    22254, 19002, 19251, 22002, 18815, 21985, 22126, 25128, 80754, 25254, 79490, 80080, 25035,
    80710, 81003, 28251, 78810, 80745, 28215, 79629, 80503, 25376, 78840, 18780, 18870, 21955,
    22378, 79470, 80040, 25055, 80655, 28185, 79410, 80070, 21945, 21915, 25095, 25115, 28378,
    409460, 409876, 469465, 469420, 469752, 415720, 415660, 416001, 469435, 469501, 469879, 470876,
    416127, 470095, 470035, 470376, 469480, 469628, 470665, 470695, 471004, 470502, 470254, 470752,
    419127, 471379, 28170]

theorem s0_closure : closureK S0gK = S0c := by decide +kernel

theorem s0_right : (S0c.all fun x => S0gK.all fun g => S0c.contains (mulK x g)) = true := by
  decide +kernel

theorem s0_right_neg :
    (!(S0c.dropLast.all fun x => S0gK.all fun g => S0c.dropLast.contains (mulK x g))) = true := by
  decide +kernel

theorem s0_closure_neg : (closureK S0gK != S0c.set 5 80878) = true := by decide +kernel

end CertificateChecks.FiveStd

end
