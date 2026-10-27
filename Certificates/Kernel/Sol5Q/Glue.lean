module

public import CFSG.Certificates.Kernel.Sol5Q.Sound
import Certificates.Kernel.Sol5Q.Check8
import Certificates.Kernel.Sol5Q.Check9
import Certificates.Kernel.Sol5Q.Check10
import Certificates.Kernel.Sol5Q.Check11

public section

namespace CFSG.KD.Sol5Q

open CFSG.KC.Sol5Q CFSG.OddStandard.Solomon75

theorem fcAll8 : FCAll 8 :=
  fcAll_of_checks (n := 8) (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) rfl (by decide +kernel) Sol5Q8.ct Sol5Q8.h Sol5Q8.gens Sol5Q8.fcb
    Sol5Q8.fcr Sol5Q8.fco2

theorem fcAll9 : FCAll 9 :=
  fcAll_of_checks (n := 9) (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) rfl (by decide +kernel) Sol5Q9.ct Sol5Q9.h Sol5Q9.gens Sol5Q9.fcb
    Sol5Q9.fcr Sol5Q9.fco2

theorem fcAll10 : FCAll 10 :=
  fcAll_of_checks (n := 10) (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) rfl (by decide +kernel) Sol5Q10.ct Sol5Q10.h Sol5Q10.gens Sol5Q10.fcb
    Sol5Q10.fcr Sol5Q10.fco2

theorem fcAll11 : FCAll 11 :=
  fcAll_of_checks (n := 11) (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) rfl (by decide +kernel) Sol5Q11.ct Sol5Q11.h Sol5Q11.gens Sol5Q11.fcb
    Sol5Q11.fcr Sol5Q11.fco2

end CFSG.KD.Sol5Q

end
