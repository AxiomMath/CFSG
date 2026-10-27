module

public import Certificates.Kernel.Over77.Data
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Repo

public section

namespace CFSG.KD.Over77

open CFSG.KC.Over77 CFSG.KC.Enum

theorem c12630t0 : idK (T 0) = true := by decide +kernel

theorem c12630gens : (canon A && canon B && canon Z && canon Sig && S.length == 9 &&
    allN 9 (fun k => canon (nth S k))) = true := by decide +kernel

end CFSG.KD.Over77

end

#kc_repo #kc_each_rows CFSG.KD.Over77 c12630pw (fun p len W => CFSG.KD.Over77.pwR p len W)
  "Certificates/Kernel/Over77/data/pw.txt.gz" 1045 6243921055104446018 0 110

#kc_repo #kc_each_rows CFSG.KD.Over77 c12630sw (fun i len W => CFSG.KD.Over77.swR i len W)
  "Certificates/Kernel/Over77/data/sw.txt.gz" 1109 10199449385633197420 0 82
