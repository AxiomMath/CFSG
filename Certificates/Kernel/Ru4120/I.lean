module

public import Certificates.Kernel.Ru4120.Fam
import Certificates.Kernel.SporSch.Ru.RowsGen
import CFSG.Certificates.Kernel.Common.Harness

public section

#kss_each CFSG.KD.Ru4120.I CFSG.KD.Ru4120.famI 11

namespace CFSG.KD.Ru4120

theorem famR_ok : famR = true := by quickRfl

end CFSG.KD.Ru4120

end
