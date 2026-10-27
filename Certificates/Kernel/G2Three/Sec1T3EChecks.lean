module

public import Certificates.Data.Kernel.G2Three.Sec1T3E
public import Certificates.Kernel.G2Three.Sec1T3Data
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.G2Three.Sec1T3

theorem s3e_sort : latSortK LMP OR 408 = true := by quickRfl

end CFSG.KD.G2Three.Sec1T3

end
