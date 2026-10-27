module

public import Certificates.Data.Kernel.G2Three.Sec1T3D
public import Certificates.Kernel.G2Three.Sec1T3Data
public import Certificates.Kernel.G2Three.Sec1T3RG
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.G2Three.Sec1T3

theorem s3d_f15a : f15aK PT PC IV SQ LMP 408 1 2 3 4 5 6 372 405 17 46 41 62 5 = true := by
  quickRfl

theorem s3d_f15b : f15bK PT PC IV SQ LMP RG 408 1 2 3 4 5 6 214 368 5 = true := by quickRfl

theorem s3d_f15c : f15cK PT PC IV SQ LMP RG 408 1 2 3 4 5 6 5 = true := by quickRfl

end CFSG.KD.G2Three.Sec1T3

end
