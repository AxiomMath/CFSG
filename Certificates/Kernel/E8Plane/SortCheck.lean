module

public import Certificates.Data.Kernel.E8Plane.Sorted
public import Certificates.Kernel.E8Plane.Data

public section

namespace CFSG.KC.E8Plane

open CFSG.KC.E7Plane CFSG.KD.E8Plane

theorem sort_check : sortB (pk 32 RC) (pk 32 SC) (pk 8 SI) = true := by decide +kernel

theorem lett_check : lettB CJ = true := by decide +kernel

end CFSG.KC.E8Plane
