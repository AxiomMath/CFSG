module

public import Certificates.Data.Kernel.Hall82K.MR
public import Certificates.Kernel.Hall82K.RmData

public section

namespace CFSG.KD.Hall82L

open CFSG.KC.Ord CFSG.KC.LQT CFSG.KC.Hall82K CFSG.KD.Hall82R

theorem ch840001le32 : P.allN 256 (le32K RMP) = true := by decide +kernel

end CFSG.KD.Hall82L
