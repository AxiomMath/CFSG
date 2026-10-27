module

public import Certificates.Data.Kernel.Hall82K.PermK

set_option maxRecDepth 100000

public section

namespace CFSG.KC.Hall82K

theorem ch840001pk :
    permK 4439643498 = true ∧ permK 34633937090 = true ∧ permK 52077576321 = true ∧
      permK 61871938592 = true := by
  decide +kernel

end CFSG.KC.Hall82K
