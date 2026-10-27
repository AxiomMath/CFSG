module

public import Certificates.Kernel.MonsterB.Conj3054Data
public import CFSG.Certificates.Kernel.SortTreeSlice
import CFSG.Certificates.Kernel.Common.Harness
public import Std.Data.HashMap

public section

namespace CertificateChecks.Conj3054

open CFSG.KC.SortTree CFSG.KLie.CT

set_option maxRecDepth 100000

theorem c4_0 : closeSl actC 24 recC edgeC 56925 484 64 448 16 = true := by quickRfl
theorem c4_1 : closeSl actC 24 recC edgeC 56925 484 64 464 16 = true := by quickRfl
theorem c4_2 : closeSl actC 24 recC edgeC 56925 484 64 480 16 = true := by quickRfl
theorem c4_3 : closeSl actC 24 recC edgeC 56925 484 64 496 16 = true := by quickRfl
theorem c4_4 : closeSl actC 24 recC edgeC 56925 484 64 512 16 = true := by quickRfl
theorem c4_5 : closeSl actC 24 recC edgeC 56925 484 64 528 16 = true := by quickRfl
theorem c4_6 : closeSl actC 24 recC edgeC 56925 484 64 544 16 = true := by quickRfl

end CertificateChecks.Conj3054

end
