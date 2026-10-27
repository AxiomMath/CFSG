module

public import Certificates.Kernel.MonsterB.Conj3054Data
public import CFSG.Certificates.Kernel.SortTreeSlice
import CFSG.Certificates.Kernel.Common.Harness
public import Std.Data.HashMap

public section

namespace CertificateChecks.Conj3054

open CFSG.KC.SortTree CFSG.KLie.CT

set_option maxRecDepth 100000

theorem c3_0 : closeSl actC 24 recC edgeC 56925 484 64 336 16 = true := by quickRfl
theorem c3_1 : closeSl actC 24 recC edgeC 56925 484 64 352 16 = true := by quickRfl
theorem c3_2 : closeSl actC 24 recC edgeC 56925 484 64 368 16 = true := by quickRfl
theorem c3_3 : closeSl actC 24 recC edgeC 56925 484 64 384 16 = true := by quickRfl
theorem c3_4 : closeSl actC 24 recC edgeC 56925 484 64 400 16 = true := by quickRfl
theorem c3_5 : closeSl actC 24 recC edgeC 56925 484 64 416 16 = true := by quickRfl
theorem c3_6 : closeSl actC 24 recC edgeC 56925 484 64 432 16 = true := by quickRfl

end CertificateChecks.Conj3054

end
