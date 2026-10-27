module

public import Certificates.Kernel.MonsterB.Conj3054Data
public import CFSG.Certificates.Kernel.SortTreeSlice
import CFSG.Certificates.Kernel.Common.Harness
public import Std.Data.HashMap

public section

namespace CertificateChecks.Conj3054

open CFSG.KC.SortTree CFSG.KLie.CT

set_option maxRecDepth 100000

theorem c5_0 : closeSl actC 24 recC edgeC 56925 484 64 560 16 = true := by quickRfl
theorem c5_1 : closeSl actC 24 recC edgeC 56925 484 64 576 16 = true := by quickRfl
theorem c5_2 : closeSl actC 24 recC edgeC 56925 484 64 592 16 = true := by quickRfl
theorem c5_3 : closeSl actC 24 recC edgeC 56925 484 64 608 16 = true := by quickRfl
theorem c5_4 : closeSl actC 24 recC edgeC 56925 484 64 624 16 = true := by quickRfl
theorem c5_5 : closeSl actC 24 recC edgeC 56925 484 64 640 16 = true := by quickRfl
theorem c5_6 : closeSl actC 24 recC edgeC 56925 484 64 656 16 = true := by quickRfl

end CertificateChecks.Conj3054

end
