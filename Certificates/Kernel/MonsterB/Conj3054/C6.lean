module

public import Certificates.Kernel.MonsterB.Conj3054Data
public import CFSG.Certificates.Kernel.SortTreeSlice
import CFSG.Certificates.Kernel.Common.Harness
public import Std.Data.HashMap

public section

namespace CertificateChecks.Conj3054

open CFSG.KC.SortTree CFSG.KLie.CT

set_option maxRecDepth 100000

theorem c6_0 : closeSl actC 24 recC edgeC 56925 484 64 672 16 = true := by quickRfl
theorem c6_1 : closeSl actC 24 recC edgeC 56925 484 64 688 16 = true := by quickRfl
theorem c6_2 : closeSl actC 24 recC edgeC 56925 484 64 704 16 = true := by quickRfl
theorem c6_3 : closeSl actC 24 recC edgeC 56925 484 64 720 16 = true := by quickRfl
theorem c6_4 : closeSl actC 24 recC edgeC 56925 484 64 736 16 = true := by quickRfl
theorem c6_5 : closeSl actC 24 recC edgeC 56925 484 64 752 16 = true := by quickRfl
theorem c6_6 : closeSl actC 24 recC edgeC 56925 484 64 768 16 = true := by quickRfl

end CertificateChecks.Conj3054

end
