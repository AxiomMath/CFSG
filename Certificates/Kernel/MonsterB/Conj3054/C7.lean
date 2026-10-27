module

public import Certificates.Kernel.MonsterB.Conj3054Data
public import CFSG.Certificates.Kernel.SortTreeSlice
import CFSG.Certificates.Kernel.Common.Harness
public import Std.Data.HashMap

public section

namespace CertificateChecks.Conj3054

open CFSG.KC.SortTree CFSG.KLie.CT

set_option maxRecDepth 100000

theorem c7_0 : closeSl actC 24 recC edgeC 56925 484 64 784 16 = true := by quickRfl
theorem c7_1 : closeSl actC 24 recC edgeC 56925 484 64 800 16 = true := by quickRfl
theorem c7_2 : closeSl actC 24 recC edgeC 56925 484 64 816 16 = true := by quickRfl
theorem c7_3 : closeSl actC 24 recC edgeC 56925 484 64 832 16 = true := by quickRfl
theorem c7_4 : closeSl actC 24 recC edgeC 56925 484 64 848 16 = true := by quickRfl
theorem c7_5 : closeSl actC 24 recC edgeC 56925 484 64 864 16 = true := by quickRfl
theorem c7_6 : closeSl actC 24 recC edgeC 56925 484 64 880 16 = true := by quickRfl

end CertificateChecks.Conj3054

end
