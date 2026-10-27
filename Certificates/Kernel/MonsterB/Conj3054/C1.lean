module

public import Certificates.Kernel.MonsterB.Conj3054Data
public import CFSG.Certificates.Kernel.SortTreeSlice
import CFSG.Certificates.Kernel.Common.Harness
public import Std.Data.HashMap

public section

namespace CertificateChecks.Conj3054

open CFSG.KC.SortTree CFSG.KLie.CT

set_option maxRecDepth 100000

theorem c1_0 : closeSl actC 24 recC edgeC 56925 484 64 112 16 = true := by quickRfl
theorem c1_1 : closeSl actC 24 recC edgeC 56925 484 64 128 16 = true := by quickRfl
theorem c1_2 : closeSl actC 24 recC edgeC 56925 484 64 144 16 = true := by quickRfl
theorem c1_3 : closeSl actC 24 recC edgeC 56925 484 64 160 16 = true := by quickRfl
theorem c1_4 : closeSl actC 24 recC edgeC 56925 484 64 176 16 = true := by quickRfl
theorem c1_5 : closeSl actC 24 recC edgeC 56925 484 64 192 16 = true := by quickRfl
theorem c1_6 : closeSl actC 24 recC edgeC 56925 484 64 208 16 = true := by quickRfl

end CertificateChecks.Conj3054

end
