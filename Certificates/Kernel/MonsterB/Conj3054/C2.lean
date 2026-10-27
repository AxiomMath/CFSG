module

public import Certificates.Kernel.MonsterB.Conj3054Data
public import CFSG.Certificates.Kernel.SortTreeSlice
import CFSG.Certificates.Kernel.Common.Harness
public import Std.Data.HashMap

public section

namespace CertificateChecks.Conj3054

open CFSG.KC.SortTree CFSG.KLie.CT

set_option maxRecDepth 100000

theorem c2_0 : closeSl actC 24 recC edgeC 56925 484 64 224 16 = true := by quickRfl
theorem c2_1 : closeSl actC 24 recC edgeC 56925 484 64 240 16 = true := by quickRfl
theorem c2_2 : closeSl actC 24 recC edgeC 56925 484 64 256 16 = true := by quickRfl
theorem c2_3 : closeSl actC 24 recC edgeC 56925 484 64 272 16 = true := by quickRfl
theorem c2_4 : closeSl actC 24 recC edgeC 56925 484 64 288 16 = true := by quickRfl
theorem c2_5 : closeSl actC 24 recC edgeC 56925 484 64 304 16 = true := by quickRfl
theorem c2_6 : closeSl actC 24 recC edgeC 56925 484 64 320 16 = true := by quickRfl

end CertificateChecks.Conj3054

end
