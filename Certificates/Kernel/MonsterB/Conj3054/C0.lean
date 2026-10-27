module

public import Certificates.Kernel.MonsterB.Conj3054Data
public import CFSG.Certificates.Kernel.SortTreeSlice
import CFSG.Certificates.Kernel.Common.Harness
public import Std.Data.HashMap

public section

namespace CertificateChecks.Conj3054

open CFSG.KC.SortTree CFSG.KLie.CT

set_option maxRecDepth 100000

theorem c0_0 : closeSl actC 24 recC edgeC 56925 484 64 0 16 = true := by quickRfl
theorem c0_1 : closeSl actC 24 recC edgeC 56925 484 64 16 16 = true := by quickRfl
theorem c0_2 : closeSl actC 24 recC edgeC 56925 484 64 32 16 = true := by quickRfl
theorem c0_3 : closeSl actC 24 recC edgeC 56925 484 64 48 16 = true := by quickRfl
theorem c0_4 : closeSl actC 24 recC edgeC 56925 484 64 64 16 = true := by quickRfl
theorem c0_5 : closeSl actC 24 recC edgeC 56925 484 64 80 16 = true := by quickRfl
theorem c0_6 : closeSl actC 24 recC edgeC 56925 484 64 96 16 = true := by quickRfl

end CertificateChecks.Conj3054

end
