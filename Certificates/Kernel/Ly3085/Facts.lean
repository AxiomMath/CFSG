
module


public import Certificates.Kernel.Ly3085.Simple

public section

namespace CertificateChecks.KernelLy

open CFSG.Sporadic.Ly

theorem card_J_S [LySeed] :
    Nat.card J = 51765179004000000 := by
  rw [J_eq_JS]
  exact card_JS

theorem isSimpleGroup_J_S [LySeed] :
    IsSimpleGroup J := by
  rw [J_eq_JS]
  exact isSimpleGroup_JS'

theorem card_Ly_S [LySeed] :
    Nat.card CFSG.Blueprint.NativeSporadic.Ly = 51765179004000000 := by
  rw [Nat.card_congr lyEquivJ.toEquiv, card_J_S]

theorem isSimpleGroup_Ly_S [LySeed] :
    IsSimpleGroup CFSG.Blueprint.NativeSporadic.Ly :=
  @MulEquiv.isSimpleGroup _ _ _ _ isSimpleGroup_J_S lyEquivJ

end CertificateChecks.KernelLy

end
