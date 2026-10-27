
module

public import Certificates.Kernel.T75JM.N0KChecks
public import Certificates.Kernel.CosPresTab.M22Glue
public import CFSG.Certificates.Kernel.T75JM.N0KSound

public section

namespace CFSG.KC.N0K

open CFSG.KC.Enum CFSG.KS CFSG.KS.PK CFSG.KC.TabWord CFSG.KC.TabWord.M22 CFSG.CGT.T75JM
  CFSG.Sporadic.Th CFSG.Blueprint

theorem letterRd_LP : LetterRd LP := fun z x hx => letter_get z x hx

theorem n0Inv_ok : n0InvCheck = true :=
  List.all_eq_true.2 fun k hk => (gen_get (k := k) (by simp at hk; omega)).2.1

theorem n0Rel_ok : n0RelCheck = true := n0RelCheck_of letterRd_LP (n0kOk_parts n0k_ok).1

end CFSG.KC.N0K

end
