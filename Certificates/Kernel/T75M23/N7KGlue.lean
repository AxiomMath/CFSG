
module

public import Certificates.Kernel.T75M23.N7KChecks
public import Certificates.Kernel.CosPresTab.M23Glue
public import CFSG.Certificates.Kernel.T75M23.N7KSound

public section

namespace CFSG.KC.N7K

open CFSG.KC.Enum CFSG.KS CFSG.KS.PK CFSG.KC.TabWord CFSG.KC.TabWord.M23 CFSG.CGT.T75M23
  CFSG.Sporadic.Th CFSG.Blueprint

theorem letterRd_NL : LetterRd NL := fun z x hx => n7L_get z x hx

theorem n7_surj' (g : N7) :
    ∃ a < 2520, ∃ k < 16, g = n7 (a7W a ++ tw7 k) :=
  n7K_surj letterRd_NL n7InvCheck_eq_true n7RelCheck_eq_true n7k_ok g

end CFSG.KC.N7K

end
