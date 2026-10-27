module

public import Certificates.Kernel.He4049.Tab
public import Certificates.Kernel.HeOrb.Final
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHeInputs

public section

namespace CFSG.KD.He4049

open CFSG.KS.HeVO

theorem heTa_eq : CFSG.QuasithinUnique.K1.SporadicPerm.heTa = TA := by
  unfold CFSG.QuasithinUnique.K1.SporadicPerm.heTa TA
  rw [CFSG.KD.HeOrb.orbitData_eq]
  refine congrArg List.toArray (List.map_congr_left fun x hx => ?_)
  have hx' := List.mem_range.1 hx
  rw [CFSG.KD.HeOrb.alpha_ap hx', tabK_spec Tab.ta_ok x hx']

theorem heTb_eq : CFSG.QuasithinUnique.K1.SporadicPerm.heTb = TB := by
  unfold CFSG.QuasithinUnique.K1.SporadicPerm.heTb TB
  rw [CFSG.KD.HeOrb.orbitData_eq]
  refine congrArg List.toArray (List.map_congr_left fun x hx => ?_)
  have hx' := List.mem_range.1 hx
  rw [CFSG.KD.HeOrb.beta_ap hx', tabK_spec Tab.tb_ok x hx']

end CFSG.KD.He4049

end
