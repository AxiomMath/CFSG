module

public import Certificates.Kernel.S1277.Mod
public import Certificates.Kernel.S1277.GmFacts
public import CFSG.Certificates.Kernel.S1277KModSound

public section

namespace CFSG.KP.S1277Mod

open CFSG.Quasithin.H13.S127.Mod Certificates.Data.S1277Struct CFSG.KC.S1277Gm CFSG.KC.S1277Mod
  CFSG.KS.S1277Gm CFSG.KS.S1277Mod CFSG.KD.S1277Gm CFSG.KD.S1277Mod CFSG.KP.S1277Gm

theorem stabL_gm6 : stabL gm6 5 = lg.map B6.ofP := by
  rw [gm6_eq]
  exact eq_of_eqB6 _ _ stabg_ok

theorem stabL_nm6 : stabL nm6 5 = ln.map B6.ofP := by
  rw [nm6_eq]
  exact eq_of_eqB6 _ _ stabn_ok

theorem lg_length : lg.length = 24 := by rfl

theorem ln_length : ln.length = 48 := by rfl

theorem modFacts_gm6 : ModFacts (stabL gm6 5) 24 apg cpg ipg oneg := by
  rw [stabL_gm6, ← lg_length]
  exact modFacts_of modg_ok

theorem modFacts_nm6 : ModFacts (stabL nm6 5) 48 apn cpn ipn onen := by
  rw [stabL_nm6, ← ln_length]
  exact modFacts_of modn_ok

end CFSG.KP.S1277Mod

end
