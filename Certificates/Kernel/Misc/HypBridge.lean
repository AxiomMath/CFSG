module

public import Certificates.Kernel.Misc.Hyp
public import Certificates.Kernel.Misc.HypS.S0
public import Certificates.Kernel.Misc.HypS.S1
public import Certificates.Kernel.Misc.HypS.S2
public import Certificates.Kernel.Misc.HypS.S3
public import Certificates.Kernel.Misc.HypS.S4
public import Certificates.Kernel.Misc.HypS.S5
public import Certificates.Kernel.Misc.HypS.S6
public import Certificates.Kernel.Misc.HypS.S7
public import CFSG.Certificates.Kernel.Misc.HypSound
public import Certificates.Kernel.Misc.Lines
public import Certificates.Kernel.Misc.T46
public import Certificates.Kernel.Misc.TvTabs
public import Certificates.Kernel.Misc.Xi

public section

namespace CFSG.KD.Misc.Hyp

open CFSG.KC.Misc.T46 CFSG.KC.Misc.Lines CFSG.KC.Misc.Xi CFSG.KC.Misc.Hyp CFSG.KD.Misc.T46
  CFSG.KD.Misc.Lines CFSG.KD.Misc.Xi CFSG.Fischer.Native

theorem searchAll : ∀ j < 1024, searchK PB LB HS LI NL RES j 1 = true := by
  intro j hj
  have h := Nat.div_add_mod j 128
  have hb : j / 128 < 8 := by omega
  have hi : j % 128 < 128 := Nat.mod_lt _ (by norm_num)
  rw [← h]
  interval_cases hq : j / 128
  exacts [searchAll0 _ hi, searchAll1 _ hi, searchAll2 _ hi, searchAll3 _ hi, searchAll4 _ hi,
    searchAll5 _ hi, searchAll6 _ hi, searchAll7 _ hi]

theorem qb0 : CFSG.KC.Misc.O73.at' 10 QB 0 = 0 := by
  decide +kernel

theorem hyp_true : hypCertificate () = true := by
  rw [hyp_eq]
  exact hyp_sound_q0 (selL := [76, 307, 51, 217, 67]) CFSG.KD.Misc.Unitary.hU rfl pts pos genAll
    xy xP yP perpAll pl linesAll tabAll memAll distinct orb0 orb1 orb2 lamAll liAll lamOK words
    rootLAll rootC nlAll searchAll qb0

end CFSG.KD.Misc.Hyp

end
