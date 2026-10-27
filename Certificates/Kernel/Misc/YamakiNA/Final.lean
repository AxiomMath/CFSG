module

public import CFSG.Certificates.Kernel.Misc.YamakiNASound
public import Certificates.Kernel.Misc.YamakiRep.FinalF
public import Certificates.Kernel.Misc.YamakiNA.Checks
public import Certificates.Kernel.Misc.YamakiNA.ChecksAl
public import CFSG.Certificates.Kernel.Misc.YamakiNWSound
public import Certificates.Kernel.Misc.YamakiNA.ChecksW
public import CFSG.Certificates.Kernel.Misc.YamakiNOSound
public import Certificates.Kernel.Misc.YamakiNA.ChecksO
public import Certificates.Kernel.Misc.YamakiNA.ChecksS

public section

namespace CFSG.KD.YamakiNA

open CFSG.ClassicalInvolution.Sp62Rec CFSG.KC.YamakiNA CFSG.KD.YamakiRepF CFSG.KC.YamakiA0

theorem centA0Check_holds : centA0Check () = true :=
  centA0Check_of enumH_repF.1
    (enumA0_inv CFSG.KD.YamakiA0.ya0_gens CFSG.KD.YamakiA0.ya0_tab_ok).1 yfH_gens na550822cK.all

theorem normA0Check_holds : normA0Check () = true :=
  normA0Check_of (enumA0_inv CFSG.KD.YamakiA0.ya0_gens CFSG.KD.YamakiA0.ya0_tab_ok).1
    CFSG.KD.YamakiA0.ya0_gens na550822nm

theorem sevenCheck_holds : sevenCheck () = true :=
  sevenCheck_of (enumA0_inv CFSG.KD.YamakiA0.ya0_gens CFSG.KD.YamakiA0.ya0_tab_ok).1
    (enumA0_inv CFSG.KD.YamakiA0.ya0_gens CFSG.KD.YamakiA0.ya0_tab_ok).2.2.2.2
    CFSG.KD.YamakiA0.ya0_gens na550822sv

theorem alphaClassCheck_holds : alphaClassCheck () = true :=
  alphaClassCheck_of CFSG.KD.YamakiA0.ya0_gens na550822ac

theorem centAlphaCheck_holds : centAlphaCheck () = true :=
  centAlphaCheck_of enumN_repF.1 enumX_repF.1 yfN_gens enumN_repF.2.2.2.2
    (Nat.blt_eq.mp na550822b5) na550822aK.all

theorem wCheck_holds : wCheck () = true :=
  CFSG.KC.YamakiNW.wCheck_of (enumA0_inv CFSG.KD.YamakiA0.ya0_gens CFSG.KD.YamakiA0.ya0_tab_ok).1
    CFSG.KD.YamakiA0.ya0_gens na550822w

theorem stabWCheck_holds : stabWCheck () = true :=
  CFSG.KC.YamakiNW.stabWCheck_of enumH_repF.1 enumX_repF.1 na550822sK.all

theorem rhoKerCheck_holds : rhoKerCheck () = true :=
  CFSG.KC.YamakiNW.rhoKerCheck_of enumN_repF.1
    (enumA0_inv CFSG.KD.YamakiA0.ya0_gens CFSG.KD.YamakiA0.ya0_tab_ok).1 na550822rK.all

theorem orbCheck_holds : orbCheck () = true :=
  CFSG.KC.YamakiNO.orbCheck_of (enumA0_inv CFSG.KD.YamakiA0.ya0_gens CFSG.KD.YamakiA0.ya0_tab_ok).1
    (enumA0_inv CFSG.KD.YamakiA0.ya0_gens CFSG.KD.YamakiA0.ya0_tab_ok).2.2.2.2
    CFSG.KD.YamakiA0.ya0_gens na550822or

theorem sylMeetCheck_holds : sylMeetCheck () = true := by
  have hS := CFSG.KC.YamakiS0.enumS0_inv CFSG.KD.YamakiS0.ys0_gens CFSG.KD.YamakiS0.ys0_tab_ok
  exact CFSG.KC.YamakiNO.sylMeetCheck_of hS.1 hS.2.2
    (enumA0_inv CFSG.KD.YamakiA0.ya0_gens CFSG.KD.YamakiA0.ya0_tab_ok).1 CFSG.KD.YamakiA0.ya0_gens
    na550822yK.all

theorem e8Check_holds : e8Check () = true :=
  CFSG.KC.YamakiNO.e8Check_of CFSG.KD.YamakiA0.ya0_gens na550822e8

end CFSG.KD.YamakiNA

end
