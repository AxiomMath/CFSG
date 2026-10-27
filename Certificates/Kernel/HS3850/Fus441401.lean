module

public import Certificates.Kernel.HS3850.Small
public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public import Certificates.Data.Kernel.Spor.PEnum
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutOuterCheckInputs
public meta import CFSG.LocalAnalysis.OddStandard.SwapPartner.TwHSFusionInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HS3850.Fus

meta def gM : Array (Array Nat) := CFSG.QuasithinUnique.Id2519.HSAut.gensE

meta def giM : Array (Array Nat) := CFSG.QuasithinUnique.Id2519.HSAut.ginvE

meta def rM : Array Nat := CFSG.OddStandard.AltStdSec.SwapPartner.fusB0Tab

end CFSG.KD.HS3850.Fus

#kpenum CFSG.KD.HS3850.FB 3850 12 true CFSG.KD.HS3850.Fus.gM CFSG.KD.HS3850.Fus.giM
  CFSG.KD.HS3850.Fus.rM 300

namespace CFSG.KD.HS3850.Fus

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.HSAutN CFSG.KC.PkPow CFSG.KD.LQT.C4126
open CFSG.KD.LQT.HO CFSG.QuasithinUnique.Id2519.HSAut CFSG.KS.PEnum CFSG.KD.HS3850

@[expose] noncomputable def E21 : Nat := pc (wfoldR lq e2Letters) (wfoldR lq e1Letters)

@[expose] noncomputable def B0 : Nat := pc E21 (pc E21 E21)

theorem fus_gens : bAnd(Nat.beq FB.k 2, bAnd(Nat.beq (FB.G 0) (wfoldR lq e1Letters),
    bAnd(Nat.beq (FB.G 1) (wfoldR lq e2Letters), bAnd(szOK 3850 12,
    allN 2 (fun j => bAnd(canonK 3850 12 (mask 12) (3850 * 12) (FB.GI j),
      Nat.beq (pc (FB.G j) (FB.GI j)) idn)))))) = true := by
  quickRfl

theorem fus_root : bAnd(Nat.beq (pc B0 B0) idn, bAnd(Nat.beq FB.cnt 210,
    penumHdK B0 FB.cnt 300 FB.T FB.PL)) = true := by
  quickRfl

theorem fus_sl : penumSlK 3850 12 (mask 12) (3850 * 12) true FB.G FB.GI FB.k FB.cnt FB.T FB.PL
    FB.POS FB.SRT FB.SRI 0 210 = true := by
  quickRfl

theorem fus_fix : bIf(Nat.beq (fx (pc (HC.F 21) B0)) (fx (HC.F 21)), false, true) = true := by
  quickRfl

theorem fus_root_neg : penumHdK E21 FB.cnt 300 FB.T FB.PL = false := by
  decide +kernel

end CFSG.KD.HS3850.Fus

end
