module

public import Certificates.Kernel.PhanD4Dce.CTNetChecks
public import CFSG.Certificates.Kernel.Misc.Coset.ActNetSound

public section

namespace CFSG.KAct.PhanD4CT

open CFSG.KC.MiscCoset.Act

theorem all : allR (nat_lit 0) (nat_lit 1120)
    (pointOK CFSG.KAct.PhanD4CT.A (nat_lit 29) (nat_lit 1120)
      (CFSG.KAct.PhanD4CT.R ++ CFSG.KAct.PhanD4CT.RD ++ CFSG.KAct.PhanD4CT.RC ++
        CFSG.KAct.PhanD4CT.RS)) = true :=
  pointOK_all_of (k := 11) (Nf := CFSG.KAct.PhanD4CT.NT) (by norm_num) (by norm_num) ct_let
    (fun c hc => allR_spec ct_nets c (Nat.zero_le c) (by omega)) ct_rels ct_codes

end CFSG.KAct.PhanD4CT

end
