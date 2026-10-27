module

public import Certificates.Kernel.RouteP.Lines.Defs
public import CFSG.Certificates.Kernel.Common.IntWords
public meta import Certificates.Data.Kernel.RouteP.TextSlp
public import Certificates.Kernel.RouteP.Text.Facts
public import Mathlib

public section

namespace CFSG.KD.RouteP.ObjW

open CFSG.KC.RouteP

meta def stM : List (List Int) :=
  prefLinesL ['L', ' '] (include_str "../../../../Certificates/Data/RouteP/CoverStab.txt").toList

meta def olM : List (List Int) :=
  stM ++ prefLinesL ['L', ' '] (include_str "../../../../Certificates/Data/RouteP/CoverN0.txt").toList

meta def ylM : List (List Int) :=
  stM ++ prefLinesL ['L', ' '] (include_str "../../../../Certificates/Data/RouteP/CoverY332.txt").toList

end CFSG.KD.RouteP.ObjW

#kc_intwords_list CFSG.KD.RouteP.ObjW.OL CFSG.KD.RouteP.ObjW.olM
#kc_intwords_list CFSG.KD.RouteP.ObjW.YL CFSG.KD.RouteP.ObjW.ylM

namespace CFSG.KD.RouteP

open CFSG.KC CFSG.KC.RouteP

@[expose] noncomputable def olckL (g : Nat) : Bool :=
  lineOK NWO KAO KBO ObjW.OL.toArray 0 (fun ℓ => 2 + ℓ) g

@[expose] noncomputable def ylckL (g : Nat) : Bool :=
  lineOK NWY KAY KBY ObjW.YL.toArray 0 (fun ℓ => 2 + ℓ) g

end CFSG.KD.RouteP

end
