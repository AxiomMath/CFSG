module

public import Certificates.Kernel.RouteP.Lines.Defs
public import CFSG.Certificates.Kernel.Common.IntWords
public meta import Certificates.Data.Kernel.RouteP.TextSlp
public import Certificates.Kernel.RouteP.Text.Facts
public import Mathlib

public section

namespace CFSG.KD.RouteP.PresW

open CFSG.KC.RouteP

meta def plM : List (List Int) :=
  prefLinesL ['L', ' '] (include_str "../../../../Certificates/Data/RouteP/CoverPresentation.txt").toList ++
    prefLinesL ['L', ' '] (include_str "../../../../Certificates/Data/RouteP/CoverBridge.txt").toList

meta def blM : List (List Int) :=
  prefLinesL ['L', ' '] (include_str "../../../../Certificates/Data/RouteP/CoverBridgeGens.txt").toList

end CFSG.KD.RouteP.PresW

#kc_intwords_list CFSG.KD.RouteP.PresW.PL CFSG.KD.RouteP.PresW.plM
#kc_intwords_list CFSG.KD.RouteP.PresW.BL CFSG.KD.RouteP.PresW.blM

namespace CFSG.KD.RouteP

open CFSG.KC CFSG.KC.RouteP

@[expose] noncomputable def plckL (g : Nat) : Bool :=
  lineOK NWP KAP KBP PresW.PL.toArray 0 (fun ℓ => 2 + ℓ) g

@[expose] noncomputable def bgckL (g : Nat) : Bool :=
  lineOK NWP KAP KBP PresW.BL.toArray 28 bgT g

end CFSG.KD.RouteP

end
