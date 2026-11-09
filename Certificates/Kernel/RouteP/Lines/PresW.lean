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

meta def pairsM : List Int → List (Nat × Int)
  | i :: e :: rest => (i.toNat, e) :: pairsM rest
  | _ => []

meta def lineWM (o : Nat) (l : List Int) : List Int :=
  ((pairsM l).reverse).flatMap fun p =>
    List.replicate p.2.natAbs (if p.2 < 0 then -((p.1 + o : Nat) : Int) else ((p.1 + o : Nat) : Int))

meta def pxM : List (List Int) := plM.map (lineWM 0)

meta def bxM : List (List Int) := blM.map (lineWM 28)

end CFSG.KD.RouteP.PresW

#kc_intwords_list CFSG.KD.RouteP.PresW.PL CFSG.KD.RouteP.PresW.plM
#kc_intwords_list CFSG.KD.RouteP.PresW.BL CFSG.KD.RouteP.PresW.blM
#kc_intwords_list CFSG.KD.RouteP.PresW.PX CFSG.KD.RouteP.PresW.pxM
#kc_intwords_list CFSG.KD.RouteP.PresW.BX CFSG.KD.RouteP.PresW.bxM

namespace CFSG.KD.RouteP

open CFSG.KC CFSG.KC.RouteP

@[expose] noncomputable def lineXOK (L : Array (List Int)) (t : Nat → Nat) (g : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (wordKOK NWP KAP KBP L[Nat.div g 20]! (t (Nat.div g 20)))
    (wordOK NWP L[Nat.div g 20]! (t (Nat.div g 20)) (Nat.mod g 20))
    (Nat.blt (Nat.mod g 20) 19)

@[expose] noncomputable def plckL (g : Nat) : Bool := lineXOK PresW.PX.toArray (fun ℓ => 2 + ℓ) g

@[expose] noncomputable def bgckL (g : Nat) : Bool := lineXOK PresW.BX.toArray bgT g

theorem PresW.px_eq : PresW.PX = PresW.PL.map (lineW 0) :=
  eq_of_beq (by decide +kernel : (PresW.PX == PresW.PL.map (lineW 0)) = true)

theorem PresW.bx_eq : PresW.BX = PresW.BL.map (lineW 28) :=
  eq_of_beq (by decide +kernel : (PresW.BX == PresW.BL.map (lineW 28)) = true)

theorem PresW.getElem!_map {f : List Int → List Int} (hf : f [] = []) (l : List (List Int)) (i : Nat) :
    (l.map f).toArray[i]! = f l.toArray[i]! := by
  rcases Nat.lt_or_ge i l.length with h | h
  · simp [getElem!_pos, h]
  · simp [getElem!_neg, h]
    exact hf.symm

theorem plckL_eq (g : Nat) : plckL g = lineOK NWP KAP KBP PresW.PL.toArray 0 (fun ℓ => 2 + ℓ) g := by
  unfold plckL lineXOK lineOK
  rw [PresW.px_eq, PresW.getElem!_map (f := lineW 0) rfl]

theorem bgckL_eq (g : Nat) : bgckL g = lineOK NWP KAP KBP PresW.BL.toArray 28 bgT g := by
  unfold bgckL lineXOK lineOK
  rw [PresW.bx_eq, PresW.getElem!_map (f := lineW 28) rfl]

end CFSG.KD.RouteP

end
