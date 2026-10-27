module

public import Certificates.Kernel.M23Dc.Data
public import Certificates.Data.Kernel.SporLatDcCode
public import Certificates.Data.Kernel.SporLatDcSort

public noncomputable section

namespace CFSG.KD.M23Dc

open CFSG.KC.SLDc CFSG.QuasithinUnique.Ch1.SporLat

@[expose] def L0 (l : Nat) : Nat → Nat := tabF (J.tabs.getD l [])

@[expose] def L (l : Nat) : Nat → Nat := pairF 23 (L0 l)

@[expose] def C : DcCtx := ⟨529, J.delta, L, 6, 3, 7, 79695⟩

@[expose] def D : DcData where
  w := J.w
  oidC := J.oidC
  tlC := J.tlC
  dpC := J.dpC
  obase := J.obase
  osz := J.osz
  K := J.K
  sep := J.sep
  mw := J.mw
  Rc := [J.R0, J.R1, J.R2, J.R3, J.R4, J.R5, J.R6, J.R7]
  msum := J.msum
  joins := J.joins
  csz := J.csz
  c0 := J.c0
  pcz := J.pcz
  npc := J.npc

@[expose] def Δc : List Nat := [246, 409, 472, 240913, 12093668392540053406538]

@[expose] def T (l : Nat) : Array Nat := (J.tabs.getD l []).toArray

@[expose] def sT : List (Array Nat) := [T 2, T 3, T 4]

@[expose] def mLet (j : Nat) : Array (Array Nat) :=
  (sT ++ (J.mw.getD j []).map (wordTabL #[T 0, T 1] 23)).toArray

@[expose] def oc (j : Nat) :
    List (List (List Nat)) × List (List Nat) × List Nat × List Nat × List Nat :=
  J.OmC.getD j default

@[expose] def memOK (j : Nat) : Bool :=
  omCodeC 23 (mLet j) Δc 64 (oc j).1 (oc j).2.1 (oc j).2.2.1 (oc j).2.2.2.1 (oc j).2.2.2.2

@[expose] def ch (i : Nat) : Bool := chunkOK C D i

end CFSG.KD.M23Dc

end
