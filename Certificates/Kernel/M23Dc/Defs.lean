module

public import Certificates.Kernel.M23Dc.Data
public import Certificates.Data.Kernel.SporLatDcCode
public import Certificates.Data.Kernel.SporLatDcSort
public import Certificates.Data.Kernel.SporLatDcT

public noncomputable section

namespace CFSG.KD.M23Dc

open CFSG.KC.SLDc CFSG.QuasithinUnique.Ch1.SporLat

@[expose] def m23PT : Nat := 6008758457487233294062889244845810110929497151550854083423562014760272857190569972453042096773078508025045325053374674249468109144193149267814924096030015457584038901334500080766264889839720793770612232400458138687419369930855323252569875926759694401627087308343459212477664257

@[expose] def L0 (l : Nat) : Nat → Nat := fun p =>
  Nat.mod (Nat.shiftRight m23PT (Nat.mul 5 (Nat.add (Nat.mul 23 l) p))) 32

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

@[expose] def m23CodeTab (j : Nat) :
    List (List Nat) × List (List Nat) × List (List Nat) × List Nat :=
  JT.T.getD j default

@[expose] def memOK (j : Nat) : Bool :=
  omOKT 23 74 11 (mLet j) Δc (m23CodeTab j).1 (m23CodeTab j).2.1 (m23CodeTab j).2.2.1
    (m23CodeTab j).2.2.2
    (omOf (oc j).1 (oc j).2.1 (oc j).2.2.1 (oc j).2.2.2.1)

@[expose] def ch (i : Nat) : Bool := chunkOK C D i

end CFSG.KD.M23Dc

end
