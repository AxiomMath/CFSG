module

public import Certificates.Kernel.J1Dc.Data
public import Certificates.Data.Kernel.SporLatDcCode

public noncomputable section

namespace CFSG.KD.J1Dc

open CFSG.KC.SLDc CFSG.KC.E64F CFSG.QuasithinUnique.Ch1.SporLat

@[expose] def L (l : Nat) : Nat → Nat := CFSG.KC.LQT.PW.imgW J.tw (J.tc.getD l 0)

@[expose] def C : DcCtx := ⟨1540, J.delta, L, 6, 3, 3, 21945⟩

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
  Rc := [J.R0, J.R1, J.R2, J.R3, J.R4, J.R5, J.R6, J.R7, J.R8, J.R9, J.R10, J.R11, J.R12, J.R13,
    J.R14, J.R15, J.R16, J.R17, J.R18, J.R19, J.R20, J.R21, J.R22, J.R23]
  msum := J.msum
  joins := J.joins
  csz := J.csz
  c0 := J.c0
  pcz := J.pcz
  npc := J.npc

@[expose] def ch (i : Nat) : Bool := chunkOK C D i

@[expose] def L2 (i : Nat) : Nat → Nat := L (Nat.add 2 i)

@[expose] def mf (j l : Nat) : Nat → Nat :=
  bif Nat.blt l 3 then L2 l else wordF L ((J.mw.getD j []).getD (Nat.sub l 3) [])

@[expose] def Om (j : Nat) : OmegaData (List Nat) := omL (J.Om.getD j default)

@[expose] def memOK (j : Nat) : Bool :=
  omOKG (fun l x => labF (mf j l) x) J.delta (Nat.add 3 (J.mw.getD j []).length) (Om j)

@[expose] def normOK : Bool :=
  (J.mw.getD 16 []).all fun w => (List.range 3).all fun i =>
    labF (L2 i) (labF (wordF L w) J.delta) == labF (wordF L w) J.delta

@[expose] def centOK (p : Nat × List Nat) : Bool :=
  (List.range 1540).all (fun q => wordF L2 p.2 (wordF L2 p.2 q) == q &&
    (List.range (Nat.add 3 (J.mw.getD p.1 []).length)).all fun l =>
      mf p.1 l (wordF L2 p.2 q) == wordF L2 p.2 (mf p.1 l q)) &&
  (List.range 1540).any fun q => !(wordF L2 p.2 q == q)

@[expose] def Sw : List (List Nat) := [[], [0], [1], [2], [0, 1], [0, 2], [1, 2], [0, 1, 2]]

@[expose] def sImg (i : Nat) : List Nat := (List.range 1540).map (wordF L2 (Sw.getD i []))

@[expose] def sClosedOK : Bool :=
  (List.range 3).all fun i => Sw.all fun w => Sw.any fun w' =>
    (List.range 1540).all fun p => L2 i (wordF L2 w p) == wordF L2 w' p

@[expose] def sDistinctOK : Bool :=
  (List.range 8).all fun i => (List.range 8).all fun j => Nat.beq i j || !(sImg i == sImg j)

@[expose] def sInvOK : Bool :=
  (List.range 3).all fun i => (List.range 1540).all fun p =>
    L2 i (L2 i p) == p && L (Nat.add 5 i) p == L2 i p

@[expose] def rangeOK : Bool :=
  (List.range 8).all fun l => (List.range 1540).all fun p => Nat.blt (L l p) 1540

end CFSG.KD.J1Dc

end
