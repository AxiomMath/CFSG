module

public import Certificates.Kernel.HeDc.Data
public import Certificates.Kernel.LocalQT.Base.C4141D
public import Certificates.Data.Kernel.SporLatDc

public noncomputable section

namespace CFSG.KD.HeDc

open CFSG.KC.SLDc CFSG.QuasithinUnique.Ch1.SporLat

@[expose] def nodes : List Nat := [0, 1, 197, 207, 226, 247, 256, 262, 263, 266]

@[expose] def L (l p : Nat) : Nat :=
  CFSG.KC.LQT.PW.imgW 14 (CFSG.KD.LQT.C4141.TF (nodes.getD l 0)) p

@[expose] def Δ : List Nat :=
  [202, 383, 847, 1424, 2149, 2563, 2843, 3224, 3879, 4471, 4498, 4700, 5020, 6619, 6732, 7546]

@[expose] def C : DcCtx := ⟨8330, Δ, L, 8, 4, 10, 3935925⟩

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
  Rc := [J.R0, J.R1, J.R2, J.R3, J.R4, J.R5, J.R6, J.R7, J.R8, J.R9, J.R10, J.R11, J.R12,
    J.R13, J.R14, J.R15, J.R16, J.R17, J.R18, J.R19, J.R20, J.R21, J.R22, J.R23]
  msum := J.msum
  joins := J.joins
  csz := J.csz
  c0 := J.c0
  pcz := J.pcz
  npc := J.npc

@[expose] def omD {Lab : Type} (x : List Lab × List (List Nat) × List Nat × List Nat) :
    OmegaData Lab :=
  ⟨x.1.toArray, (x.2.1.map List.toArray).toArray, x.2.2.1.toArray, x.2.2.2.toArray⟩

@[expose] def Om (j : Nat) : OmegaData (List Nat) := omD (J.Om.getD j default)

@[expose] def Ot (j : Nat) : OmegaData (List (List Nat)) := omD (J.Ot.getD j default)

@[expose] def Lm (j l : Nat) : Nat → Nat :=
  bif Nat.blt l 4 then L (Nat.add 2 l) else wordF' (J.mw.getD j []) (Nat.sub l 4)
where
  wordF' (ws : List (List Nat)) (i : Nat) : Nat → Nat := CFSG.KC.E64F.wordF L (ws.getD i [])

@[expose] def memOK (j : Nat) : Bool :=
  omOKG (fun l x => labF (Lm j l) x) Δ (Nat.add 4 (J.mw.getD j []).length) (Om j) &&
    omOKG (fun l X => X.map (labF (L (Nat.add 2 l)))) (Om j).lbl.toList 4 (Ot j)

@[expose] def gensInF (j jj : Nat) : Bool :=
  (J.mw.getD j []).all fun w => (Om jj).lbl.toList.contains (labF (CFSG.KC.E64F.wordF L w) Δ)

@[expose] def inclL : List (List Nat) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10], [1, 2, 3, 4, 9], [2, 3, 4], [3], [4], [3, 5],
    [2, 3, 4, 5, 6], [7], [3, 5, 7, 8], [4, 9], [4, 7, 9, 10]]

@[expose] def inclOK : Bool :=
  (List.range 11).all fun j => (List.range 11).all fun jj =>
    gensInF j jj == (inclL.getD j []).contains jj

end CFSG.KD.HeDc

end
