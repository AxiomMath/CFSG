module

public meta import Lean
meta import Certificates.Data.G24LinEq
public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import CFSG.Open.LocalVocabulary

namespace CFSG.KD.G24Lin.Gen

open CFSG.Quasithin.St84.G24LE CFSG.Quasithin.St84.G24MF
open CFSG.Quasithin.H.Q13 (om)

meta def bitsN (s : String) : Nat :=
  (s.toList.zipIdx).foldl (fun acc (c, i) => if c = '1' then acc ||| (1 <<< i) else acc) 0

meta def packLanes (l : List Nat) : Nat :=
  (l.zipIdx).foldl (fun acc (x, i) => acc ||| (x <<< (16 * i))) 0

meta def rowN (l : List (ZMod 2)) : Nat :=
  (l.zipIdx).foldl (fun acc (x, i) => acc ||| (x.val <<< i)) 0

meta def spanData {R C K : Type} (rows : List R) (cols : List C) (ks : List K)
    (m : R → C → ZMod 2) (k : C → K → ZMod 2) (ps ys : List String) : List Nat :=
  ps.map bitsN ++ cols.map (fun c => rowN (ks.map (k c))) ++ ys.map bitsN ++
    rows.map fun r => rowN (cols.map (m r))

meta def quadLanes (n d : Nat) (R : Fin 3 → Matrix (Fin n) (Fin n) (ZMod 2))
    (S : Fin 3 → Matrix (Fin d) (Fin d) (ZMod 2)) : List Nat :=
  [packLanes <| (List.finRange 3).flatMap fun g => (List.finRange n).map fun i =>
      rowN ((List.finRange n).map fun r => R g r i),
    packLanes <| (List.finRange 3).flatMap fun g => (List.finRange d).map fun t =>
      rowN ((List.finRange d).map fun s => S g t s),
    packLanes <| (monoList n).map fun mu => rowN ((List.finRange n).map fun i => testVec mu i)]

meta def ext2KListM : List ((Fin 2 × Fin 4) ⊕ Fin 2) :=
  ((List.finRange 2).flatMap fun i => (List.finRange 4).map fun j => Sum.inl (i, j)) ++
    (List.finRange 2).map Sum.inr

meta def dq1 : List Nat := spanData (quadRows 8 2) (quadCols 8 2) (List.finRange 2)
  (quadM matV1 matZ1) (quadK sqV1 cmV1 om) pQuad1 yQuad1

meta def dq2 : List Nat := spanData (quadRows 6 4) (quadCols 6 4) (List.finRange 2)
  (quadM matV2 matZ2) (quadK sqV2 cmV2 omegaN) pQuad2 yQuad2

meta def dc : List Nat := spanData commRows commCols (List.finRange 2) commM commK pComm yComm

meta def de : List Nat := spanData ext2Rows ext2Cols ext2KListM ext2M ext2K pExt2 yExt2

meta def cq1 : List Nat := quadLanes 8 2 matV1 matZ1

meta def cq2 : List Nat := quadLanes 6 4 matV2 matZ2

end CFSG.KD.G24Lin.Gen

#kss_ntree CFSG.KD.G24Lin.DQ1 CFSG.KD.G24Lin.Gen.dq1
#kss_ntree CFSG.KD.G24Lin.DQ2 CFSG.KD.G24Lin.Gen.dq2
#kss_ntree CFSG.KD.G24Lin.DC CFSG.KD.G24Lin.Gen.dc
#kss_ntree CFSG.KD.G24Lin.DE CFSG.KD.G24Lin.Gen.de
#kss_ntree CFSG.KD.G24Lin.CQ1 CFSG.KD.G24Lin.Gen.cq1
#kss_ntree CFSG.KD.G24Lin.CQ2 CFSG.KD.G24Lin.Gen.cq2
