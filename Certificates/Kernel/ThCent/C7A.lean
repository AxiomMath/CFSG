module

public import Certificates.Data.Kernel.ThCent.Defs
public import Certificates.Kernel.ThCent.Data
public import CFSG.Certificates.Kernel.Th.S.Data.DB_Sel
public import Certificates.Kernel.SporSch.Ru.RowsGen

public section

namespace CFSG.KD.ThCent.C7A

open CFSG.KC.Th CFSG.KC.ThCent

theorem misc : classMisc ThB.LT ThA.CB ThB.HB ThB.GB ThB.OB SV ThB.osh ThB.owd ThB.om ThB.NO
    word FL CS CM o r i1 j1 Hi N1 m1 = true := by decide +kernel

@[expose] noncomputable def diffF (i : Nat) : Bool :=
  diffChunk SV R H1 ThB.NO BF (psOf (wordM ThB.LT word) (Nat.sub o 1)) (FL.map (DceS.mat ThA.CB))
    i1 i
@[expose] noncomputable def selF (i : Nat) : Bool := selChunk R ThB.NO CS i
@[expose] noncomputable def commF (i : Nat) : Bool :=
  commChunk ThB.HB ThB.TB (mul24 (mul24 (gmN ThB.HB ThB.GB j1) (wordM ThB.LT word)) Hi) ThB.nT CM i
@[expose] noncomputable def or1F (i : Nat) : Bool := orChunk ThB.E1 36864 o r OR1 i
@[expose] noncomputable def or2F (i : Nat) : Bool := orChunk ThB.E2 13824 o r OR2 i
@[expose] noncomputable def or3F (i : Nat) : Bool := orChunk ThB.E3 486 o r OR3 i
@[expose] noncomputable def or4F (i : Nat) : Bool := orChunk ThB.E4 288 o r OR4 i
@[expose] noncomputable def or5F (i : Nat) : Bool := orChunk ThB.E5 54 o r OR5 i
@[expose] noncomputable def or6F (i : Nat) : Bool := orChunk ThB.E6 6 o r OR6 i
@[expose] noncomputable def or7F (i : Nat) : Bool := orChunk ThB.E7 126 o r OR7 i
@[expose] noncomputable def or8F (i : Nat) : Bool := orChunk ThB.E8 78 o r OR8 i
@[expose] noncomputable def or9F (i : Nat) : Bool := orChunk ThB.E9 72 o r OR9 i
@[expose] noncomputable def or10F (i : Nat) : Bool := orChunk ThB.E10 3528 o r OR10 i

#kss_each CFSG.KD.ThCent.C7A.diff CFSG.KD.ThCent.C7A.diffF 9
#kss_each CFSG.KD.ThCent.C7A.sel CFSG.KD.ThCent.C7A.selF 9
#kss_each CFSG.KD.ThCent.C7A.comm CFSG.KD.ThCent.C7A.commF 18
#kss_each CFSG.KD.ThCent.C7A.or1 CFSG.KD.ThCent.C7A.or1F 18
#kss_each CFSG.KD.ThCent.C7A.or2 CFSG.KD.ThCent.C7A.or2F 7
#kss_each CFSG.KD.ThCent.C7A.or3 CFSG.KD.ThCent.C7A.or3F 1
#kss_each CFSG.KD.ThCent.C7A.or4 CFSG.KD.ThCent.C7A.or4F 1
#kss_each CFSG.KD.ThCent.C7A.or5 CFSG.KD.ThCent.C7A.or5F 1
#kss_each CFSG.KD.ThCent.C7A.or6 CFSG.KD.ThCent.C7A.or6F 1
#kss_each CFSG.KD.ThCent.C7A.or7 CFSG.KD.ThCent.C7A.or7F 1
#kss_each CFSG.KD.ThCent.C7A.or8 CFSG.KD.ThCent.C7A.or8F 1
#kss_each CFSG.KD.ThCent.C7A.or9 CFSG.KD.ThCent.C7A.or9F 1
#kss_each CFSG.KD.ThCent.C7A.or10 CFSG.KD.ThCent.C7A.or10F 2

end CFSG.KD.ThCent.C7A

end
