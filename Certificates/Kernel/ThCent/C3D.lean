module

public import Certificates.Data.Kernel.ThCent.Outer
public import Certificates.Kernel.ThCent.Data
public import Certificates.Kernel.ThCent.Data3C
public import CFSG.Certificates.Kernel.Th.S.Data.DB_Sel
public import Certificates.Kernel.SporSch.Ru.RowsGen

public section

namespace CFSG.KD.ThCent.C3D

open CFSG.KC.Th CFSG.KC.ThCent

theorem misc : classMisc ThB.LT ThA.CB ThB.HB ThB.GB ThB.OB SV ThB.osh ThB.owd ThB.om ThB.NO
    word FL CS CM o r i1 j1 Hi N1 m1 = true := by decide +kernel

theorem jv : DceS.notB (jv2 C3C.MU (wordM ThB.LT word)) = true := by decide +kernel

@[expose] noncomputable def diffF (i : Nat) : Bool :=
  diffChunk SV R H1 ThB.NO BF (psOf (wordM ThB.LT word) (Nat.sub o 1)) (FL.map (DceS.mat ThA.CB))
    i1 i
@[expose] noncomputable def selF (i : Nat) : Bool := selChunk R ThB.NO CS i
@[expose] noncomputable def commF (i : Nat) : Bool :=
  commChunk ThB.HB ThB.TB (mul24 (mul24 (gmN ThB.HB ThB.GB j1) (wordM ThB.LT word)) Hi) ThB.nT CM i

#kss_each CFSG.KD.ThCent.C3D.diff CFSG.KD.ThCent.C3D.diffF 9
#kss_each CFSG.KD.ThCent.C3D.sel CFSG.KD.ThCent.C3D.selF 9
#kss_each CFSG.KD.ThCent.C3D.comm CFSG.KD.ThCent.C3D.commF 18

end CFSG.KD.ThCent.C3D

end
