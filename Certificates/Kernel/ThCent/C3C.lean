module

public import Certificates.Data.Kernel.ThCent.Outer
public import Certificates.Kernel.ThCent.Data
public import Certificates.Kernel.ThCent.Data3C
public import CFSG.Certificates.Kernel.Th.S.Data.DB_Sel
public import Certificates.Kernel.SporSch.Ru.RowsGen

public section

namespace CFSG.KD.ThCent.C3C

open CFSG.KC.Th CFSG.KC.ThCent

theorem misc : classMisc ThB.LT ThA.CB ThB.HB ThB.GB ThB.OB SV ThB.osh ThB.owd ThB.om ThB.NO
    word FL CS CM o r i1 j1 Hi N1 m1 = true := by decide +kernel

theorem mu : muOK MU ThB.LT = true := by decide +kernel

theorem outer : outerQ ThA.CB MU o r (wordM ThB.LT word) = true := by decide +kernel

@[expose] noncomputable def diffF (i : Nat) : Bool :=
  diffChunk SV R H1 ThB.NO BF (psOf (wordM ThB.LT word) (Nat.sub o 1)) (FL.map (DceS.mat ThA.CB))
    i1 i
@[expose] noncomputable def selF (i : Nat) : Bool := selChunk R ThB.NO CS i
@[expose] noncomputable def commF (i : Nat) : Bool :=
  commChunk ThB.HB ThB.TB (mul24 (mul24 (gmN ThB.HB ThB.GB j1) (wordM ThB.LT word)) Hi) ThB.nT CM i
@[expose] noncomputable def oj1F (i : Nat) : Bool := ojChunk ThB.E1 36864 MU o r OJ1 i
@[expose] noncomputable def oj2F (i : Nat) : Bool := ojChunk ThB.E2 13824 MU o r OJ2 i
@[expose] noncomputable def oj3F (i : Nat) : Bool := ojChunk ThB.E3 486 MU o r OJ3 i
@[expose] noncomputable def oj4F (i : Nat) : Bool := ojChunk ThB.E4 288 MU o r OJ4 i
@[expose] noncomputable def oj5F (i : Nat) : Bool := ojChunk ThB.E5 54 MU o r OJ5 i
@[expose] noncomputable def oj6F (i : Nat) : Bool := ojChunk ThB.E6 6 MU o r OJ6 i
@[expose] noncomputable def oj7F (i : Nat) : Bool := ojChunk ThB.E7 126 MU o r OJ7 i
@[expose] noncomputable def oj8F (i : Nat) : Bool := ojChunk ThB.E8 78 MU o r OJ8 i
@[expose] noncomputable def oj9F (i : Nat) : Bool := ojChunk ThB.E9 72 MU o r OJ9 i
@[expose] noncomputable def oj10F (i : Nat) : Bool := ojChunk ThB.E10 3528 MU o r OJ10 i

#kss_each CFSG.KD.ThCent.C3C.diff CFSG.KD.ThCent.C3C.diffF 9
#kss_each CFSG.KD.ThCent.C3C.sel CFSG.KD.ThCent.C3C.selF 9
#kss_each CFSG.KD.ThCent.C3C.comm CFSG.KD.ThCent.C3C.commF 18
#kss_each CFSG.KD.ThCent.C3C.oj1 CFSG.KD.ThCent.C3C.oj1F 18
#kss_each CFSG.KD.ThCent.C3C.oj2 CFSG.KD.ThCent.C3C.oj2F 7
#kss_each CFSG.KD.ThCent.C3C.oj3 CFSG.KD.ThCent.C3C.oj3F 1
#kss_each CFSG.KD.ThCent.C3C.oj4 CFSG.KD.ThCent.C3C.oj4F 1
#kss_each CFSG.KD.ThCent.C3C.oj5 CFSG.KD.ThCent.C3C.oj5F 1
#kss_each CFSG.KD.ThCent.C3C.oj6 CFSG.KD.ThCent.C3C.oj6F 1
#kss_each CFSG.KD.ThCent.C3C.oj7 CFSG.KD.ThCent.C3C.oj7F 1
#kss_each CFSG.KD.ThCent.C3C.oj8 CFSG.KD.ThCent.C3C.oj8F 1
#kss_each CFSG.KD.ThCent.C3C.oj9 CFSG.KD.ThCent.C3C.oj9F 1
#kss_each CFSG.KD.ThCent.C3C.oj10 CFSG.KD.ThCent.C3C.oj10F 2

theorem mk1 : markOK ThB.E1 ThA.CB MU o r 36864 MK1 0 = true := by decide +kernel
theorem mk2 : markOK ThB.E2 ThA.CB MU o r 13824 MK2 0 = true := by decide +kernel
theorem mk3 : markOK ThB.E3 ThA.CB MU o r 486 MK3 0 = true := by decide +kernel
theorem mk4 : markOK ThB.E4 ThA.CB MU o r 288 MK4 0 = true := by decide +kernel
theorem mk5 : markOK ThB.E5 ThA.CB MU o r 54 MK5 0 = true := by decide +kernel
theorem mk6 : markOK ThB.E6 ThA.CB MU o r 6 MK6 0 = true := by decide +kernel
theorem mk7 : markOK ThB.E7 ThA.CB MU o r 126 MK7 0 = true := by decide +kernel
theorem mk8 : markOK ThB.E8 ThA.CB MU o r 78 MK8 0 = true := by decide +kernel
theorem mk9 : markOK ThB.E9 ThA.CB MU o r 72 MK9 0 = true := by decide +kernel
theorem mk10 : markOK ThB.E10 ThA.CB MU o r 3528 MK10 0 = true := by decide +kernel

end CFSG.KD.ThCent.C3C

end
