module

public import Certificates.Kernel.KGC31M24.Data
public import Certificates.Data.Kernel.KGC31P
public import Certificates.Data.Kernel.Child3

public section

namespace CertificateChecks.KernelKGC31M24

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.KGC31P CFSG.KC.Child3
open CFSG.Quasithin.KGC31.M24 CertificateChecks.KernelSporSch

@[expose] noncomputable def G (l : Int) : Nat := if l = 1 then M24Q.S 0 else M24Q.S 1

@[expose] noncomputable def pw (wd : List Int) : Nat := pword 24 5 G wd

@[expose] noncomputable def X5 : Nat := pw w5
@[expose] noncomputable def X7 : Nat := pw w7
@[expose] noncomputable def X11 : Nat := pw w11
@[expose] noncomputable def X23 : Nat := pw w23

@[expose] noncomputable def cnd (k : Nat) : Nat := pw (candW.getD k [])

@[expose] noncomputable def cAll (c : Nat) (bs : List Nat) : List Nat := bs.map (pcj 24 5 c (pinv 24 5 c))

@[expose] noncomputable def oP : List Nat := oW.map pw
@[expose] noncomputable def s16P : List Nat := s16W.map pw
@[expose] noncomputable def s32P : List Nat := s32W.map pw
@[expose] noncomputable def r2P : List Nat := r2W.map pw
@[expose] noncomputable def u4P : List Nat := u4W.map pw
@[expose] noncomputable def u5P : List Nat := u5W.map pw
@[expose] noncomputable def u6P : List Nat := u6W.map pw
@[expose] noncomputable def tP : List Nat := tW.map pw

@[expose] noncomputable def C5 : List (List Nat) := [cAll (cnd 0) s32P, cAll (cnd 1) s32P,
    cAll (cnd 2) s32P, cAll (cnd 3) s16P, cAll (cnd 4) oP, cAll (cnd 5) oP,
    cAll (cnd 6) oP, cAll (cnd 7) oP]

@[expose] noncomputable def C7 : List (List Nat) := [cAll (cnd 8) u4P, cAll (cnd 9) u4P,
    cAll (cnd 10) r2P, cAll (cnd 11) r2P, cAll (cnd 12) u5P, cAll (cnd 13) oP,
    cAll (cnd 14) u4P, cAll (cnd 15) r2P, cAll (cnd 16) oP, cAll (cnd 17) u5P,
    cAll (cnd 18) u5P, cAll (cnd 19) oP, cAll (cnd 20) u6P, cAll (cnd 21) u6P,
    cAll (cnd 22) u6P, cAll (cnd 23) u6P, cAll (cnd 24) u6P, cAll (cnd 25) u6P]

@[expose] noncomputable def fC (fr : List (ℕ × List ℤ)) : List (List Nat) :=
  fr.map fun p => cAll (pw p.2) (if p.1 = 1 then oP else tP)

@[expose] noncomputable def invOne (j : Nat) : Bool :=
  permOK 24 5 (mask 5) (24 * 5) (RI.E j) (pinv 24 5 (RI.E j)) &&
    porbOne 24 5 5 X5 C5 (RI.E j) && porbOne 24 5 7 X7 C7 (RI.E j) &&
    pactOne 24 5 11 X11 (RI.E j) && pactOne 24 5 23 X23 (RI.E j)

@[expose] noncomputable def invBlk (k : Nat) : Bool :=
  (List.range' (1000 * k) (min 1000 (RI.N - 1000 * k))).all invOne

@[expose] noncomputable def clsBlk (k : Nat) : Bool :=
  (List.range' (1000 * k) (min 1000 (RI.N - 1000 * k))).all
    (repK 24 5 RI.GP RI.GIP 2 RI.CS RI.OFF RI.CI RI.E RI.P RI.L RI.K RI.S RI.SI RI.N 40000)

@[expose] noncomputable def qE (j : Nat) : Nat :=
  CFSG.KS.SporSch.MOC.elemK 24 5 (mask 5) (24 * 5) (pidn 24 5) QQ.LR QQ.TR 2 j

@[expose] noncomputable def frOne (k : Nat) (fr : List (ℕ × List ℤ)) (j : Nat) : Bool :=
  permOK 24 5 (mask 5) (24 * 5) (qE j) (pinv 24 5 (qE j)) &&
    pframeOne 24 5 7 X7 (cAll (cnd k) u5P) (fC fr) (pcj 24 5 (cnd k) (pinv 24 5 (cnd k)) (qE j))

end CertificateChecks.KernelKGC31M24

end
