module

public import Certificates.Kernel.SporSch.Mathieu.M23Cls
public import CFSG.Quasithin.Vol2.KGFactC31M23Data
public import Certificates.Data.Kernel.KGC31P

public section

namespace CertificateChecks.KernelKGC31M23

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.KGC31P CFSG.KS.SporSch.MOC
open CFSG.Quasithin.KGC31.M23 CertificateChecks.KernelSporSch

@[expose] noncomputable def D : ClsD := M23CK.getD 0
  ⟨0, 0, 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩

@[expose] noncomputable def G (l : Int) : Nat := if l = 1 then M23Q.S 0 else M23Q.S 1

@[expose] noncomputable def pw (wd : List Int) : Nat := pword 23 5 G wd

@[expose] noncomputable def X5 : Nat := pw w5
@[expose] noncomputable def X7 : Nat := pw w7
@[expose] noncomputable def X11 : Nat := pw w11
@[expose] noncomputable def X23 : Nat := pw w23

@[expose] noncomputable def cnd (k : Nat) : Nat := pw (candW.getD k [])

@[expose] noncomputable def cAll (c : Nat) (bs : List Nat) : List Nat :=
  bs.map (pcj 23 5 c (pinv 23 5 c))

@[expose] noncomputable def wP : List Nat := wW.map pw
@[expose] noncomputable def tP : List Nat := tW.map pw
@[expose] noncomputable def eP : List Nat := eW.map pw
@[expose] noncomputable def sP : List Nat := sW.map pw

@[expose] noncomputable def C5 : List (List Nat) :=
  [cAll (cnd 0) tP, cAll (cnd 1) wP, cAll (cnd 2) wP, cAll (cnd 3) wP]

@[expose] noncomputable def C7 : List (List Nat) :=
  [cAll (cnd 4) eP, cAll (cnd 5) wP, cAll (cnd 6) eP, cAll (cnd 7) sP]

@[expose] noncomputable def invOne (k : Nat) : Bool :=
  permOK 23 5 (mask 5) (23 * 5) (D.ST k) (pinv 23 5 (D.ST k)) &&
    porbOne 23 5 5 X5 C5 (D.ST k) && porbOne 23 5 7 X7 C7 (D.ST k) &&
    pactOne 23 5 11 X11 (D.ST k) && pactOne 23 5 23 X23 (D.ST k)

@[expose] noncomputable def invBlk (k : Nat) : Bool :=
  (List.range' (500 * k) (min 500 (D.c - 500 * k))).all invOne

end CertificateChecks.KernelKGC31M23

end
