module

public import Certificates.Kernel.KGC31M22.Data
public import Certificates.Kernel.SporSch.Mathieu.M22Cls
public import Certificates.Data.Kernel.KGC31PB

public section

namespace CertificateChecks.KernelKGC31M22

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.KGC31P CFSG.KS.SporSch.MOC
open CFSG.Quasithin.KGC31.M22 CertificateChecks.KernelSporSch

@[expose] noncomputable def G (l : Int) : Nat := if l = 1 then M22Q.S 0 else M22Q.S 1

@[expose] noncomputable def pw (wd : List Int) : Nat := pword 22 5 G wd

@[expose] noncomputable def pwN (wd : List Nat) : Nat := pw (wd.map Int.ofNat)

@[expose] noncomputable def X5 : Nat := pw w5
@[expose] noncomputable def X7 : Nat := pw w7
@[expose] noncomputable def X11 : Nat := pw w11

@[expose] noncomputable def P5 : List Nat := (List.range 5).map (ppw 22 5 X5)

@[expose] noncomputable def P7 : List Nat := (List.range 7).map (ppw 22 5 X7)

@[expose] noncomputable def P11 : List Nat := (List.range 11).map (ppw 22 5 X11)

@[expose] noncomputable def hexP : List Nat := hexW.map pw
@[expose] noncomputable def duadP : List Nat := duadW.map pw
@[expose] noncomputable def e8P : List Nat := e8W.map pw

@[expose] noncomputable def hcP : Nat := pw hexConjW

@[expose] noncomputable def hex2P : List Nat := hexP.map (pcj 22 5 hcP (pinv 22 5 hcP))

@[expose] noncomputable def C5 : List (List Nat) := [duadP, hexP, hex2P]

@[expose] noncomputable def C7 : List (List Nat) := [e8P]

@[expose] noncomputable def D : ClsD := M22CK.getD 0 clsD0

@[expose] noncomputable def invOne (k : Nat) : Bool :=
  permOK 22 5 (mask 5) (22 * 5) (D.ST k) (pinv 22 5 (D.ST k)) &&
    P5.all (fun x => porbOne 22 5 5 x C5 (D.ST k)) &&
    P7.all (fun x => porbOne 22 5 7 x C7 (D.ST k)) &&
    P11.all (fun x => pactOne 22 5 11 x (D.ST k))

@[expose] noncomputable def invBlk (k : Nat) : Bool :=
  (List.range' (200 * k) (min 200 (D.c - 200 * k))).all invOne

@[expose] noncomputable def CB : List Nat :=
  pfilterProducts 22 5 (fun _ => true) (trPL 22 5 M22C1.LR M22C1.TR 3) (pidn 22 5) []

@[expose] noncomputable def cent (r : Nat) : List Nat := CB.map (pcj 22 5 r (pinv 22 5 r))

@[expose] noncomputable def cosAll (U : List Nat) (r₀ : Nat) (rs : List Nat) (cC cN : Nat) :
    Bool :=
  Nat.beq (pcj 22 5 r₀ (pinv 22 5 r₀) M22OC.R0) (U.headD 0) && pcosetOK 22 5 (U.headD 0) U rs &&
    Nat.beq ((cent r₀).countP (pcommAll 22 5 U)) cC &&
    Nat.beq (pcosetCount 22 5 (cent r₀) rs fun g => pnormAll 22 5 U g (pinv 22 5 g)) cN

@[expose] noncomputable def cosBlk (i : Nat) : Bool :=
  if i = 0 then cosAll hexP (pwN W.hexR0) (W.hexRs.map pwN) 16 5760
  else if i = 1 then cosAll duadP (pwN W.duadR0) (W.duadRs.map pwN) 16 1920
  else cosAll e8P (pwN W.e8R0) (W.e8Rs.map pwN) 8 1344

end CertificateChecks.KernelKGC31M22

end
