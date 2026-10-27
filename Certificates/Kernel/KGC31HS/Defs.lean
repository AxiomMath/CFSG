module

public import Certificates.Kernel.KGC31HS.Data
public import Certificates.Kernel.HS100.ChainData
public import Certificates.Kernel.HS100.FiveData
public import Certificates.Data.Kernel.KGC31PB
public import Certificates.Data.Kernel.Child3

public section

namespace CertificateChecks.KernelKGC31HS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.KGC31P CFSG.KC.Child3
open CFSG.Quasithin.KGC31.HS CertificateChecks.KernelHS100

@[expose] noncomputable def G (l : Int) : Nat := if l = 1 then HP.F 0 else HP.F 1

@[expose] noncomputable def pw (wd : List Int) : Nat := pword 100 7 G wd

@[expose] noncomputable def X7 : Nat := pw w7
@[expose] noncomputable def X11 : Nat := pw w11
@[expose] noncomputable def RB : Nat := pw wB

@[expose] noncomputable def cnd (k : Nat) : Nat := pw (candW.getD k [])

@[expose] noncomputable def cAll (c : Nat) (bs : List Nat) : List Nat :=
  bs.map (pcj 100 7 c (pinv 100 7 c))

@[expose] noncomputable def u16P : List Nat := u16W.map pw
@[expose] noncomputable def u8P : List Nat := u8W.map pw
@[expose] noncomputable def qP : List Nat := qGenW.map pw
@[expose] noncomputable def r16P : List Nat := u16CosetW.map pw
@[expose] noncomputable def r8P : List Nat := u8CosetW.map pw

@[expose] noncomputable def C5 : List (List Nat) := (List.range 5).map fun k => cAll (cnd k) u16P

@[expose] noncomputable def C7 : List (List Nat) := [cAll (cnd 5) u8P, cAll (cnd 6) u8P]

@[expose] noncomputable def invOne (j : Nat) : Bool :=
  permOK 100 7 (mask 7) (100 * 7) (RH.E j) (pinv 100 7 (RH.E j)) &&
    porbOne 100 7 5 (FV.F 2) C5 (RH.E j) && pactOne 100 7 5 (FV.F 4) (RH.E j) &&
    pactOne 100 7 5 (FV.F 25) (RH.E j) && porbOne 100 7 7 X7 C7 (RH.E j) &&
    pactOne 100 7 11 X11 (RH.E j)

@[expose] noncomputable def invBlk (k : Nat) : Bool :=
  (List.range' (1000 * k) (min 1000 (RH.N - 1000 * k))).all invOne

@[expose] noncomputable def clsBlk (k : Nat) : Bool :=
  (List.range' (1000 * k) (min 1000 (RH.N - 1000 * k))).all
    (repK 100 7 RH.GP RH.GIP 2 RH.CS RH.OFF RH.CI RH.E RH.P RH.L RH.K RH.S RH.SI RH.N 20000)

@[expose] noncomputable def invCovK (X : Nat) : Bool :=
  !Nat.beq (pc 100 7 X X) (pidn 100 7) || Nat.beq X (pidn 100 7) ||
    ((List.range 5775).any fun k => Nat.beq X (RH.E k)) ||
      (List.range 15400).any fun k => Nat.beq X (RH.E (5775 + k))

@[expose] noncomputable def cbP : List Nat :=
  pfilterProducts 100 7 (fun _ => true) (trPL 100 7 CCA.LR CCA.TR 3) (pidn 100 7) []

@[expose] noncomputable def cosCnt (bs : List Nat) (r : Nat) : Nat :=
  cbP.countP fun c => pnormAll 100 7 bs (pc 100 7 r c) (pinv 100 7 (pc 100 7 r c))

end CertificateChecks.KernelKGC31HS

end
