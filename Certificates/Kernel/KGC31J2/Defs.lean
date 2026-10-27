module

public import Certificates.Kernel.KGC31J2.Data
public import CFSG.Quasithin.Vol2.KGFactC31J2Data
public import Certificates.Data.Kernel.KGC31P

public section

namespace CertificateChecks.KernelKGC31J2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.KGC31P CFSG.KC.Child3 CFSG.KC.J2Enum
open CFSG.Quasithin.KGC31.J2 CertificateChecks.KernelSporSch

@[expose] noncomputable def G (l : Int) : Nat := if l = 1 then PJ2.S 0 else PJ2.S 1

@[expose] noncomputable def pw (wd : List Int) : Nat := pword 315 9 G wd

@[expose] noncomputable def X5a : Nat := pw w5a
@[expose] noncomputable def X5b : Nat := pw w5b
@[expose] noncomputable def X7 : Nat := pw w7

@[expose] noncomputable def L5 (c : Nat) : Nat := pc 315 9 (ppw 315 9 X5a c) X5b

@[expose] noncomputable def invOne (j : Nat) : Bool :=
  permOK 315 9 (mask 9) (315 * 9) (RJ.E j) (pinv 315 9 (RJ.E j)) &&
    pactOne 315 9 5 X5a (RJ.E j) && (List.range 5).all (fun c => pactOne 315 9 5 (L5 c) (RJ.E j)) &&
    pactOne 315 9 7 X7 (RJ.E j)

@[expose] noncomputable def invBlk (k : Nat) : Bool :=
  (List.range' (200 * k) (min 200 (RJ.N - 200 * k))).all invOne

@[expose] noncomputable def fRJ (j : Nat) : Bool :=
  repK 315 9 RJ.GP RJ.GIP 2 RJ.CS RJ.OFF RJ.CI RJ.E RJ.P RJ.L RJ.K RJ.S RJ.SI RJ.N 4000 j

@[expose] noncomputable def fE0 (a : Nat) : Bool :=
  Nat.beq (blkCnt 315 9 PJ2.LR PJ2.TR PJ2.BP (pidn 315 9) (PJ2.S 0) (PJ2.S 1) a) (lget E0 a)

end CertificateChecks.KernelKGC31J2

end
