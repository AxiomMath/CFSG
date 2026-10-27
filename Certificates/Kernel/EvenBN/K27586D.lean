module

public import Certificates.Kernel.EvenBN.Lists
public import Certificates.Data.Kernel.EvenBN.BaseTw
public import Certificates.Data.TitsAschbacherNLocal

public section

namespace CertificateChecks.KernelEvenBN.NLoc

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CertificateChecks.KernelSpor
open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native
open Certificates.TitsAschbacherParrott Certificates.TitsAschbacherNLocal

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 1755 11 (mask 11) p q

@[expose] noncomputable def Y : Nat := wP TitsN.S yWord

@[expose] noncomputable def YI : Nat := pinvS 1755 11 (mask 11) Y

@[expose] noncomputable def VQ (i : Nat) : Nat := pc (pc Pi (V i)) PiI

@[expose] noncomputable def W (m j : Nat) : Nat := pc (FL.getD m 0) (V j)

@[expose] def jL : List Nat := [7, 9, 10, 11, 12]

@[expose] def uL : List Nat := [0, 8, 16, 24]

@[expose] noncomputable def cT (gx : Nat → Nat) : Bool :=
  !([10, 11, 12].all fun i => baseComm TitsK.BP 5 gx (pgR (V i))) ||
    jL.all fun j => uL.any fun m => baseTw TitsK.BP 5 gx (pgR (V j)) (pgR (W m j))

@[expose] noncomputable def cTP (gx : Nat → Nat) : Bool :=
  !([10, 11, 12].all fun i => baseTw TitsK.BP 5 gx (pgR (VQ i)) (pgR (V i))) ||
    jL.all fun j => uL.any fun m => baseTw TitsK.BP 5 gx (pgR (VQ j)) (pgR (W m j))

@[expose] noncomputable def PK (t0 t1 t2 t3 t4 : Nat) : Bool :=
  cT (gptR t0 t1 t2 t3 t4) && cTP (gptR t0 t1 t2 t3 t4)

@[expose] def pK (k : Array Nat) : Bool := cTest k && cTest (compA 1755 k CFSG.Quasithin.titsPiArr)

@[expose] noncomputable def PK' (t0 t1 t2 t3 t4 : Nat) : Bool :=
  Bool.rec (pK (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))) true (PK t0 t1 t2 t3 t4)

@[expose] noncomputable def b0 : Nat := pg 11 (mask 11) TitsS.BP 0

@[expose] noncomputable def out0 (q : Nat) : Bool :=
  Nat.ble (rcnt (TitsS.LR 0)) (rpos 11 (mask 11) (1755 * 11) (TitsS.LR 0) q)

@[expose] noncomputable def l0 (gx : Nat → Nat) : Bool :=
  out0 (pg 11 (mask 11) YI (gx (pg 11 (mask 11) Y b0))) &&
    out0 (pg 11 (mask 11) YI (gx (pg 11 (mask 11) Y (pg 11 (mask 11) PiI b0))))

@[expose] noncomputable def PS (t0 t1 t2 t3 t4 : Nat) : Bool :=
  ktKB TitsK.LR TitsK.TRI TitsK.BP TitsS.BP t0 t1 t2 t3 t4 ||
    (l0 (gptR t0 t1 t2 t3 t4) && l0 (fun q => gptR t0 t1 t2 t3 t4 (pg 11 (mask 11) Pi q)))

@[expose] def pS (s : Array Nat) : Bool :=
  tTest (invCand 1755 (yArr ())) (yArr ()) s &&
    tTest (invCand 1755 (yArr ())) (yArr ()) (compA 1755 s CFSG.Quasithin.titsPiArr)

@[expose] noncomputable def PS' (t0 t1 t2 t3 t4 : Nat) : Bool :=
  Bool.rec (pS (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))) true (PS t0 t1 t2 t3 t4)

@[expose] noncomputable def QK : Nat → Nat → Nat → Nat → Nat → Nat → Bool :=
  survQ (fun t0 t1 t2 t3 t4 => !PK' t0 t1 t2 t3 t4) 0

@[expose] noncomputable def QS : Nat → Nat → Nat → Nat → Nat → Nat → Bool :=
  survQ (fun t0 t1 t2 t3 t4 => !PS' t0 t1 t2 t3 t4) 0

end CertificateChecks.KernelEvenBN.NLoc

end
