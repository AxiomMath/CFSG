module

public import Certificates.Data.Kernel.J4Q.QT2A
public import Certificates.Data.CFSGNative.J4.Data
public import Certificates.Kernel.J4Q.X0OrbData
public import Certificates.Kernel.J4Q.EtaMats
public import Certificates.Kernel.J4Q.VlData

public section

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native

@[expose] noncomputable def getLV (l : List (List Nat)) (i : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun m _ ih i => Nat.rec (motive := fun _ => List Nat) m (fun j _ => ih j) i) l i

@[expose] noncomputable def xiV : Nat := getN one XG 0

@[expose] noncomputable def xiIV : Nat := getN one XG 8

@[expose] noncomputable def cjV (T : Nat) : Nat := mulJ c rm (mulJ c rm xiV T) xiIV

@[expose] noncomputable def vValidK (t : Nat) : Bool :=
  andB (Nat.beq (mulJ c rm t t) one)
    ((fun t1 => (fun t2 => andB (andB (Nat.beq (mulJ c rm t t1) (mulJ c rm t1 t)) (Nat.beq (mulJ c rm t t2) (mulJ c rm t2 t)))
      ((fun t3 => Nat.beq (mulJ c rm (mulJ c rm (mulJ c rm (mulJ c rm t t1) t2) t3) (cjV t3)) one) (cjV t2)))
      (cjV t1)) (cjV t))

@[expose] noncomputable def tK (j e : Nat) : Nat := mulJ c rm (CFSG.KD.ETA.EF e) (getN one VLS j)

@[expose] noncomputable def vtK (v j e : Nat) : Nat := vecJ rm (vecJ rm v (CFSG.KD.ETA.EF e)) (getN one VLS j)

@[expose] noncomputable def vxK (v j e : Nat) : Nat := vecJ rm (vtK (vecJ rm v xiV) j e) xiIV

@[expose] noncomputable def W0 : Nat := v2N rootV

@[expose] noncomputable def vpK (j e : Nat) : Bool :=
  andB (Nat.beq (vtK (vtK W0 j e) j e) (vecJ rm W0 one))
    (andB (Nat.beq (vxK (vtK W0 j e) j e) (vtK (vxK W0 j e) j e)) (vValidK (tK j e)))

@[expose] noncomputable def segAt (j c' : Nat) : Bool :=
  (((List.range 64).map (Nat.add (Nat.mul 64 c'))).filter fun e => vpK j e) ==
    (getLV VLEL j).filter fun e => andB (Nat.ble (Nat.mul 64 c') e) (Nat.blt e (Nat.add (Nat.mul 64 c') 64))

@[expose] noncomputable def segK (t : Nat) : Bool :=
  allR 10 fun i => (fun j => Bool.rec (motive := fun _ => Bool) true (segAt j (Nat.div t 8)) (Nat.blt j 75))
    (Nat.add (Nat.mul 10 (Nat.mod t 8)) i)

end CertificateChecks.KernelJ4Q

end
