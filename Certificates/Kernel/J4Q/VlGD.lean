module

public import Certificates.Kernel.J4Q.VlK
import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.VG

@[expose] def root : Bool × Nat × Nat × Nat := (true, CFSG.KD.J4Q.one, 0, 0)

@[expose] noncomputable def cj (T : Nat) : Nat :=
  CFSG.KC.J4Q.mulJ CFSG.KD.J4Q.c CFSG.KD.J4Q.rm
    (CFSG.KC.J4Q.mulJ CFSG.KD.J4Q.c CFSG.KD.J4Q.rm (CFSG.KC.J4Q.getN CFSG.KD.J4Q.one CFSG.KD.J4Q.XG 0) T)
    (CFSG.KC.J4Q.getN CFSG.KD.J4Q.one CFSG.KD.J4Q.XG 8)

@[expose] noncomputable def cjPow (n t : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) t (fun _ x => cj x) n

@[expose] noncomputable def letter (w : List Nat) (o : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) CFSG.KD.J4Q.one
    (fun i _ => cjPow i (CertificateChecks.KernelJ4Q.tK (CFSG.KC.J4Q.getN 0 w 0)
      (CFSG.KC.J4Q.getN 0 w 1))) o

@[expose] noncomputable def run (w : List Nat) (k : Nat) (s : Bool × Nat × Nat × Nat) :
    Bool × Nat × Nat × Nat :=
  (true, CFSG.KC.J4Q.mulJ CFSG.KD.J4Q.c CFSG.KD.J4Q.rm s.2.1
    (letter w (Nat.land (Nat.shiftRight k 20) 1048575)), 0, 0)

end CFSG.KD.VG

end

#kc_chain CFSG.KD.VG CFSG.KD.VG.run "vlgd.plan.txt" 70676 12995498387221308216

#kc_select CFSG.KD.VG GDF X 2112
