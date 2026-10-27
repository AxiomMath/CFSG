module

public import Certificates.Kernel.EaLat318002.Data
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelEaLat318002

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.EaLat

set_option maxRecDepth 100000

@[expose] noncomputable def orbW (W : Nat → Nat) (el sz p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (Nat.shiftLeft (nat_lit 1) p)
    (fun t acc => Nat.lor acc
      (Nat.shiftLeft (nat_lit 1) (img (W (fld el (Nat.mul (nat_lit 8) t) (nat_lit 255))) p))) sz

@[expose] noncomputable def pop24 (x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.add acc (Nat.land (Nat.shiftRight x i) (nat_lit 1))) (nat_lit 24)

@[expose] noncomputable def cntW (W : Nat → Nat) (el sz : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun p acc => Nat.add acc (Nat.shiftLeft (nat_lit 1)
      (Nat.mul (nat_lit 8) (pop24 (orbW W el sz p))))) (nat_lit 24)

@[expose] noncomputable def profW (W : Nat → Nat) (f : Nat) : Bool :=
  letB (REC f) fun r => letB (fld r (nat_lit 24) (nat_lit 255)) fun sz =>
    impB (Nat.ble (nat_lit 31) sz)
      (letB (cntW W (Nat.shiftRight r (nat_lit 576)) sz) fun c =>
        letB (fld c (nat_lit 16) (nat_lit 255)) fun p2 => letB (fld c (nat_lit 32) (nat_lit 255)) fun p4 =>
          orB (andB (Nat.blt (nat_lit 0) p2) (Nat.ble p2 (nat_lit 10)))
            (orB (andB (Nat.blt (nat_lit 0) p4) (Nat.ble p4 (nat_lit 20)))
              (orB (Nat.beq p4 (nat_lit 24)) (Nat.beq (fld c (nat_lit 64) (nat_lit 255)) (nat_lit 24)))))

@[expose] noncomputable def ch318002p (k : Nat) : Bool :=
  allN (nat_lit 278) fun d => profW V (Nat.add (Nat.add (nat_lit 1) (Nat.mul (nat_lit 278) k)) d)

theorem ch318002p_zero : profW V (nat_lit 0) = true := by quickRfl

#kc_each ch318002p 0 27

theorem ch318002n_prof : notB (profW (fun _ => one (nat_lit 24)) (nat_lit 7506)) = true := by quickRfl

end CertificateChecks.KernelEaLat318002

end
