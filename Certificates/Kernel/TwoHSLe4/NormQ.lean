module

public import Certificates.Kernel.TwoHSLe4.NormP

public section

namespace CertificateChecks.KernelTwoHSLe4.NormP

open CFSG.EvenSporadicStandard.TwoHS CFSG.KC.F4M3B CertificateChecks.KernelTwoHSLe4.Norm

variable {α : Type}

@[expose] def inA (o : Ops α) (h : ℕ → α) : Q4 α :=
  ⟨(h 0, zr o), (h 1, zr o), (h 2, zr o), (h 3, zr o), (h 4, zr o), (h 5, zr o), (h 6, zr o),
   (h 7, zr o), (h 8, zr o), (h 9, zr o), (h 10, zr o), (h 11, zr o), (h 12, zr o),
   (h 13, zr o), (h 14, zr o), (h 15, zr o)⟩

@[expose] def eqLE (o : Ops α) (p q : α × α) : α := bnot o (o.x p.1 q.1)

@[expose] def eqL (o : Ops α) (A B : Q4 α) : α :=
  o.a (eqLE o A.e00 B.e00) (o.a (eqLE o A.e01 B.e01) (o.a (eqLE o A.e02 B.e02)
  (o.a (eqLE o A.e03 B.e03) (o.a (eqLE o A.e10 B.e10) (o.a (eqLE o A.e11 B.e11)
  (o.a (eqLE o A.e12 B.e12) (o.a (eqLE o A.e13 B.e13) (o.a (eqLE o A.e20 B.e20)
  (o.a (eqLE o A.e21 B.e21) (o.a (eqLE o A.e22 B.e22) (o.a (eqLE o A.e23 B.e23)
  (o.a (eqLE o A.e30 B.e30) (o.a (eqLE o A.e31 B.e31) (o.a (eqLE o A.e32 B.e32)
  (eqLE o A.e33 B.e33)))))))))))))))

@[expose] def finA (o : Ops α) (N : List R4) (A : Q4 α) (P Q : List (Q4 α)) : α :=
  bor o (bnot o (o.a (allA o (P.map fun p => anyA o (Q.map fun q => eqL o p q)))
      (allA o (Q.map fun q => anyA o (P.map fun p => eqL o p q)))))
    (anyA o (N.map fun c => eqM o A (cQ o c)))

@[expose] def chkA (o : Ops α) (L N : List R4) (h : ℕ → α) : α :=
  bindQ o (inA o h) fun A =>
    bindL o (L.map fun s => mulM o A (cQ o s)) fun P =>
      bindL o (L.map fun s => mulM o (cQ o s) A) fun Q => finA o N A P Q

@[expose] noncomputable def chkAG (L N : List R4) : Bool :=
  frcL L fun L' => frcL N fun N' =>
    frc (Nat.sub (Nat.pow 2 (Nat.pow 2 16)) 1) fun t =>
      Nat.beq (chkA (natOps t) L' N' fun j => pln j 16) t

@[expose] noncomputable def chkAN : Bool := chkAG (SL.map R4.mod2) nvL

end CertificateChecks.KernelTwoHSLe4.NormP

end
