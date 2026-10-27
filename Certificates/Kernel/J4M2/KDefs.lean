module

public import Certificates.Kernel.J4Q.QT2AData
public import Certificates.Kernel.J4Q.MatData
public import Certificates.Data.Kernel.J4Q.QT2A

public section

namespace CertificateChecks.KernelJ4M2

open CFSG.KC.J4Q CFSG.KD.J4Q

@[expose] noncomputable def qaL : List Nat :=
  [QA_0, QA_1, QA_2, QA_3, QA_4, QA_5, QA_6, QA_7, QA_8, QA_9, QA_10, QA_11]

@[expose] noncomputable def pK (m : Nat) : Nat :=
  (List.range 12).foldl (fun acc j => if m.testBit j then mulJ c rm acc (getN one qaL j) else acc) one

@[expose] noncomputable def cK : Nat :=
  mulJ c rm (mulJ c rm (mulJ c rm YA YB) (mulJ c rm YA YA)) (mulJ c rm YB YB)

@[expose] noncomputable def triK (b : Nat) : Bool :=
  strictB (mulJ c rm b cK) fun x1 => strictB (mulJ c rm x1 cK) fun x2 =>
    andB (notB (Nat.beq x1 (mulJ c rm cK b)))
      (andB (notB (Nat.beq x2 (mulJ c rm cK x1))) (notB (Nat.beq (mulJ c rm x2 cK) (mulJ c rm cK x2))))

@[expose] noncomputable def commC (m : Nat) : Bool :=
  orB (Nat.beq m 0) (strictB (pK m) fun p => andB (triK p) (triK (mulJ c rm p ZM)))

@[expose] noncomputable def commBlk (k : Nat) : Bool := allR 128 fun j => commC (128 * k + j)

@[expose] noncomputable def commBlkHi (k : Nat) : Bool := commBlk (16 + k)

end CertificateChecks.KernelJ4M2

end
