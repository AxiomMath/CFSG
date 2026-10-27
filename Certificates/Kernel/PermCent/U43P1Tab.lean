module

public import Certificates.Kernel.PermCent.U43P1In
public import Certificates.Kernel.PermCent.U43P1M1a
public import Certificates.Kernel.PermCent.U43P1M1b
public import Certificates.Kernel.PermCent.U43P1Fa
public import Certificates.Kernel.PermCent.U43P1Fb
public import Certificates.Kernel.PermCent.U43P1Ia
public import Certificates.Kernel.PermCent.U43P1T

public section

namespace CertificateChecks.KernelPermCent.U43P1

@[expose] noncomputable def clsT (c : ℕ) : ℕ → ℕ :=
  cond (Nat.beq c 0) CIn.T (cond (Nat.beq c 1) CM1a.T (cond (Nat.beq c 2) CM1b.T
    (cond (Nat.beq c 3) CFa.T (cond (Nat.beq c 4) CFb.T CIa.T))))

@[expose] noncomputable def clsN (c : ℕ) : ℕ :=
  cond (Nat.beq c 0) CIn.N (cond (Nat.beq c 1) CM1a.N (cond (Nat.beq c 2) CM1b.N
    (cond (Nat.beq c 3) CFa.N (cond (Nat.beq c 4) CFb.N CIa.N))))

@[expose] noncomputable def clsR (c : ℕ) : ℕ :=
  cond (Nat.beq c 0) CIn.r0 (cond (Nat.beq c 1) CM1a.r0 (cond (Nat.beq c 2) CM1b.r0
    (cond (Nat.beq c 3) CFa.r0 (cond (Nat.beq c 4) CFb.r0 CIa.r0))))

@[expose] noncomputable def a6T (c : ℕ) : ℕ → ℕ := cond (Nat.beq c 0) CM1a.T CIa.T

@[expose] noncomputable def a6N (c : ℕ) : ℕ := cond (Nat.beq c 0) CM1a.N CIa.N

@[expose] noncomputable def tM1aG (k : ℕ) : ℕ → ℕ :=
  cond (Nat.beq k 0) TM0.G (cond (Nat.beq k 1) TM1.G (cond (Nat.beq k 2) TM2.G
    (cond (Nat.beq k 3) TM3.G (cond (Nat.beq k 4) TM4.G TM5.G))))

@[expose] noncomputable def tM1aT (k : ℕ) : ℕ → ℕ :=
  cond (Nat.beq k 0) TM0.T (cond (Nat.beq k 1) TM1.T (cond (Nat.beq k 2) TM2.T
    (cond (Nat.beq k 3) TM3.T (cond (Nat.beq k 4) TM4.T TM5.T))))

@[expose] noncomputable def tIaG (k : ℕ) : ℕ → ℕ :=
  cond (Nat.beq k 0) TI0.G (cond (Nat.beq k 1) TI1.G (cond (Nat.beq k 2) TI2.G TI3.G))

@[expose] noncomputable def tIaT (k : ℕ) : ℕ → ℕ :=
  cond (Nat.beq k 0) TI0.T (cond (Nat.beq k 1) TI1.T (cond (Nat.beq k 2) TI2.T TI3.T))

end CertificateChecks.KernelPermCent.U43P1

end
