module

public import Certificates.Data.Kernel.U43Cls.Defs
public import Certificates.Kernel.U43Cls.Data
public import Certificates.Kernel.U43Mod.Checks
import CFSG.Certificates.Kernel.Common.Harness
meta import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU43Cls

open CFSG.KC.Enum CFSG.KC.U43Mod CFSG.KC.U43Cls CFSG.KS CertificateChecks.KernelU43Mod

@[expose] noncomputable def GC (c q : Nat) : Nat :=
  nIf(Nat.blt c (nat_lit 3),
    nIf(Nat.beq c (nat_lit 0), GA (nat_lit 0) q,
      nIf(Nat.beq c (nat_lit 1), GA (nat_lit 1) q, GAi (nat_lit 1) q)),
    pg (nat_lit 10) (mask (nat_lit 10)) (ET (Nat.sub c (nat_lit 3))) q)

@[expose] noncomputable def GCi (c q : Nat) : Nat :=
  nIf(Nat.blt c (nat_lit 3),
    nIf(Nat.beq c (nat_lit 0), GAi (nat_lit 0) q,
      nIf(Nat.beq c (nat_lit 1), GAi (nat_lit 1) q, GA (nat_lit 1) q)),
    pg (nat_lit 10) (mask (nat_lit 10)) (ETI (Nat.sub c (nat_lit 3))) q)

@[expose] noncomputable def X (q : Nat) : Nat := GA (nat_lit 1) (GA (nat_lit 0) q)

@[expose] noncomputable def Xi (q : Nat) : Nat := GAi (nat_lit 0) (GAi (nat_lit 1) q)

@[expose] noncomputable def Y (k q : Nat) : Nat :=
  nIf(Nat.beq k (nat_lit 0), X q, strictN (X q) X)

@[expose] noncomputable def Yi (k q : Nat) : Nat :=
  nIf(Nat.beq k (nat_lit 0), Xi q, strictN (Xi q) Xi)

@[expose] noncomputable def recC (c : Nat) : Bool :=
  cBlk RT GC GCi (GA (nat_lit 0)) Y Yi (nat_lit 19) (nat_lit 0) (nat_lit 1) (nat_lit 9)
    (nat_lit 2835) c

theorem kET : allN 16 (fun j => bAnd(permOK 820 10 (mask 10) (820 * 10) (ET j) (ETI j),
    inPU (ET j))) = true := by
  quickRfl

theorem kX : (baseEq bs (fpow X 7) (fun q => q) && !baseEq bs X (fun q => q)) = true := by
  quickRfl

#kc_each recC 0 45

end CertificateChecks.KernelU43Cls

end
