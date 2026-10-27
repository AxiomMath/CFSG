module

public import Certificates.Kernel.Fi22S0.Each
public import Certificates.Kernel.Fi22S0.Strs
public import Certificates.Data.Kernel.LyS0.Check
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22S0

open CFSG.KD.LyS0

@[expose] noncomputable def opsRec (k : Nat) : Nat := tb (nat_lit 0) k

@[expose] noncomputable def parRec (k : Nat) : Nat :=
  nIf(Nat.beq (Nat.land k (nat_lit 1)) (nat_lit 0), pp (Nat.shiftRight k (nat_lit 1)),
    pj (Nat.shiftRight k (nat_lit 1)))

@[expose] noncomputable def LRec (k : Nat) : Nat :=
  lt (Nat.div k (nat_lit 19683)) (Nat.mod k (nat_lit 19683))

theorem ch131101pOps : parseOK opsRec OS.chars 1134 = true := by quickRfl

theorem ch131101pPar : parseOK parRec PS.chars 39366 = true := by quickRfl

end CertificateChecks.KernelFi22S0

end
