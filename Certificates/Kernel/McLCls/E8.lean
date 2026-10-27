module

public import Certificates.Kernel.McLCls.Checks
public import Certificates.Kernel.McLCls.Enum
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMcLCls

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.M305 CertificateChecks.KernelLC.McLC

@[expose] noncomputable def e8At (N : Nat) (T : Nat → Nat) : Bool :=
  allN N (fun i => bIf(Nat.beq i 0, true, m305e8 (T i) (MC.F 4) IE.N IE.T))

theorem e8a : e8At R5E.N R5E.T = true := by
  quickRfl

theorem e8b : e8At R7E.N R7E.T = true := by
  quickRfl

theorem e8c : e8At P3E.N P3E.T = true := by
  quickRfl

theorem e8gens : bAnd(Nat.beq (R5E.G 0) (m305word hL (nthW xWd 0)),
    bAnd(Nat.beq (R7E.G 0) (m305word hL (nthW xWd 1)),
    bAnd(Nat.beq (P3E.G 0) (m305word hL (nthW xWd 2)),
    bAnd(Nat.beq (P3E.G 1) (m305word hL (nthW xWd 3)),
    bAnd(Nat.beq (IE.G 0) (MC.F 5), Nat.beq (IE.G 1) (MC.F 6)))))) = true := by
  quickRfl

end CertificateChecks.KernelMcLCls

end
