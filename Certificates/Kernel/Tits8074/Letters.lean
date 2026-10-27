module

public import Certificates.Kernel.Tits8074.Data
public import Certificates.Data.Kernel.Tits8074
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelT8074

open CFSG.KC.Tits8074

@[expose] noncomputable def lw (w : List Nat) : Bool := allL w fun c => Nat.blt c 24

@[expose] noncomputable def lx (E : List (List Nat × Nat)) : Bool := allL E fun e => lw e.1

@[expose] noncomputable def lws (W : List (List Nat)) : Bool := allL W lw

theorem xs : bAnd(lx x0, bAnd(lx x1, bAnd(lx x2, bAnd(lx x3, bAnd(lx x4, bAnd(lx x5, bAnd(lx x6,
    bAnd(lx x7, bAnd(lx x8, bAnd(lx x9, bAnd(lx x10, bAnd(lx x11, bAnd(lx x12, bAnd(lx x13,
    bAnd(lx x14, lx x15))))))))))))))) = true := by
  quickRfl

theorem ws : bAnd(lw aw, bAnd(lws r2, bAnd(lws r3, bAnd(lws r4, bAnd(lws r5, bAnd(lws r6,
    bAnd(lws hw, bAnd(lws tg, bAnd(lws cw, bAnd(Nat.blt zc 24, Nat.blt sc 24)))))))))) = true := by
  quickRfl

end CertificateChecks.KernelT8074

end
