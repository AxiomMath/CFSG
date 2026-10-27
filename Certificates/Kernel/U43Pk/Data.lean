module

public import Certificates.Data.Kernel.U43Pk.Defs
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000

#kc_repo #kc_blocked_root CertificateChecks.KernelU43Pk.TT "Certificates/Kernel/U43Pk/data/pts.bin"
  4 7 340282366920938463463374607431768211455 16384 8552045406370817104

#kc_repo #kc_blocked_root CertificateChecks.KernelU43Pk.OT "Certificates/Kernel/U43Pk/data/tab.bin"
  6 4 65535 16384 15759372029861581077

namespace CertificateChecks.KernelU43Pk

@[expose] noncomputable def G (k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) 3630203748610024227 27958496020303708166 (Nat.beq k 2))
    (Bool.rec (motive := fun _ => Nat) 18879195191053582384 25364279698426691590 (Nat.beq k 0))
    (Nat.blt k 2)

@[expose] noncomputable def T (i : Nat) : Nat := TT i

@[expose] noncomputable def E (i k : Nat) : Nat := OT (Nat.add (Nat.mul 4 i) k)

@[expose] noncomputable def PA (i : Nat) : Nat := OT (Nat.add 4096 i)

@[expose] noncomputable def LA (i : Nat) : Nat := OT (Nat.add 5120 i)

@[expose] noncomputable def SO (i : Nat) : Nat := OT (Nat.add 6144 i)

@[expose] noncomputable def SOI (i : Nat) : Nat := OT (Nat.add 7168 i)

@[expose] noncomputable def u43PkBlk (q : Nat) : Bool :=
  CFSG.KD.U43Pk.blkK 4 1024 G T E PA LA SO SOI (Nat.mul 64 q) 64

@[expose] noncomputable def gensC : Bool :=
  CFSG.KC.Enum.allBlk 0 (fun k => CFSG.KD.U43Pk.rawValidK (G k)) 4

end CertificateChecks.KernelU43Pk

end
