module

public import Certificates.Data.Kernel.WittCnt
public import Certificates.Kernel.Sporadic.M22Syl.Checks

public section

namespace CertificateChecks.KernelLC.Witt

open CFSG.KC.WCnt CertificateChecks.KernelSpor.M22Syl

@[expose] noncomputable def lev (C0 : Nat → Bool) (C1 : Nat → Nat → Bool)
    (C2 : Nat → Nat → Nat → Bool) : List ((Nat → Bool) × List Nat) :=
  [(fun x => C0 (pt x 0), L0), (fun x => C1 (pt x 0) (pt x 1), L1),
    (fun x => C2 (pt x 0) (pt x 1) (pt x 2), L2), (fun _ => true, L3), (fun _ => true, L4)]

@[expose] noncomputable def wc (Q : (Fin 22 → Fin 22) → Prop) [DecidablePred Q] (D : Nat)
    (C0 : Nat → Bool) (C1 : Nat → Nat → Bool) (C2 : Nat → Nat → Nat → Bool) : Nat :=
  ccnt 22 5 31 (ind Q D) (lev C0 C1 C2) I 0

@[expose] noncomputable def wcB (b : Nat → Bool) (D : Nat) (C0 : Nat → Bool)
    (C1 : Nat → Nat → Bool) (C2 : Nat → Nat → Nat → Bool) : Nat :=
  ccnt 22 5 31 (indB b D) (lev C0 C1 C2) I 0

end CertificateChecks.KernelLC.Witt

end
