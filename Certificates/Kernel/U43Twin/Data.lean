module

public import Certificates.Data.Kernel.U43Twin.Defs
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000

#kc_repo #kc_blocked_root CertificateChecks.KernelU43Twin.OrbTT
  "Certificates/Kernel/U43Twin/data/orb_pts.bin"
  4 7 340282366920938463463374607431768211455 45360 7326517700308981885

#kc_repo #kc_blocked_root CertificateChecks.KernelU43Twin.OrbOT
  "Certificates/Kernel/U43Twin/data/orb_tab.bin"
  6 4 65535 34020 5121735856800779625

#kc_repo #kc_blocked_root CertificateChecks.KernelU43Twin.C0TT
  "Certificates/Kernel/U43Twin/data/c0_pts.bin"
  4 7 340282366920938463463374607431768211455 18432 10997845133829616725

#kc_repo #kc_blocked_root CertificateChecks.KernelU43Twin.C0OT
  "Certificates/Kernel/U43Twin/data/c0_tab.bin"
  6 4 65535 13824 2933518672071644020

#kc_repo #kc_blocked_root CertificateChecks.KernelU43Twin.T0TT
  "Certificates/Kernel/U43Twin/data/t0_pts.bin"
  4 7 340282366920938463463374607431768211455 2048 11914469953937673874

#kc_repo #kc_blocked_root CertificateChecks.KernelU43Twin.T0OT
  "Certificates/Kernel/U43Twin/data/t0_tab.bin"
  6 4 65535 1792 2299293199705932504

namespace CertificateChecks.KernelU43Twin

open CFSG.KD.U43Pk CFSG.KD.U43Twin

@[expose] noncomputable def T0K : Nat := 216278335230443568

@[expose] noncomputable def GI (k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) 2621185156243063107 432363156413677616 (Nat.beq k 0)

@[expose] noncomputable def GIi (k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) 1450248150662316867 216207966485938224 (Nat.beq k 0)

@[expose] noncomputable def GC (k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) 5932410062504096804 8072710579741525824 (Nat.beq k 0)

@[expose] noncomputable def GT (k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) 1591567482548725267 8430831960934580292 (Nat.beq k 1))
    3458767812355817520 (Nat.beq k 0)

@[expose] noncomputable def orbA (k P : Nat) : Nat := cjK (GI k) (GIi k) P

@[expose] noncomputable def OT (i : Nat) : Nat := OrbTT i

@[expose] noncomputable def OE (i k : Nat) : Nat := OrbOT (Nat.add (Nat.mul 2 i) k)

@[expose] noncomputable def OPA (i : Nat) : Nat := OrbOT (Nat.add 5670 i)

@[expose] noncomputable def OLA (i : Nat) : Nat := OrbOT (Nat.add 8505 i)

@[expose] noncomputable def OSO (i : Nat) : Nat := OrbOT (Nat.add 11340 i)

@[expose] noncomputable def OSOI (i : Nat) : Nat := OrbOT (Nat.add 14175 i)

@[expose] noncomputable def ch397503orb (q : Nat) : Bool :=
  blkAK 2 2835 orbA T0K OT OE OPA OLA OSO OSOI (Nat.mul 63 q) 63

@[expose] noncomputable def CT (i : Nat) : Nat := C0TT i

@[expose] noncomputable def CE (i k : Nat) : Nat := C0OT (Nat.add (Nat.mul 2 i) k)

@[expose] noncomputable def CPA (i : Nat) : Nat := C0OT (Nat.add 2304 i)

@[expose] noncomputable def CLA (i : Nat) : Nat := C0OT (Nat.add 3456 i)

@[expose] noncomputable def CSO (i : Nat) : Nat := C0OT (Nat.add 4608 i)

@[expose] noncomputable def CSOI (i : Nat) : Nat := C0OT (Nat.add 5760 i)

@[expose] noncomputable def ch397503c (q : Nat) : Bool :=
  blkK 2 1152 GC CT CE CPA CLA CSO CSOI (Nat.mul 64 q) 64

@[expose] noncomputable def TT (i : Nat) : Nat := T0TT i

@[expose] noncomputable def TE (i k : Nat) : Nat := T0OT (Nat.add (Nat.mul 3 i) k)

@[expose] noncomputable def TPA (i : Nat) : Nat := T0OT (Nat.add 384 i)

@[expose] noncomputable def TLA (i : Nat) : Nat := T0OT (Nat.add 512 i)

@[expose] noncomputable def TSO (i : Nat) : Nat := T0OT (Nat.add 640 i)

@[expose] noncomputable def TSOI (i : Nat) : Nat := T0OT (Nat.add 768 i)

@[expose] noncomputable def ch397503t (q : Nat) : Bool :=
  blkK 3 128 GT TT TE TPA TLA TSO TSOI (Nat.mul 64 q) 64

end CertificateChecks.KernelU43Twin

end
