module

public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LyE81.Check
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000

#kc_repo #kc_items_root CertificateChecks.KernelLyE81.MI "Certificates/Kernel/LyE81/data/mats.items"
  295752 15339459149553847746

#kc_repo #kc_items_root CertificateChecks.KernelLyE81.VI "Certificates/Kernel/LyE81/data/pts.items"
  370778 15549874229458394310

#kc_repo #kc_blocked_root CertificateChecks.KernelLyE81.OT "Certificates/Kernel/LyE81/data/orb.bin"
  6 4 65535 48114 861145146664151311

namespace CertificateChecks.KernelLyE81

@[expose] noncomputable def C : Nat := MI 0

@[expose] noncomputable def D : Nat := MI 1

@[expose] noncomputable def CD (l : Nat) : Nat := nIf(Nat.beq l 0, C, D)

@[expose] noncomputable def PK (k : Nat) : Nat := MI (Nat.add 2 k)

@[expose] noncomputable def PT (k : Nat) : Nat := MI (Nat.add 9 k)

@[expose] noncomputable def V (i : Nat) : Nat := VI i

@[expose] noncomputable def E (i k : Nat) : Nat := OT (Nat.add (Nat.mul 7 i) k)

@[expose] noncomputable def PA (i : Nat) : Nat := OT (Nat.add 15309 i)

@[expose] noncomputable def LA (i : Nat) : Nat := OT (Nat.add 17496 i)

@[expose] noncomputable def SO (i : Nat) : Nat := OT (Nat.add 19683 i)

@[expose] noncomputable def SOI (i : Nat) : Nat := OT (Nat.add 21870 i)

@[expose] noncomputable def orbC (q : Nat) : Bool :=
  CFSG.KD.LyE81.orbK PT V E PA LA (Nat.mul 81 q) 81

@[expose] noncomputable def sortC (q : Nat) : Bool :=
  CFSG.KD.LyE81.sortK V SO SOI (Nat.mul 81 q) 81

end CertificateChecks.KernelLyE81

end
