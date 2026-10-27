module

public import Certificates.Data.Kernel.SortTree
public import Certificates.Kernel.MonsterB.Orb3132Act
public import Certificates.Kernel.MonsterB.Orb3132DS
public import Certificates.Kernel.MonsterB.Orb3132D39
public import Certificates.Kernel.MonsterB.Orb3132D35a
public import Certificates.Kernel.MonsterB.Orb3132D35b
public import Certificates.Kernel.MonsterB.Orb3132D35c

public section

namespace CertificateChecks.Orb3132

open CFSG.KLie.CT CFSG.KC.SortTree

@[expose] noncomputable def rec60 : Nat → Nat := recT R60 6 44
@[expose] noncomputable def rec32 : Nat → Nat := recT R32 6 48
@[expose] noncomputable def rec39 : Nat → Nat := recT R39 6 52

@[expose] noncomputable def B35 (b : Nat) : Nat :=
  nIf(Nat.blt b (nat_lit 4158), R35a b,
    nIf(Nat.blt b (nat_lit 8316), R35b (Nat.sub b (nat_lit 4158)), R35c (Nat.sub b (nat_lit 8316))))

@[expose] noncomputable def rec35 : Nat → Nat := recT B35 6 52

@[expose] noncomputable def chunk (r : Nat) (rec : Nat → Nat) (n wl wp c : Nat) : Bool :=
  chunkOK act 17 (fun _ => true) r rec n 22 wl wp 2048 c

@[expose] noncomputable def slice (r : Nat) (rec : Nat → Nat) (n wl wp o m : Nat) : Bool :=
  allN m fun j => chunk r rec n wl wp (Nat.add o j)

end CertificateChecks.Orb3132

end
