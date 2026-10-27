module

public import Certificates.Kernel.SporSch.PairJ3.C81Fns
public import Certificates.Kernel.SporSch.PairJ3.C66Data

public section

namespace CertificateChecks.KernelSporSch.PJ3C66

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CertificateChecks.KernelSporSch
  CertificateChecks.KernelSporSch.PJ3C81

@[expose] noncomputable def gBase (r : Nat) : Nat := nIf(Nat.beq r 0, 10, 22)

@[expose] noncomputable def hP (r g x : Nat) : Nat := cP (Nat.add (gBase r) g) x

@[expose] noncomputable def hI (r g x : Nat) : Nat := cI (Nat.add (gBase r) g) x

@[expose] noncomputable def sI (j x : Nat) : Nat := nfp (nfX 4 (PJ3Cl.X j)) x

@[expose] noncomputable def sO (j x : Nat) : Nat := nfp (C81D.CL j) (cP 21 (nfi (C81D.CL j) x))

@[expose] noncomputable def cKey (r g : Nat) (s : Nat → Nat) : Nat :=
  keyL 6156 (fun b => hP r g (s (hI r g b))) bs

@[expose] noncomputable def fAtG (r N ng nr : Nat) (s : Nat → Nat → Nat) (K P G D R : Nat → Nat)
    (j : Nat) : Bool :=
  bIf(Nat.blt j N,
    bIf(Nat.beq (D j) 0,
      bAnd(Nat.blt (P j) nr, Nat.beq (R (P j)) j),
      bAnd(Nat.blt (P j) N, bAnd(Nat.blt (G j) ng,
      bAnd(Nat.beq (D j) (Nat.succ (D (P j))),
        Nat.beq (cKey r (G j) (s (P j))) (K j))))),
    true)

@[expose] noncomputable def fiAt (j : Nat) : Bool :=
  fAtG 0 26163 5 27 sI PJ3Cl.K C66D.FIP C66D.FIG C66D.FID C66D.RI j

@[expose] noncomputable def foAt (j : Nat) : Bool :=
  fAtG 1 20520 3 22 sO C81D.CK C66D.FOP C66D.FOG C66D.FOD C66D.RO j

@[expose] noncomputable def fiB (g r : Nat) : Bool :=
  allBlk (Nat.mul (Nat.add (Nat.mul g 6) r) (nat_lit 570)) fiAt (nat_lit 570)

@[expose] noncomputable def foB (g r : Nat) : Bool :=
  allBlk (Nat.mul (Nat.add (Nat.mul g 6) r) (nat_lit 570)) foAt (nat_lit 570)

end CertificateChecks.KernelSporSch.PJ3C66

end
