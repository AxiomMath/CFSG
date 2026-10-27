module

public import Certificates.Kernel.HS3850.InnerKData
public import Certificates.Kernel.LocalQT.HSAut.D4146

public section

namespace CertificateChecks.KernelHS3850

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.HSAutN CFSG.KD.LQT.HN
open CFSG.EvenSporadicStandard.HSStd.Zassenhaus.InnerCert

@[expose] noncomputable def GI1 : Nat := pinvS 3850 12 (mask 12) (IT.F 0)

@[expose] noncomputable def kCode (Y c : Nat) : Nat :=
  nIf(Nat.beq c (nat_lit 0), IT.F 0, nIf(Nat.beq c (nat_lit 1), GI1, Y))

@[expose] noncomputable def kW (Y : Nat) (w : List Nat) : Nat :=
  w.foldr (fun c acc => pc (kCode Y c) acc) idn

@[expose] noncomputable def p5K (t : Nat) : Nat := pc (pc (pc t t) (pc t t)) t

@[expose] noncomputable def patK (Y : Nat) : Bool :=
  filtV.all fun p => Bool.beq (Nat.beq (kW Y p.1) idn) p.2

@[expose] noncomputable def hpK : Nat → Nat
  | 0 => idn
  | k + 1 => pc (IT.F 2) (hpK k)

@[expose] noncomputable def ptI (i : Nat) : Bool :=
  strictB (A.T i) (fun t =>
    bAnd(bIf(bAnd(Nat.beq (p5K t) idn, (Nat.beq t idn).not),
        bAnd(Nat.blt (OW i) (nat_lit 7680),
          Nat.beq (pc (A.T (OW i)) t) (pc (IT.F 0) (A.T (OW i)))), true),
      bIf(patK t,
        bAnd(Nat.blt (FW i / 4) (nat_lit 20),
          Nat.beq (pc (hpK (FW i / 4)) t) (pc (IT.F (3 + FW i % 4)) (hpK (FW i / 4)))), true)))

@[expose] noncomputable def ckI (s : Nat) : Bool :=
  allN 32 (fun d => strictB (Nat.add (Nat.mul s (nat_lit 32)) d) (fun i =>
    bIf(Nat.blt i (nat_lit 7680), ptI i, true)))

end CertificateChecks.KernelHS3850

end
