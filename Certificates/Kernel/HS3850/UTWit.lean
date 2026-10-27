module

public import Certificates.Kernel.HS3850.UTDefs
public import Certificates.Kernel.LocalQT.SV.C4126T
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.ConjOrb
public import Certificates.Data.Kernel.PkPow

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHS3850.UT

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.HSAutN CFSG.KD.LQT.C4126 CFSG.KC.InvTabK
open CFSG.Quasithin.B45Exc.HS CFSG.Quasithin.B45Exc.Tab

@[expose] noncomputable def L0 : List Nat := [HS.F 0, HS.F 1]

@[expose] noncomputable def LI0 : List Nat := [HSI 0, HSI 1]

@[expose] noncomputable def pwK (e Y : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) idn (fun _ acc => pc Y acc) e

@[expose] noncomputable def regL (B : List Nat) (G GI : Nat) : List Nat :=
  B.map xE ++ B.map fun i => pc (pc G (xE i)) GI

@[expose] noncomputable def regLI (B : List Nat) (G GI : Nat) : List Nat :=
  B.map xE ++ B.map fun i => pc G (pc (xE i) GI)

@[expose] noncomputable def genK (w : GenWit) : Bool :=
  strictB (wordP1 3850 12 L0 LI0 w.g) fun G => strictB (wordP2 3850 12 L0 LI0 w.g) fun GI =>
    w.basis.all (fun i => Nat.blt i 191) && Nat.beq w.ws.length 2 &&
      (List.zip w.ws L0).all fun p =>
        Nat.beq (wordP1 3850 12 (regL w.basis G GI) (regLI w.basis G GI) p.1) p.2

@[expose] noncomputable def dimK (w : DimWit) : Bool :=
  strictB (wordP1 3850 12 L0 LI0 w.g) fun G => strictB (wordP2 3850 12 L0 LI0 w.g) fun GI =>
    strictB (pc (pc (pc G (xE w.e)) GI) (xE w.e')) fun Y =>
    Nat.blt w.d 191 && Nat.blt w.c 191 && Nat.blt w.e 191 && Nat.blt w.e' 191 &&
      Nat.beq (FX w.d) 46 && Nat.beq (FX w.c) 350 &&
      (Nat.beq (FX w.e) 170 || Nat.beq (FX w.e) 30) &&
      (Nat.beq (FX w.e') 170 || Nat.beq (FX w.e') 30) &&
      Nat.beq (pc G (xE w.c)) (pc (xE w.c) G) && Nat.beq (pwK 5 Y) idn && !(Nat.beq Y idn)

theorem ecanon : allN 1024 (fun i => canonK 3850 12 (mask 12) (3850 * 12) (SY.E i)) = true := by
  quickRfl

theorem gcanon : allN 2 (fun k => canonK 3850 12 (mask 12) (3850 * 12) (HS.F k) &&
    canonK 3850 12 (mask 12) (3850 * 12) (HSI k)) = true := by quickRfl

theorem gen : hsGenWits.all genK = true := by quickRfl

theorem dim : hsDimWits.all dimK = true := by quickRfl

end CertificateChecks.KernelHS3850.UT

end
