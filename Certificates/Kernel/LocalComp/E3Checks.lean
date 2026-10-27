
module

public import Certificates.Kernel.LocalComp.E3Data
public import Certificates.Kernel.LocalComp.E3Bridge
public import Certificates.Kernel.LocalComp.Co3IdentCubeK
public import Certificates.Kernel.LocalComp.BlockGen

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.Co3Id

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Fendel CFSG.KC.Co3Bfs CFSG.KC.E3
open CFSG.KC.Child3 (offOK)
open CFSG.EvenSmallLie.SympSix.Co3Ident CertificateChecks.KernelLC

@[expose] noncomputable def GI (i : Nat) : Nat := pinvS 276 9 (mask 9) (HR.G i)

@[expose] noncomputable def l1K (j : Nat) : Bool :=
  bIf(Nat.beq (E3.TB j) 1,
    bAnd(testK P0 P4 EAP [HR.E j] E3.WS1,
      strictB (ckF E3.CI E3.MI E3.N j) (fun c => strictB (ciF E3.CS E3.OFF E3.CI E3.CV E3.MI E3.N j)
        (fun v => bAnd(Nat.blt c 3, bAnd(Nat.blt v 4608,
          Nat.beq (pc (HR.E v) (HR.E j)) (pc (HR.E (lget E3.R c)) (HR.E v))))))),
    failK P0 P4 EAP [HR.E j] E3.WS1 (E3.W1 j / 32) (E3.W1 j % 32))

@[expose] noncomputable def cdPos (p : Nat) : Bool :=
  cdPosK HR.E HR.G GI E3.TB E3.CS E3.OFF E3.CI E3.M E3.PA E3.LB E3.CC E3.CV E3.K E3.MI E3.N p

@[expose] noncomputable def cdMem (j : Nat) : Bool := cdMemK E3.TB E3.CS E3.OFF E3.CI E3.M E3.MI E3.N j

@[expose] noncomputable def l2K (x : Nat) : Bool :=
  strictB (E3.W2 x) (fun w => bIf(Nat.beq w 1000000, E3.P2.contains x,
    failK P0 P4 EAP [HR.E (lget E3.R (x / 4608)), HR.E (x % 4608)] E3.WS2 (w / 32) (w % 32)))

@[expose] noncomputable def l3K (x : Nat) : Bool :=
  strictB (lget E3.P2 (x / 4608)) (fun pr => strictB (E3.W3 x) (fun w =>
    bIf(Nat.beq w 1000000, E3.P3.contains x,
      failK P0 P4 EAP [HR.E (lget E3.R (pr / 4608)), HR.E (pr % 4608), HR.E (x % 4608)] E3.WS3
        (w / 32) (w % 32))))

@[expose] noncomputable def leafY (ℓ : Nat) : List Nat :=
  [HR.E (lget E3.R (lget E3.P2 (lget E3.P3 ℓ / 4608) / 4608)),
    HR.E (lget E3.P2 (lget E3.P3 ℓ / 4608) % 4608), HR.E (lget E3.P3 ℓ % 4608)]

@[expose] noncomputable def PSI (m : Nat) : Nat := pc P3 (pc (HR.G m) P3)

@[expose] noncomputable def TPl (ℓ i : Nat) : Nat := treeP HR.P HR.L (lget (leafY ℓ)) (E3.DD i) i

@[expose] noncomputable def leafH (ℓ : Nat) : Bool :=
  strictB (lget E3.LI ℓ) (fun i => bIf(Nat.beq (lget E3.LK ℓ) 0,
    bAnd(Nat.blt i 4608, allN 3 (fun m =>
      Nat.beq (pc (HR.E i) (PSI m)) (pc (lget (leafY ℓ) m) (HR.E i)))),
    strictB (lget E3.LY ℓ) (fun iy => bAnd(Nat.blt i 4608, bAnd(Nat.blt iy 4608,
      bAnd(allN 3 (fun m => canonK 276 9 (mask 9) (276 * 9) (lget (leafY ℓ) m)),
      bAnd(invEqK 276 9 (mask 9) (Nat.mul 276 9) (HR.E i) (pinvS 276 9 (mask 9) (HR.E i)),
      bAnd(Nat.beq (HR.E iy) (pc (HR.E i) (pc YP (pinvS 276 9 (mask 9) (HR.E i)))),
      bAnd(Nat.beq (pc (HR.E iy) (HR.E i)) (pc (HR.E i) YP),
        Nat.beq (TPl ℓ iy) YP)))))))))

@[expose] noncomputable def leafC (y : Nat) : Bool :=
  strictB (y / 128) (fun ℓ => strictB (y % 128) (fun c => bIf(Nat.beq (lget E3.LK ℓ) 0, true,
  strictB (HR.E (lget E3.LI ℓ)) (fun H => strictB (pinvS 276 9 (mask 9) H) (fun HI =>
  strictB (lget CL c) (fun k =>
  strictB (E3.LW (Nat.add (Nat.mul 6 y) 0)) (fun j0 => strictB (E3.LW (Nat.add (Nat.mul 6 y) 1)) (fun w1 =>
  strictB (E3.LW (Nat.add (Nat.mul 6 y) 2)) (fun w1' => strictB (E3.LW (Nat.add (Nat.mul 6 y) 3)) (fun w2 =>
  strictB (E3.LW (Nat.add (Nat.mul 6 y) 4)) (fun w2' => strictB (E3.LW (Nat.add (Nat.mul 6 y) 5)) (fun w3 =>
  bAnd(Nat.blt j0 4608, bAnd(Nat.blt w1 4608, bAnd(Nat.blt w1' 4608, bAnd(Nat.blt w2 4608,
  bAnd(Nat.blt w2' 4608, bAnd(Nat.blt w3 4608, bAnd(cy (HR.E j0),
  bAnd(Nat.beq (HR.E w1) (pc H (pc (HR.E j0) HI)),
  bAnd(Nat.beq (HR.E w1') (pc BCBP (pc (TPl ℓ w1) BCBP)),
  bAnd(Nat.beq (HR.E w2) (pc H (pc (HR.E w1') HI)),
  bAnd(Nat.beq (HR.E w2') (pc BCBP (pc (TPl ℓ w2) BCBP)),
  bAnd(Nat.beq (HR.E w3) (pc H (pc (HR.E w2') HI)),
  bAnd(Nat.beq (pc (HR.E w1) H) (pc H (HR.E j0)),
  bAnd(Nat.beq (pc (HR.E w2) H) (pc H (HR.E w1')),
  bAnd(Nat.beq (pc (HR.E w3) H) (pc H (HR.E w2')),
    bIf(Nat.beq (pc (pc BCBP (pc (TPl ℓ w3) BCBP)) (HR.E k)) (pc (HR.E k) (HR.E j0)), false,
      true))))))))))))))))))))))))))))

@[expose] noncomputable def ddK (j : Nat) : Bool :=
  bIf(Nat.beq j 0, Nat.beq (E3.DD 0) 0, Nat.beq (E3.DD j) (Nat.succ (E3.DD (HR.P j))))

end CertificateChecks.KernelLC.Co3Id

end
