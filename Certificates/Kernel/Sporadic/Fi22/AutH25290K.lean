module

public import Certificates.Kernel.Sporadic.Fi22.AutH25290D
public import Certificates.Kernel.Sporadic.Fi22.X2069Final
public import Certificates.Kernel.Sporadic.Fi22.Ext2073
public import Certificates.Kernel.Sporadic.Fi22.G3147
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.AH25

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CertificateChecks.KernelSpor

@[expose] noncomputable def ev (P x : Nat) : Nat := pg 12 (mask 12) P x

@[expose] noncomputable def idP : Nat := pidn 3510 12

@[expose] noncomputable def isP (p : Nat) : Bool :=
  Fi22X.cn p && permOK 3510 12 (mask 12) (3510 * 12) p (Fi22X.inv p)

@[expose] noncomputable def bitB (m i : Nat) : Bool := Nat.blt 0 (Nat.land m (Nat.shiftLeft 1 i))

@[expose] noncomputable def L10 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

@[expose] noncomputable def ptL (Bf : Nat → Nat) (m : Nat) (l : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x
    (fun i _ acc => Bool.rec (motive := fun _ => Nat) acc (ev (Bf i) acc) (bitB m i)) l

@[expose] noncomputable def phL (Bf : Nat → Nat) (m : Nat) (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) idP
    (fun i _ acc => Bool.rec (motive := fun _ => Nat) acc (Fi22X.c (Bf i) acc) (bitB m i)) l

@[expose] noncomputable def wl (Wn q : Nat) : Nat := pg 11 (mask 11) Wn q

@[expose] noncomputable def tl (Tn j : Nat) : Nat := pg 10 (mask 10) Tn j

@[expose] noncomputable def basisOK (b : Nat) : Bool :=
  isP b && Nat.beq (Fi22X.c b b) idP && Fi22X.siftP b

@[expose] noncomputable def injOK (Bf : Nat → Nat) (Wn m : Nat) : Bool :=
  Nat.beq (wl Wn (ptL Bf m L10 0)) m

@[expose] noncomputable def covOK (Bf : Nat → Nat) (Wn q : Nat) : Bool :=
  strictB (wl Wn q) fun l =>
    Bool.rec (motive := fun _ => Bool)
      (strictB (Nat.sub l 1024) fun m =>
        Nat.blt 0 m && Nat.blt m 1024 && Nat.beq (ptL Bf m L10 q) q)
      (Nat.beq (ptL Bf l L10 0) q) (Nat.blt l 1024)

@[expose] noncomputable def baseOK (Bf R : Nat → Nat) (Z Tm j : Nat) : Bool :=
  strictB (phL Bf (tl Tm j) L10) fun v => Nat.beq (R j) (Fi22X.c v (Fi22X.c Z v))

@[expose] noncomputable def ruleOK (R : Nat → Nat) (Tr r : Nat) : Bool :=
  strictB (tl Tr (Nat.mul 2 r)) fun a => strictB (tl Tr (Nat.add (Nat.mul 2 r) 1)) fun b =>
    Nat.blt a (Nat.add 7 r) && Nat.blt b (Nat.add 7 r) &&
      Nat.beq (R (Nat.add 7 r)) (Fi22X.c (R a) (R b))

@[expose] noncomputable def nR : Nat := tl (AH25T 2) 2

@[expose] noncomputable def eR (k : Nat) : Nat := tl (AH25T 2) k

theorem okB : allN 10 (fun i => basisOK (AH25B i)) = true := by quickRfl

theorem okC : allN 10 (fun i => allN i fun j =>
    Nat.beq (Fi22X.c (AH25B i) (AH25B j)) (Fi22X.c (AH25B j) (AH25B i))) = true := by quickRfl

theorem okZ : isP Fi22E2073.E = true := by quickRfl

theorem okInj : allN 1024 (fun m => injOK AH25B (AH25W 0) m) = true := by quickRfl

theorem okCov : allN 3510 (fun q => covOK AH25B (AH25W 0) q) = true := by quickRfl

theorem okBase : allN 7 (fun j => baseOK AH25B AH25R Fi22E2073.E (AH25T 1) j) = true := by
  quickRfl

theorem okRules : strictB nR (fun n => allN n fun r => ruleOK AH25R (AH25T 0) r) = true := by
  quickRfl

theorem okEnd : (Nat.blt (eR 0) (Nat.add 7 nR) && Nat.blt (eR 1) (Nat.add 7 nR) &&
    Nat.beq (AH25R (eR 0)) (Fi22CGT.F 0) && Nat.beq (AH25R (eR 1)) (Fi22CGT.F 1)) = true := by
  quickRfl

end CertificateChecks.KernelSpor.AH25

end
