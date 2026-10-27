module

public import Certificates.Kernel.J4Q.OrbBase
public import Certificates.Kernel.J4Q.Mat
public import Certificates.Kernel.J4Q.AllN
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Data.J4Seven.Native
public meta import Certificates.Data.J4Seven.Native
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q.C4219

open CFSG.Quasithin.J4Seven

meta def atM : Array Nat := (Array.range 2048).map actX

end CertificateChecks.KernelJ4Q.C4219

#ks_perm CertificateChecks.KernelJ4Q.C4219.AT 11 CertificateChecks.KernelJ4Q.C4219.atM

namespace CertificateChecks.KernelJ4Q.C4219

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2
  CFSG.Quasithin.J4Seven CertificateChecks.KernelJ4Q

@[expose] noncomputable def S7 : Nat := powJ c rm one L2 3

@[expose] noncomputable def S7R : List Nat := rowsOfJ rm S7

@[expose] noncomputable def memK (x : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun y _ ih => orB (Nat.beq x y) ih) l

@[expose] noncomputable def allK (f : Nat → Bool) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun y _ ih => andB (f y) ih) l

@[expose] noncomputable def fixK (rs : List Nat) (x : Nat) : Bool := Nat.beq (vecLJ x rs) x

@[expose] noncomputable def SFK : List Nat :=
  [v2N (sevenFix.getD 0 rootV), v2N (sevenFix.getD 1 rootV), v2N (sevenFix.getD 2 rootV),
    v2N (sevenFix.getD 3 rootV)]

@[expose] noncomputable def fixChunk (i : Nat) : Bool :=
  allK (fun e => orB (notB (fixK S7R (Nat.land e rm))) (memK (Nat.land e rm) SFK)) (CH5.getD i [])

@[expose] noncomputable def itK (k c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) c (fun _ ih => CFSG.KC.Enum.pg 11 (CFSG.KS.mask 11) AT ih) k

@[expose] noncomputable def cntN (n : Nat) (f : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun c ih => CFSG.KC.Loop.strictN ih fun a => Bool.rec (motive := fun _ => Nat) a (Nat.succ a) (f c)) n

@[expose] noncomputable def cntK (k : Nat) : Nat :=
  cntN 2048 fun c => Nat.beq (Nat.xor (Nat.xor (itK (k * 3) c) (itK k c)) c) 0

@[expose] noncomputable def cntsK (k : Nat) : Nat :=
  cntN 2048 fun c => Nat.beq (Nat.xor (Nat.xor (itK (k * 3) c) (itK (k * 2) c)) c) 0

end CertificateChecks.KernelJ4Q.C4219

#j4q_all CertificateChecks.KernelJ4Q.C4219.ch4219f CertificateChecks.KernelJ4Q.C4219.fixChunk 15

namespace CertificateChecks.KernelJ4Q.C4219

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2
  CFSG.Quasithin.J4Seven CertificateChecks.KernelJ4Q

theorem ch4219len : Nat.beq CH5.length 15 = true := by quickRfl

theorem ch4219o : andB (Nat.beq (powJ c rm one S7 7) one) (notB (Nat.beq S7 one)) = true := by
  quickRfl

theorem ch4219r : orB (notB (fixK S7R (repK 5))) (memK (repK 5) SFK) = true := by quickRfl

theorem ch4219s : allK (fun y => andB (fixK S7R y) (memK y (vptsK rm (repK 5) CH5.flatten))) SFK =
    true := by quickRfl

theorem ch4219a : CFSG.KC.Enum.allN 2048 (fun c => andB (Nat.blt (CFSG.KC.Enum.pg 11
    (CFSG.KS.mask 11) AT c) 2048) (Nat.beq (CFSG.KC.Enum.pg 11 (CFSG.KS.mask 11) AT c)
      (actX c))) = true := by quickRfl

theorem ch4219c : CFSG.KC.Enum.allN 6 (fun k => notB (Nat.beq (cntK (Nat.succ k)) (cntsK (Nat.succ k)))) =
    true := by quickRfl

theorem ch4219neg1 : notB (Nat.beq (powJ c rm one L2 7) one) = true := by quickRfl

theorem ch4219neg2 : notB (allK (fun y => andB (fixK S7R y) (memK y [])) SFK) = true := by quickRfl

theorem ch4219neg3 : notB (allK (fun y => fixK (rowsOfJ rm L2) y) SFK) = true := by quickRfl

end CertificateChecks.KernelJ4Q.C4219

end
