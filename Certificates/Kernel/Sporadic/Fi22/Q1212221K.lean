module

public import Certificates.Kernel.Sporadic.RawTreeGen
public import Certificates.Kernel.Sporadic.Fi22.X2069Final
public import Certificates.Kernel.Sporadic.Fi22.E2065T
public meta import CFSG.Sporadic.FischerOddCore.Fi22QCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Assembly.Defs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22QK

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.FischerOddCore

meta def wordA (Q : Array (Array Nat)) (w : List Int) : Array Nat :=
  w.foldr (fun z acc => compA 3510 Q[z.toNat - 1]! acc) (idA 3510)

meta def DTm : List (List Int) := [[5, 3], [6, 4]]

meta def DZm : List (List Int) :=
  [[4, 2, 1, 1], [5, 7, 6, 8], [8, 3, 9, 2, 1], [7, 8, 6, 3, 1], [7, 4, 9, 6, 1, 1]]

meta def ST : Array (Array Nat) := fi22QTwoArr ++ (DTm.map (wordA fi22QTwoArr)).toArray

meta def SZ : Array (Array Nat) := fi22QZeroArr ++ (DZm.map (wordA fi22QZeroArr)).toArray

meta def B : Array Nat := #[0, 1, 2, 3, 6, 4]

@[expose] def DT : List (List Int) := [[5, 3], [6, 4]]

@[expose] def DZ : List (List Int) :=
  [[4, 2, 1, 1], [5, 7, 6, 8], [8, 3, 9, 2, 1], [7, 8, 6, 3, 1], [7, 4, 9, 6, 1, 1]]

end CertificateChecks.KernelSpor.Fi22QK

#ks_rawtree CertificateChecks.KernelSpor.Fi22Q2T 3510 12 64 64 0 CertificateChecks.KernelSpor.Fi22QK.ST
  CertificateChecks.KernelSpor.Fi22QK.B 6 CertificateChecks.KernelSpor.Fi22QK.DT

#ks_rawtree CertificateChecks.KernelSpor.Fi22Q0T 3510 12 64 64 0 CertificateChecks.KernelSpor.Fi22QK.SZ
  CertificateChecks.KernelSpor.Fi22QK.B 9 CertificateChecks.KernelSpor.Fi22QK.DZ

namespace CertificateChecks.KernelSpor.Fi22QK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def powP (x m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pidn 3510 12) (fun _ ih => Fi22X.c x ih) m

@[expose] noncomputable def conjP (g a : Nat) : Nat := Fi22X.c g (Fi22X.c a (Fi22X.inv g))

@[expose] noncomputable def seedK (PS : Nat → Nat) (a b m : Nat) : Bool :=
  Nat.beq (PS 0) (powP (Fi22X.c (Fi22CentT.L a) (Fi22CentT.L b)) m)

@[expose] noncomputable def stepsK (PS : Nat → Nat) (st : Nat) (l : List (Nat × Nat)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun s _ ih i => bAnd(Nat.beq (PS (Nat.succ i))
      (conjP (Fi22CentT.L (Nat.add st s.1)) (PS s.2)), ih (Nat.succ i))) l

@[expose] noncomputable def inPK (PS : Nat → Nat) (kS : Nat) : Bool :=
  bAnd(allN kS (fun j => Fi22X.cn (PS j)), allN kS (fun j => Fi22X.siftP (PS j)))

@[expose] noncomputable def baseK (BP : Nat) : Bool :=
  allN 6 (fun t => Nat.beq (#[0, 1, 2, 3, 6, 4] : Array Nat)[t]! (pg 12 (mask 12) BP t))

@[expose] noncomputable def linesK (st k : Nat) : Bool :=
  allN k (fun i => strictB (Fi22CentT.L (Nat.add st i)) (fun g => bAnd(Fi22X.cn g,
    bAnd(Fi22X.cn (Fi22X.inv g), permOK 3510 12 (mask 12) (3510 * 12) g (Fi22X.inv g)))))

@[expose] noncomputable def wordImg (PS : Nat → Nat) (w : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x (fun z _ ih => pg 12 (mask 12) (PS (Nat.sub z 1)) ih) w

@[expose] noncomputable def normK (PS : Nat → Nat) (st kO nQ : Nat) (N : List (List Nat)) : Bool :=
  allN kO (fun k => strictB (Fi22CentT.L (Nat.add st k)) (fun g => allN nQ (fun j =>
    allN 6 (fun t => strictB ((#[0, 1, 2, 3, 6, 4] : Array Nat)[t]!) (fun b =>
      Nat.beq (pg 12 (mask 12) g (pg 12 (mask 12) (PS j) b))
        (wordImg PS (N.getD (Nat.add (Nat.mul k nQ) j) []) (pg 12 (mask 12) g b)))))))

@[expose] noncomputable def witK (q : Nat) (ls : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun l _ ih => strictB (Fi22CentT.L l) (fun g =>
    bAnd(Fi22X.cn g, bAnd(Bool.not (Nat.beq (Fi22X.c g q) (Fi22X.c q g)), ih)))) ls

@[expose] noncomputable def ordK (LR : Nat → Nat) : Nat :=
  ((List.range 6).map fun i => rcnt (LR i)).prod

@[expose] def NT : List (List Nat) :=
  [[1], [3], [2], [6], [5], [4], [1], [4], [3], [5, 4, 2], [2], [6, 5, 3, 1], [2], [1], [5],
    [5, 4, 3], [3], [6, 5, 3]]

@[expose] def NZ : List (List Nat) :=
  [[1], [2], [3], [4], [5], [6], [7], [8], [9], [2], [5, 8, 6, 1], [9, 8, 4, 2, 3, 1],
    [8, 9, 6, 6, 2, 1], [6, 8, 6, 5, 2], [9, 5, 6, 8, 6, 3, 2], [7, 3, 2, 6, 5], [5, 4, 7, 5, 1],
    [7, 6, 8, 3, 6], [3], [6, 5, 9, 6, 1, 1, 1], [1], [4, 3, 1, 1, 1], [8, 9, 4, 1],
    [6, 3, 1, 1, 1], [9, 5, 6, 8, 7, 1], [9, 6, 8, 6, 5, 3, 2], [9, 2, 8, 7, 7, 1], [4],
    [5, 3, 9, 3, 1], [4, 3, 1, 1, 1], [1], [8, 3, 9, 1], [6, 4, 1, 1, 1], [9, 8, 7, 5, 6, 1],
    [9, 4, 8, 5, 2], [9, 8, 6, 6, 2, 1], [5], [5, 2, 6, 8, 6], [9, 6, 8, 4, 6], [9, 6, 8, 3, 6],
    [1], [8, 6, 7, 4, 2], [9, 4, 7, 3, 1], [8, 5, 1, 1, 1], [9, 5, 1, 1, 1], [1],
    [6, 9, 7, 5, 2], [8, 8, 5], [6, 5, 6, 1, 1], [4, 1, 1], [5, 8, 1], [2, 5, 7, 2, 1],
    [9, 6, 3, 8, 5, 1], [6, 1, 1], [6], [9, 7, 4, 3, 1], [6, 3, 1, 1, 1], [4, 6, 1, 1, 1],
    [8, 7, 6, 3, 2], [1], [5, 6, 8, 6, 2, 1, 1], [7, 8, 6, 9, 3, 2, 1], [6, 5, 8, 1, 1], [5],
    [6, 8, 6, 2, 5], [8, 6, 9, 3, 6], [8, 6, 9, 4, 6], [1], [8, 7, 6, 4, 2], [7, 3, 9, 3, 1],
    [8, 5, 1, 1, 1], [9, 5, 1, 1, 1], [7], [1, 8, 1], [8, 5, 7, 6, 9, 1], [5, 9, 6, 7, 8, 1],
    [1, 6, 9, 7, 6], [7, 8, 1, 2], [9, 1, 6, 8, 5, 1], [9, 7, 7, 7, 5], [4, 8, 5, 2, 1], [8],
    [6, 8, 6, 2, 5, 1, 1], [9, 3, 2, 1], [3, 9, 7, 7, 2, 1], [8, 5, 1, 1, 1],
    [9, 5, 6, 7, 8, 3, 2, 1], [2, 9, 7, 1, 1, 1], [1], [6, 5, 9, 6, 1, 1, 1], [3],
    [6, 1, 9, 6, 5], [1], [4, 3, 1, 1, 1], [9, 8, 4, 1], [6, 3, 1, 1, 1], [8, 5, 7, 6, 9, 1],
    [9, 7, 8, 5, 7, 4, 2], [8, 6, 9, 6, 2, 1], [9], [9, 3, 1, 8], [8, 2, 6, 9, 6, 1],
    [8, 9, 4, 3, 2, 1], [9, 5, 1, 1, 1], [5, 6, 8, 1], [2, 7, 5, 4, 3, 2, 1], [8, 7, 7, 2, 2],
    [1]]

theorem seedT : seedK Fi22Q2T.S 35 36 10 = true := by quickRfl
theorem seedZ : seedK Fi22Q0T.S 0 5 4 = true := by quickRfl
theorem stT : stepsK Fi22Q2T.S 35 [(2, 0), (0, 1), (1, 1), (2, 2), (0, 3)] 0 = true := by quickRfl
theorem stZ : stepsK Fi22Q0T.S 0 [(1, 0), (2, 0), (3, 0), (4, 0), (6, 0), (8, 0), (9, 0), (11, 0)]
    0 = true := by quickRfl
theorem inPT : inPK Fi22Q2T.S 8 = true := by quickRfl
theorem inPZ : inPK Fi22Q0T.S 14 = true := by quickRfl
theorem bpT : baseK Fi22Q2T.BP = true := by quickRfl
theorem bpZ : baseK Fi22Q0T.BP = true := by quickRfl
theorem cnI : Fi22X.cn (pidn 3510 12) = true := by quickRfl
theorem odT : Nat.beq (ordK Fi22Q2T.LR) 64 = true := by quickRfl
theorem odZ : Nat.beq (ordK Fi22Q0T.LR) 8192 = true := by quickRfl
theorem pkT : allN 8 (fun j => permOK 3510 12 (mask 12) (3510 * 12) (Fi22Q2T.S j)
    (Fi22X.inv (Fi22Q2T.S j))) = true := by quickRfl
theorem pkZ : allN 14 (fun j => permOK 3510 12 (mask 12) (3510 * 12) (Fi22Q0T.S j)
    (Fi22X.inv (Fi22Q0T.S j))) = true := by quickRfl
theorem lnT : linesK 35 3 = true := by quickRfl
theorem lnZ : linesK 0 12 = true := by quickRfl
theorem nmT : normK Fi22Q2T.S 35 3 6 NT = true := by quickRfl
theorem nmZ : normK Fi22Q0T.S 0 12 9 NZ = true := by quickRfl
theorem wtT : witK (Fi22Q2T.S 0) [148, 150, 152, 154, 156, 158, 160] = true := by quickRfl
theorem wtZ : witK (Fi22Q0T.S 0)
    [108, 110, 112, 114, 116, 118, 120, 122, 124, 126, 128, 130, 132] = true := by quickRfl

end CertificateChecks.KernelSpor.Fi22QK

end
