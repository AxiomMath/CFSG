
module

public import Certificates.Kernel.SporSch.J4S.InvP
public import Certificates.Kernel.SporSch.J4S.Orbits
public import Certificates.Kernel.SporSch.J4S.FormK
public import CFSG.Sporadic.Schreier.J4SNoCompData
meta import Certificates.Kernel.SporSch.J4S.NoCData
meta import CFSG.Sporadic.Schreier.J4SNoCompData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_pairs CertificateChecks.KernelSporSch.J4RP CertificateChecks.KernelSporSch.J4NoC.repPairs
#kss_vec CertificateChecks.KernelSporSch.J4RV CFSG.Sporadic.J4Schreier.NoComp.repVecs
#kss_pairs CertificateChecks.KernelSporSch.J4CJ CertificateChecks.KernelSporSch.J4NoC.conjFlat
#kss_tree CertificateChecks.KernelSporSch.J4OW CertificateChecks.KernelSporSch.J4NoC.outW 11

namespace CertificateChecks.KernelSporSch.J4NoCK

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.C11 CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KS.SporSch.J4B
open CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4Schreier.NoComp CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.J4Eta

@[expose] noncomputable def memL (x : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun y _ ih => bIf(Nat.beq x y, true, ih)) l

@[expose] noncomputable def allL (l : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun y _ ih => bAnd(f y, ih)) l

@[expose] noncomputable def cntK (n : Nat) (f : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun a acc => Nat.add acc (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (f a))) n

@[expose] noncomputable def getL (L : List (List Nat)) (i : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun x _ ih i => Nat.rec (motive := fun _ => List Nat) x (fun m _ => ih m) i) L i

@[expose] noncomputable def RF (l : Nat) : Nat :=
  wFK c rm one A A B Bi (J4InvA.getW repWords.toList l) one
@[expose] noncomputable def RS (l : Nat) : Nat :=
  wSK c rm one A A B Bi (J4InvA.getW repWords.toList l) one

@[expose] noncomputable def etaN (n s a : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) s
    (fun j acc => CFSG.KC.Loop.strictN acc fun x =>
      nIf(Nat.testBit a j, vecJ rm x (E (Nat.add 13 j)), x)) n

@[expose] noncomputable def etaK (s a : Nat) : Nat := etaN 11 s a

@[expose] noncomputable def vneK (x y : Nat) : Bool :=
  J4InvC.anyK 112 (fun j => bne (Nat.testBit x j) (Nat.testBit y j))

@[expose] noncomputable def CP (w : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft
      (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (Nat.testBit w i))
      (Nat.mul 128 i)))
    112

@[expose] noncomputable def bilK (w : Nat) (b : Bool) : Bool :=
  bAnd(canonJ pad (CP w), bAnd(allN 112 (fun i => Nat.beq (rowJ rm (CP w) i)
      (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (Nat.testBit w i))),
    Bool.rec (motive := fun _ => Bool) (notB b) b
      (Nat.testBit (vecJ rm (vecJ rm rootBits J4FR) (CP w)) 0)))

@[expose] noncomputable def outK (l a : Nat) : Bool :=
  bIf(bIf(Nat.beq a 0, true, memL a (getL (dSets.toList) l)), true,
    CFSG.KC.J4Q.strictB (ent 11 (J4OW l) a) fun w => bAnd(Nat.blt 0 w,
      CFSG.KC.J4Q.strictB (Nat.div (Nat.sub w 1) 112) fun j =>
      CFSG.KC.J4Q.strictB (Nat.mod (Nat.sub w 1) 112) fun t =>
      bAnd(Nat.blt j 11, CFSG.KC.J4Q.strictB (getN one J4CJ (Nat.add (Nat.mul 11 l) j)) fun Y =>
        vneK (vecJ rm (etaK (Nat.shiftLeft 1 t) a) Y) (etaK (vecJ rm (Nat.shiftLeft 1 t) Y) a))))

@[expose] noncomputable def outI (k : Nat) : Bool :=
  bIf(Nat.blt k 12288, outK (Nat.succ (Nat.div k 2048)) (Nat.mod k 2048), true)

@[expose] noncomputable def kdC (d l : Nat) (w : List Int) : Bool :=
  bAnd(Nat.beq (wordAppK J4X J4XI J4Y J4YI w 1) d,
    allL dList (fun a => Nat.beq (etaK (J4RV l) (wordAppK J4X J4XI J4Y J4YI w a)) (J4RV l)))

@[expose] noncomputable def swK (w : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun a => a)
    (fun i _ ih a => CFSG.KC.Loop.strictN (ih a) fun b => appK (J4G1 i) b) w

theorem rp : allN 7 (fun l => bAnd(Nat.beq (RF l) (getN one J4RP l),
    Nat.beq (RS l) (getN one J4RP (Nat.add 7 l)))) = true := by quickRfl

theorem rv : allN 7 (fun l => Nat.beq (vecJ rm rootBits (getN one J4RP l)) (J4RV l)) = true := by
  quickRfl

theorem cj : allN 77 (fun k => Nat.beq (getN one J4CJ k)
    (mulJ c rm (mulJ c rm (getN one J4RP (Nat.add 7 (Nat.div k 11)))
      (E (Nat.add 13 (Nat.mod k 11)))) (getN one J4RP (Nat.div k 11)))) = true := by quickRfl

theorem cnt0 : Nat.beq (cntK 2048 fun a => Nat.beq (etaK (J4RV 0) a) (J4RV 0)) 2048 = true := by
  quickRfl
theorem cnt1 : Nat.beq (cntK 2048 fun a => Nat.beq (etaK (J4RV 1) a) (J4RV 1)) 2 = true := by
  quickRfl
theorem cnt2 : Nat.beq (cntK 2048 fun a => Nat.beq (etaK (J4RV 2) a) (J4RV 2)) 1 = true := by
  quickRfl
theorem cnt3 : Nat.beq (cntK 2048 fun a => Nat.beq (etaK (J4RV 3) a) (J4RV 3)) 1 = true := by
  quickRfl
theorem cnt4 : Nat.beq (cntK 2048 fun a => Nat.beq (etaK (J4RV 4) a) (J4RV 4)) 16 = true := by
  quickRfl
theorem cnt5 : Nat.beq (cntK 2048 fun a => Nat.beq (etaK (J4RV 5) a) (J4RV 5)) 512 = true := by
  quickRfl
theorem cnt6 : Nat.beq (cntK 2048 fun a => Nat.beq (etaK (J4RV 6) a) (J4RV 6)) 128 = true := by
  quickRfl

theorem nes : allN 7 (fun l => allN 2048 (fun a => bIf(Nat.beq (etaK (J4RV l) a) (J4RV l), true,
    vneK (etaK (J4RV l) a) (J4RV l)))) = true := by quickRfl

theorem rvlt :allN 7 (fun l => Nat.blt (J4RV l) (Nat.pow 2 112)) = true := by quickRfl

theorem bil2 : bilK (J4RV 2) true = true := by quickRfl
theorem bil3 : bilK (J4RV 3) false = true := by quickRfl

theorem tdx : allL dList (fun a => allL dList (fun b => memL (Nat.xor a b) dList)) = true := by
  quickRfl

theorem tdo : allN 276 (fun i => allN 276 (fun i' => bIf(Nat.beq (Nat.xor (J4O14.PT i) 1)
    (J4O14.PT i'), memL (J4O14.PT i) dList, true))) = true := by quickRfl

theorem tdc : allN 6 (fun j =>
    bAnd(J4InvC.anyK 276 (fun i => Nat.beq (J4O14.PT i) (getN 0 chainBase.toList (Nat.succ j))),
      J4InvC.anyK 276 (fun i =>
        Nat.beq (J4O14.PT i) (Nat.xor (getN 0 chainBase.toList (Nat.succ j)) 1)))) = true := by
  quickRfl

theorem tdd : allN 6 (fun l => allN 276 (fun i =>
    notB (memL (J4O14.PT i) (getL dSets.toList (Nat.succ l))))) = true := by quickRfl

theorem kd : List.rec (motive := fun _ => Bool) true
    (fun e _ ih => bAnd(kdC e.1 e.2.1 e.2.2, ih)) kdData = true := by quickRfl

end CertificateChecks.KernelSporSch.J4NoCK

#kss_slices CertificateChecks.KernelSporSch.J4NO CertificateChecks.KernelSporSch.J4NoCK.outI 256 48

end
