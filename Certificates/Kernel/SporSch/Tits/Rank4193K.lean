module

public import CFSG.Quasithin.EmptyFaithful.F112SInputs
public import Certificates.Kernel.EvenBN.K27580D
public import Certificates.Kernel.Misc.Tits.Pi7092
public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.Quasithin.EmptyFaithful.F112SInputs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Rank4193

meta def invsM : Array (Array Nat) := CFSG.Quasithin.F112S.invs

meta def rowsM : Array (Array Nat) := CFSG.Quasithin.F112S.prodTab

end CertificateChecks.KernelSporSch.Rank4193

#kmisc_packarrs CertificateChecks.KernelSporSch.Rank4193.IT
  CertificateChecks.KernelSporSch.Rank4193.invsM 11
#kmisc_packarrs CertificateChecks.KernelSporSch.Rank4193.PT
  CertificateChecks.KernelSporSch.Rank4193.rowsM 8

public section

namespace CertificateChecks.KernelSporSch.Rank4193

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CertificateChecks.KernelSpor
open CertificateChecks.KernelEvenBN

@[expose] noncomputable def mulT (i j : Nat) : Nat := pg 8 (mask 8) (PT i) j

@[expose] noncomputable def forceL (l : List Nat) (k : List Nat → Bool) : Bool :=
  List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k [])
    (fun x _ ih k => strictB x (fun x' => ih (fun xs => k (x' :: xs)))) l k

@[expose] noncomputable def memB (y : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ ih => bIf(Nat.beq y x, true, ih)) l

@[expose] noncomputable def allR (f : Nat → Bool) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => bAnd(f x, ih)) l

@[expose] noncomputable def searchK (N : Nat) (m : Nat → Nat → Nat) (f : Nat) :
    List Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => List Nat → Nat → Bool) (fun _ _ => false)
    (fun _ ih sp lo => allN N (fun y =>
      bIf(Nat.blt y lo, true, bIf(memB y sp, true,
        bIf(allR (fun s => Nat.blt (m y s) N) sp,
          bIf(allR (fun s => Nat.ble y (m y s)) sp,
            forceL (y :: (sp ++ sp.map (m y))) (fun sp' => ih sp' (Nat.succ y)), true),
          true))))) f

@[expose] noncomputable def baseEqK (A B C : Nat) : Bool :=
  allN 5 (fun t => strictB (pg 11 (mask 11) TitsS.BP t) (fun b =>
    Nat.beq (pg 11 (mask 11) A (pg 11 (mask 11) B b)) (pg 11 (mask 11) C b)))

@[expose] noncomputable def movedK (A B : Nat) : Bool :=
  bIf(allN 1755 (fun x => Nat.beq (pg 11 (mask 11) A (pg 11 (mask 11) B
    (pg 11 (mask 11) A (pg 11 (mask 11) B x)))) x), false, true)

@[expose] noncomputable def pcK (M : Nat → Nat → Nat) (i j : Nat) : Bool :=
  strictB (IT i) (fun A => strictB (IT j) (fun B => strictB (M i j) (fun k =>
    bIf(Nat.blt k 143, baseEqK A B (IT k),
      bAnd(Nat.beq k 143, bIf(Nat.beq i j, true, movedK A B))))))

@[expose] noncomputable def sqQ (Q t0 t1 t2 t3 t4 : Nat) : Bool :=
  allN 1755 (fun i =>
    Nat.beq (gpt 11 (mask 11) t0 t1 t2 t3 t4 (pg 11 (mask 11) Q
      (gpt 11 (mask 11) t0 t1 t2 t3 t4 (pg 11 (mask 11) Q i)))) i)

@[expose] noncomputable def outQ (Q t0 t1 t2 t3 t4 : Nat) : Bool :=
  bIf(sqQ Q t0 t1 t2 t3 t4, false, true)

theorem ch4193len : Nat.beq E32.SI.L.length 143 = true := by quickRfl

theorem ch4193it : allN 143 (fun i => Nat.beq (IT i) (E32.SI.L.getD i 0)) = true := by quickRfl

theorem ch4193pc0 : allN 36 (fun i => allN 143 (fun j => pcK mulT i j)) = true := by quickRfl

theorem ch4193pc1 : allN 36 (fun i => allN 143 (fun j => pcK mulT (Nat.add 36 i) j)) = true := by
  quickRfl

theorem ch4193pc2 : allN 36 (fun i => allN 143 (fun j => pcK mulT (Nat.add 72 i) j)) = true := by
  quickRfl

theorem ch4193pc3 : allN 35 (fun i => allN 143 (fun j => pcK mulT (Nat.add 108 i) j)) = true := by
  quickRfl

theorem ch4193srch : searchK 143 mulT 6 [] 0 = true := by quickRfl

theorem ch4193out : all5K 1755 (1755 * 11) TitsS.LR TitsS.TR
    (fun _ => outQ CertificateChecks.KernelMisc.TitsPi.P) = true := by quickRfl

theorem ch4193negS : (searchK 143 mulT 2 [] 0).not = true := by quickRfl

theorem ch4193negP : (allN 143 (fun j => pcK (fun _ _ => 143) 0 j)).not = true := by quickRfl

theorem ch4193negW : (all5K 1755 (1755 * 11) TitsS.LR TitsS.TR
    (fun _ => outQ (pidn 1755 11))).not = true := by quickRfl

theorem ch4193negI : (Nat.beq (IT 1) (E32.SI.L.getD 0 0)).not = true := by quickRfl

end CertificateChecks.KernelSporSch.Rank4193

end
