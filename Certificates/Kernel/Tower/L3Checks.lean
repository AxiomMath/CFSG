module

public import Certificates.Data.Kernel.Tower.T2
public import Certificates.Kernel.Tower.WData
public import Certificates.Kernel.Tower.AData
public import Certificates.Kernel.Tower.L3Data
public import Certificates.Data.Kernel.Tower.Chunk
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.EachBy
import CFSG.Certificates.Kernel.Common.ForallTree

public section

namespace Certificates.KernelTower

open Certificates.KernelTower

@[expose] noncomputable def l3P (f : Nat) : Nat := wrL3 (Nat.mul 34 f)

@[expose] noncomputable def l3S (f j : Nat) : Nat := wrL3 (Nat.add (Nat.mul 34 f) (Nat.add 2 (Nat.mul 2 j)))

@[expose] noncomputable def l3X (f j : Nat) : Nat := wrL3 (Nat.add (Nat.mul 34 f) (Nat.add 3 (Nat.mul 2 j)))

@[expose] noncomputable def l3U (f : Nat) : Nat := Nat.rec 0 (fun j acc => Nat.lor (l3S f j) acc) 16

@[expose] noncomputable def l3H (f j : Nat) : Nat := l16 (l3P f) (Nat.add 7 j)

@[expose] noncomputable def l3HM (f : Nat) : Nat :=
  Nat.rec 0 (fun j acc => Nat.lor acc
    (Nat.lor (Nat.shiftLeft 1 (l3H f j)) (Nat.shiftLeft 1 (Nat.xor (l3H f j) 2)))) 16

@[expose] noncomputable def l3M (f : Nat) : Nat → Nat → Nat :=
  tm (wm wrSM wrAC) (wrA (Nat.add 2 (l16 (l3P f) 0))) (l16 (l3P f) 1)

@[expose] noncomputable def ch36408_l3 (f : Nat) : Bool :=
  famB (l3M f) wrPT (Nat.shiftRight (l3P f) 48) (wrL3 (Nat.add (Nat.mul 34 f) 1)) (l16 (l3P f) 2)
    (l3H f) (l3S f) (l3X f) (l3U f) (l3HM f)

@[expose] noncomputable def l3FC (f c : Nat) : Bool :=
  famC (l3M f) wrPT (Nat.shiftRight (l3P f) 48) (wrL3 (Nat.add (Nat.mul 34 f) 1)) (l16 (l3P f) 2)
    (l3H f) (l3S f) (l3X f) (l3U f) (l3HM f) c (l16 (wrL3 (Nat.add (Nat.mul 34 f) 1)) c)

@[expose] noncomputable def ch36408_l3C (q : Nat) : Bool := chunkB (l3FC (q / 16)) (q % 16)

@[expose] noncomputable def ch36408_l3H (f : Nat) : Bool :=
  allB 4 (fun i => Nat.blt (l16 (Nat.shiftRight (l3P f) 48) i) 16384) &&
    Nat.blt (l16 (l3P f) 2) 16384 && Nat.beq (l16 (wrL3 (Nat.add (Nat.mul 34 f) 1)) 0) 0 &&
    allB 16 (fun j => Nat.blt (l3H f j) 16384 && bitS (l3HM f) (l3H f j) &&
      bitS (l3HM f) (Nat.xor (l3H f j) 2))

#kc_each ch36408_l3C 0 448
#kc_each ch36408_l3H 0 28

#kc_forall_tree ch36408_l3C_all (fun q => ch36408_l3C q = true) 448
  Certificates.KernelTower.ch36408_l3C
#kc_forall_tree ch36408_l3H_all (fun f => ch36408_l3H f = true) 28
  Certificates.KernelTower.ch36408_l3H

theorem ch36408_l3_lt (f : Nat) (hf : f < 28) : ch36408_l3 f = true := by
  have hC : ∀ q < 16, chunkB (l3FC f) q = true := by
    intro q hq
    have hlt : 16 * f + q < 448 := by omega
    have h := ch36408_l3C_all (16 * f + q) hlt
    have e1 : (16 * f + q) / 16 = f := by omega
    have e2 : (16 * f + q) % 16 = q := by omega
    rw [ch36408_l3C, e1, e2] at h
    exact h
  have hH := ch36408_l3H_all f hf
  rw [ch36408_l3H] at hH
  rw [ch36408_l3, famB, hH, Bool.true_and]
  exact allB_of_chunks (m := 16) hC

#kc_each_by ch36408_l3 0 28 ch36408_l3_lt

theorem ch36408_l3_neg :
    notB (famB (l3M 0) wrPT (Nat.shiftRight (l3P 0) 48) (wrL3 1) (l16 (l3P 0) 2)
      (l3H 0) (fun j => Nat.xor (l3S 0 j) (Nat.shiftLeft 1 300))
      (l3X 0) (Nat.xor (l3U 0) (Nat.shiftLeft 1 300)) (l3HM 0)) = true := by
  decide +kernel

end Certificates.KernelTower
