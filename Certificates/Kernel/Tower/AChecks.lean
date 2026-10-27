module

public import Certificates.Data.Kernel.Tower.Tree
public import Certificates.Kernel.Tower.WData
public import Certificates.Kernel.Tower.AData
public import Certificates.Data.Kernel.Tower.Chunk
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree

public section

namespace Certificates.KernelTower

open Certificates.KernelTower

@[expose] def imA (IM a : Nat) : Nat := Nat.shiftRight IM (Nat.mul 64 a)

@[expose] noncomputable def slRec (k : Nat) : Bool :=
  allB 8 fun j => recB 8192 4 (wm slSM slAC) slPT (imA slIM (Nat.add (Nat.mul 8 k) j))
    (slA (Nat.add (Nat.add (Nat.mul 8 k) j) 2))

@[expose] noncomputable def wrRecU (a c : Nat) : Bool :=
  Nat.beq c 0 || Nat.beq (l16 (wrA (Nat.add a 2)) c)
    (wm wrSM wrAC (l16 (imA wrIM a) (ptGi wrPT c)) (l16 (wrA (Nat.add a 2)) (ptPar wrPT c)))

@[expose] noncomputable def ch36408_recC (q : Nat) : Bool := chunkB (wrRecU (q / 16)) (q % 16)

@[expose] noncomputable def wrRecH (a : Nat) : Bool :=
  allB 4 (fun i => Nat.blt (l16 (imA wrIM a) i) 8192) && Nat.beq (l16 (wrA (Nat.add a 2)) 0) 0

theorem ch36409_tree : treeB 8192 4 (wm slSM slAC) wGS slPT = true := by decide +kernel
theorem ch36408_tree : treeB 8192 4 (wm wrSM wrAC) wGS wrPT = true := by decide +kernel

theorem ch36409_rec0 : slRec 0 = true := by decide +kernel
theorem ch36409_rec1 : slRec 1 = true := by decide +kernel
theorem ch36409_rec2 : slRec 2 = true := by decide +kernel
theorem ch36409_rec3 : slRec 3 = true := by decide +kernel

theorem ch36408_recH : allB 96 wrRecH = true := by decide +kernel

#kc_each ch36408_recC 0 1536

#kc_forall_tree ch36408_recC_all (fun q => ch36408_recC q = true) 1536
  Certificates.KernelTower.ch36408_recC

theorem ch36408_rec_lt {a : Nat} (ha : a < 96) :
    recB 8192 4 (wm wrSM wrAC) wrPT (imA wrIM a) (wrA (Nat.add a 2)) = true := by
  have hC : ∀ q < 16, chunkB (wrRecU a) q = true := by
    intro q hq
    have hlt : 16 * a + q < 1536 := by omega
    have h := ch36408_recC_all (16 * a + q) hlt
    have e1 : (16 * a + q) / 16 = a := by omega
    have e2 : (16 * a + q) % 16 = q := by omega
    rw [ch36408_recC, e1, e2] at h
    exact h
  have hH := allB_true_iff.1 ch36408_recH a ha
  rw [wrRecH] at hH
  rw [recB, hH, Bool.true_and]
  exact allB_of_chunks (m := 16) hC

theorem ch36409_tree_neg :
    (!treeB 8192 4 (wm slSM slAC) wGS (Nat.xor slPT (Nat.shiftLeft 1 (Nat.mul 32 77)))) = true := by
  decide +kernel
theorem ch36409_rec_neg :
    (!recB 8192 4 (wm slSM slAC) slPT (imA slIM 5) (Nat.xor (slA 7) (Nat.shiftLeft 1 1600))) =
      true := by
  decide +kernel

end Certificates.KernelTower
