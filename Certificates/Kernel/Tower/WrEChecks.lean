module

public import Certificates.Data.Kernel.Tower.Search14O
public import Certificates.Data.Kernel.Tower.Cls14
public import Certificates.Data.Kernel.Tower.T2
public import Certificates.Kernel.Tower.WData
public import Certificates.Kernel.Tower.AData
public import Certificates.Kernel.Tower.L3Data
public import Certificates.Kernel.Tower.L3WData
public import Certificates.Kernel.Tower.WrEData
public import Certificates.Data.Kernel.Tower.Chunk
public import Certificates.Data.Kernel.Tower.Cnt
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.EachBy
import CFSG.Certificates.Kernel.Common.ForallTree

public section

namespace Certificates.KernelTower

open Certificates.KernelTower

@[expose] noncomputable def wrED (e k : Nat) : Nat := wrE (Nat.add (Nat.mul 64 e) k)

@[expose] noncomputable def wrEP (e k : Nat) : Nat := l16 (wrX 12) (Nat.add (Nat.mul 16 e) k)

@[expose] noncomputable def wrEm (a g : Nat) : Nat → Nat → Nat :=
  tm (wm wrSM wrAC) (wrA (Nat.add a 2)) g

@[expose] noncomputable def wrEM (e : Nat) : Nat → Nat → Nat := wrEm (wrEP e 0) (wrEP e 1)

@[expose] noncomputable def wrTG (f0 q : Nat) : Nat :=
  wrL3W (Nat.add (Nat.mul 18 (Nat.add f0 (Nat.shiftRight q 4))) (Nat.add 2 (Nat.land q 15)))

@[expose] noncomputable def ch36408_eord (e : Nat) : Bool := ordOK 16384 (wrEM e) (wrED e 0)

@[expose] noncomputable def ch36408_elab (e : Nat) : Bool :=
  labOK16 16384 4 (wrEM e) (wrED e 5) (wrED e 6) (wrED e 1) (wrED e 2) (wrEP e 2) &&
    czOK16 16384 (wrED e 1) (wrED e 3)

@[expose] noncomputable def ch36408_eh (e : Nat) : Bool :=
  hOK16 16384 (wrEM e) 128 (wrED e 4) && treeB 16384 4 (wrEM e) (wrED e 5) (wrED e 7) &&
    kyOK (wrEM e) (wrED e 0) (wrED e 1) (wrED e 3) (wrED e 5) (wrED e 8) (wrED e 9)

@[expose] noncomputable def ch36408_ecm (e : Nat) : Bool :=
  cmOK16 16384 (wrEM e) 128 (wrED e 0) (wrED e 1) (wrED e 3) (kyL (wrED e 8) 0) (wrED e 10)
      (wrED e 12) (wrEP e 3) &&
    cmOK16 16384 (wrEM e) 128 (wrED e 0) (wrED e 1) (wrED e 3) (kyL (wrED e 8) 1) (wrED e 11)
      (wrED e 13) (wrEP e 4) &&
    cmOK16 16384 (wrEM e) 128 (wrED e 0) (wrED e 1) (wrED e 3) (kyL (wrED e 8) 2) (wrED e 17)
      (wrED e 18) (wrEP e 5)

@[expose] noncomputable def ch36408_el12 (e : Nat) : Bool :=
  e14Lvl1 16384 (wrEM e) (wrED e 4) (wrED e 10) (wrEP e 3) (wrED e 14) (wrED e 15) (wrEP e 6) &&
    allB (wrEP e 6) fun r1 => e14Lvl2 16384 (wrEM e) (wrED e 0) (wrED e 1) (wrED e 3) 128
      (wrED e 4) (wrED e 11) (wrEP e 4) (wrED e 14) (wrED e 16) (pvL (wrED e 9) 0) (wrEP e 7)
      (wrED e (Nat.add 19 r1)) r1

@[expose] noncomputable def wrEL3 (e r2 : Nat) : Bool :=
  e14Lvl3O (wrEM e) (wrED e 0) (wrED e 1) (wrED e 3) 128 (wrED e 4) (wrED e 5) (wrED e 7)
    (wrEP e 8) (wrED e 14) (wrED e 16) (pvL (wrED e 9) 1) (pvL (wrED e 9) 2) (wrTG (wrEP e 9))
    (Nat.mul 16 (wrEP e 10)) (wrED e 17) (wrEP e 5) (wrED e (Nat.add 19 (Nat.add (wrEP e 6) r2)))
    r2

@[expose] noncomputable def ch36408_el3 (e : Nat) : Bool := allB (wrEP e 7) (wrEL3 e)

@[expose] noncomputable def ch36408_efam (e : Nat) : Bool :=
  allB (wrEP e 10) fun k =>
    Nat.beq (l16 (wrL3 (Nat.mul 34 (Nat.add (wrEP e 9) k))) 0) (wrEP e 0) &&
      Nat.beq (l16 (wrL3 (Nat.mul 34 (Nat.add (wrEP e 9) k))) 1) (wrEP e 1) &&
      allB 4 fun i => Nat.beq (l16 (wrL3W (Nat.mul 18 (Nat.add (wrEP e 9) k))) i) (l16 (wrED e 5) i)

@[expose] noncomputable def ch36408_epc (e : Nat) : Bool :=
  pcB 16384 (wrEM e) (wrED e 0) (wrED e 1) (wrED e 2) (wrED e 3) (wrEP e 2) 128 (l16 (wrED e 5) 0)

@[expose] noncomputable def ch36408_echi (e : Nat) : Bool :=
  chiB 16384 (wrEM e) (wrED e 5) (wrX e) 128 (l16 (wrED e 5) 0)

@[expose] noncomputable def ch36408_eordC (q : Nat) : Bool :=
  chunkB (fun c => ordC (wrEM (q / 32)) c (oe (wrED (q / 32) 0) c)) (q % 32)

@[expose] noncomputable def ch36408_elabC (q : Nat) : Bool :=
  chunkB (labC16 16384 4 (wrEM (q / 32)) (wrED (q / 32) 5) (wrED (q / 32) 6) (wrED (q / 32) 1)
    (wrED (q / 32) 2) (wrEP (q / 32) 2)) (q % 32)

@[expose] noncomputable def ch36408_elabH (e : Nat) : Bool :=
  allB 4 (fun i => Nat.blt (l16 (wrED e 6) i) 16384 &&
      Nat.beq (wrEM e (l16 (wrED e 5) i) (l16 (wrED e 6) i)) 0) &&
    allB (wrEP e 2) (fun l => Nat.blt (l16 (wrED e 2) l) 16384 &&
      Nat.beq (lbL (wrED e 1) (l16 (wrED e 2) l)) l) &&
    czOK16 16384 (wrED e 1) (wrED e 3)

@[expose] noncomputable def ch36408_echiC (q : Nat) : Bool :=
  chunkB (fun c => allB 4 fun s => Nat.beq (bit (wrX (q / 32)) (wrEM (q / 32) (l16 (wrED (q / 32) 5) s) c))
    (Nat.xor (bit (wrX (q / 32)) (l16 (wrED (q / 32) 5) s)) (bit (wrX (q / 32)) c))) (q % 32)

@[expose] noncomputable def ch36408_echiH (e : Nat) : Bool :=
  Nat.beq (bit (wrX e) 0) 0 && Nat.beq (bit (wrX e) 128) 1 &&
    Nat.beq (bit (wrX e) (l16 (wrED e 5) 0)) 1

@[expose] noncomputable def wrCmU (e u : Nat) : Bool :=
  (fun k => (!Nat.beq k (kyL (wrED e 8) 0) ||
      Nat.blt (rkL (wrED e 12) u) (wrEP e 3) && Nat.beq (l16 (wrED e 10) (rkL (wrED e 12) u)) u) &&
    (!Nat.beq k (kyL (wrED e 8) 1) ||
      Nat.blt (rkL (wrED e 13) u) (wrEP e 4) && Nat.beq (l16 (wrED e 11) (rkL (wrED e 13) u)) u) &&
    (!Nat.beq k (kyL (wrED e 8) 2) ||
      Nat.blt (rkL (wrED e 18) u) (wrEP e 5) && Nat.beq (l16 (wrED e 17) (rkL (wrED e 18) u)) u))
  (ivOf (wrEM e) (wrED e 0) (wrED e 1) (wrED e 3) 128 u)

@[expose] noncomputable def ch36408_ecmC (q : Nat) : Bool := chunkB (wrCmU (q / 32)) (q % 32)

@[expose] noncomputable def wrEhU (e c : Nat) : Bool :=
  (!Nat.beq (wrEM e c 128) (wrEM e 128 c) || bitS (hmL (wrED e 4) 256) c) &&
    (Nat.beq c 0 || (Nat.blt (ptGi (wrED e 7) c) 4 && Nat.blt (ptPar (wrED e 7) c) 16384 &&
      Nat.blt (ptDep (wrED e 7) (ptPar (wrED e 7) c)) (ptDep (wrED e 7) c) &&
      Nat.beq (wrEM e (l16 (wrED e 5) (ptGi (wrED e 7) c)) (ptPar (wrED e 7) c)) c))

@[expose] noncomputable def ch36408_ehC (q : Nat) : Bool := chunkB (wrEhU (q / 32)) (q % 32)

@[expose] noncomputable def ch36408_ehH (e : Nat) : Bool :=
  allB 256 (fun j => Nat.blt (l16 (wrED e 4) j) 16384 &&
      Nat.beq (wrEM e (l16 (wrED e 4) j) 128) (wrEM e 128 (l16 (wrED e 4) j))) &&
    allB 255 (fun j => Nat.blt (l16 (wrED e 4) j) (l16 (wrED e 4) (Nat.succ j))) &&
    allB 4 (fun i => Nat.blt (l16 (wrED e 5) i) 16384) &&
    kyOK (wrEM e) (wrED e 0) (wrED e 1) (wrED e 3) (wrED e 5) (wrED e 8) (wrED e 9)

#kc_each ch36408_eordC 0 384
#kc_each ch36408_elabC 0 384
#kc_each ch36408_elabH 0 12
#kc_each ch36408_echiC 0 384
#kc_each ch36408_echiH 0 12
#kc_each ch36408_ecmC 0 384
#kc_each ch36408_ehC 0 384
#kc_each ch36408_ehH 0 12

#kc_forall_tree ch36408_eordC_all (fun q => ch36408_eordC q = true) 384
  Certificates.KernelTower.ch36408_eordC
#kc_forall_tree ch36408_elabC_all (fun q => ch36408_elabC q = true) 384
  Certificates.KernelTower.ch36408_elabC
#kc_forall_tree ch36408_elabH_all (fun e => ch36408_elabH e = true) 12
  Certificates.KernelTower.ch36408_elabH
#kc_forall_tree ch36408_echiC_all (fun q => ch36408_echiC q = true) 384
  Certificates.KernelTower.ch36408_echiC
#kc_forall_tree ch36408_echiH_all (fun e => ch36408_echiH e = true) 12
  Certificates.KernelTower.ch36408_echiH
#kc_forall_tree ch36408_ecmC_all (fun q => ch36408_ecmC q = true) 384
  Certificates.KernelTower.ch36408_ecmC
#kc_forall_tree ch36408_ehC_all (fun q => ch36408_ehC q = true) 384
  Certificates.KernelTower.ch36408_ehC
#kc_forall_tree ch36408_ehH_all (fun e => ch36408_ehH e = true) 12
  Certificates.KernelTower.ch36408_ehH

theorem chunk_div {e q : Nat} (hq : q < 32) : (32 * e + q) / 32 = e := by omega

theorem chunk_mod {e q : Nat} (hq : q < 32) : (32 * e + q) % 32 = q := by omega

theorem chunk_lt {e q : Nat} (he : e < 12) (hq : q < 32) : 32 * e + q < 384 := by omega

theorem ch36408_eord_lt (e : Nat) (he : e < 12) : ch36408_eord e = true := by
  have hC : ∀ q < 32, chunkB (fun c => ordC (wrEM e) c (oe (wrED e 0) c)) q = true := by
    intro q hq
    have h := ch36408_eordC_all (32 * e + q) (chunk_lt he hq)
    rw [ch36408_eordC, chunk_div hq, chunk_mod hq] at h
    exact h
  rw [ch36408_eord, ordOK]
  exact allB_of_chunks hC

theorem ch36408_elab_lt (e : Nat) (he : e < 12) : ch36408_elab e = true := by
  have hC : ∀ q < 32, chunkB (labC16 16384 4 (wrEM e) (wrED e 5) (wrED e 6) (wrED e 1)
      (wrED e 2) (wrEP e 2)) q = true := by
    intro q hq
    have h := ch36408_elabC_all (32 * e + q) (chunk_lt he hq)
    rw [ch36408_elabC, chunk_div hq, chunk_mod hq] at h
    exact h
  have hH := ch36408_elabH_all e he
  rw [ch36408_elabH, Bool.and_eq_true, Bool.and_eq_true] at hH
  rw [ch36408_elab, labOK16, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨⟨hH.1.1, hH.1.2⟩, allB_of_chunks (m := 32) hC⟩, hH.2⟩

theorem ch36408_echi_lt (e : Nat) (he : e < 12) : ch36408_echi e = true := by
  have hC : ∀ q < 32, chunkB (fun c => allB 4 fun s => Nat.beq (bit (wrX e)
      (wrEM e (l16 (wrED e 5) s) c)) (Nat.xor (bit (wrX e) (l16 (wrED e 5) s)) (bit (wrX e) c)))
      q = true := by
    intro q hq
    have h := ch36408_echiC_all (32 * e + q) (chunk_lt he hq)
    rw [ch36408_echiC, chunk_div hq, chunk_mod hq] at h
    exact h
  have hH := ch36408_echiH_all e he
  rw [ch36408_echiH, Bool.and_eq_true, Bool.and_eq_true] at hH
  rw [ch36408_echi, chiB, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨⟨hH.1.1, hH.1.2⟩, hH.2⟩, allB_of_chunks (m := 32) hC⟩

theorem ch36408_ecm_lt (e : Nat) (he : e < 12) : ch36408_ecm e = true := by
  have hC : ∀ q < 32, chunkB (wrCmU e) q = true := by
    intro q hq
    have h := ch36408_ecmC_all (32 * e + q) (chunk_lt he hq)
    rw [ch36408_ecmC, chunk_div hq, chunk_mod hq] at h
    exact h
  have hA := allB_true_iff.1 (allB_of_chunks (m := 32) hC)
  simp only [ch36408_ecm, cmOK16, Bool.and_eq_true]
  refine ⟨⟨allB_true_iff.2 fun u hu => ?_, allB_true_iff.2 fun u hu => ?_⟩,
    allB_true_iff.2 fun u hu => ?_⟩
  · have h := hA u (by omega)
    simp only [wrCmU, Bool.and_eq_true] at h
    exact h.1.1
  · have h := hA u (by omega)
    simp only [wrCmU, Bool.and_eq_true] at h
    exact h.1.2
  · have h := hA u (by omega)
    simp only [wrCmU, Bool.and_eq_true] at h
    exact h.2

theorem ch36408_ehU_lt (e : Nat) (he : e < 12) : ∀ c < 16384, wrEhU e c = true := by
  have hC : ∀ q < 32, chunkB (wrEhU e) q = true := by
    intro q hq
    have h := ch36408_ehC_all (32 * e + q) (chunk_lt he hq)
    rw [ch36408_ehC, chunk_div hq, chunk_mod hq] at h
    exact h
  exact allB_true_iff.1 (allB_of_chunks (m := 32) hC)

#kc_each_by ch36408_eord 0 12 ch36408_eord_lt
#kc_each_by ch36408_elab 0 12 ch36408_elab_lt
#kc_each_by ch36408_ecm 0 12 ch36408_ecm_lt
#kc_each ch36408_el12 0 12
#kc_each ch36408_el3 0 12
#kc_each ch36408_efam 0 12
#kc_each_by ch36408_echi 0 12 ch36408_echi_lt

theorem ch36408_e_neg : (!e14Lvl3O (wrEM 0) (wrED 0 0) (wrED 0 1) (wrED 0 3) 128 (wrED 0 4)
    (wrED 0 5) (wrED 0 7) (wrEP 0 8) (wrED 0 14) (wrED 0 16) (pvL (wrED 0 9) 1) (pvL (wrED 0 9) 2)
    (wrTG (wrEP 0 9)) (Nat.mul 16 (wrEP 0 10)) (wrED 0 17) (wrEP 0 5) 0 0) = true := by
  decide +kernel

theorem ch36408_e_neg2 : (!allB (wrEP 0 7) fun r2 => e14Lvl3O (wrEM 0) (wrED 0 0) (wrED 0 1)
    (wrED 0 3) 128 (wrED 0 4) (wrED 0 5) (wrED 0 7) (wrEP 0 8) (wrED 0 14) (wrED 0 16)
    (pvL (wrED 0 9) 1) (pvL (wrED 0 9) 2) (wrTG (wrEP 0 9)) 1 (wrED 0 17) (wrEP 0 5)
    (wrED 0 (Nat.add 19 (Nat.add (wrEP 0 6) r2))) r2) = true := by
  decide +kernel

theorem ch36408_e_pc_neg : (!pcB 16384 (wrEM 0) (wrED 0 0) (wrED 0 1) (wrED 0 2) (wrED 0 3)
    (wrEP 0 2) 128 128) = true := by
  decide +kernel

theorem ch36408_e_chi_neg : (!chiB 16384 (wrEM 0) (wrED 0 5) (Nat.xor (wrX 0) 8) 128
    (l16 (wrED 0 5) 0)) = true := by
  decide +kernel

end Certificates.KernelTower
