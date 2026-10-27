module

public import Certificates.Data.Kernel.Tower.Search14
public import Certificates.Data.Kernel.Tower.T2
public import Certificates.Kernel.Tower.WData
public import Certificates.Kernel.Tower.AData
public import Certificates.Kernel.Tower.E14Data
public import Certificates.Data.Kernel.Tower.Chunk
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree

public section

namespace Certificates.KernelTower

open Certificates.KernelTower

@[expose] noncomputable def slEm (a g : Nat) : Nat → Nat → Nat :=
  tm (wm slSM slAC) (slA (Nat.add a 2)) g

@[expose] noncomputable def e14Ord (D : Nat → Nat) (a g : Nat) : Bool := ordOK 16384 (slEm a g) (D 0)

@[expose] noncomputable def e14Lab (D : Nat → Nat) (a g nl : Nat) : Bool :=
  labOK16 16384 4 (slEm a g) (D 5) (D 6) (D 1) (D 2) nl && czOK16 16384 (D 1) (D 3)

@[expose] noncomputable def e14H (D : Nat → Nat) (a g : Nat) : Bool :=
  hOK16 16384 (slEm a g) 128 (D 4) && treeB 16384 4 (slEm a g) (D 5) (D 7) &&
    kyOK (slEm a g) (D 0) (D 1) (D 3) (D 5) (D 8) (D 9)

@[expose] noncomputable def e14Cm (D : Nat → Nat) (a g c1 c2 : Nat) : Bool :=
  cmOK16 16384 (slEm a g) 128 (D 0) (D 1) (D 3) (kyL (D 8) 0) (D 10) (D 12) c1 &&
    cmOK16 16384 (slEm a g) 128 (D 0) (D 1) (D 3) (kyL (D 8) 1) (D 11) (D 13) c2

@[expose] noncomputable def e14L12 (D : Nat → Nat) (a g c1 c2 n1 n2 : Nat) : Bool :=
  e14Lvl1 16384 (slEm a g) (D 4) (D 10) c1 (D 14) (D 15) n1 &&
    allB n1 fun r1 => e14Lvl2 16384 (slEm a g) (D 0) (D 1) (D 3) 128 (D 4) (D 11) c2 (D 14) (D 16)
      (pvL (D 9) 0) n2 (D (Nat.add 17 r1)) r1

@[expose] noncomputable def e14L3 (D : Nat → Nat) (a g n1 r2 : Nat) : Bool :=
  e14Lvl3 16384 (slEm a g) (D 0) (D 1) (D 3) 128 (D 5) (D 7) 16 (D 14) (D 16) (kyL (D 8) 2)
    (pvL (D 9) 1) (pvL (D 9) 2) (D (Nat.add 17 (Nat.add n1 r2))) r2

@[expose] def sl4 (e x0 x1 x2 x3 : Nat) : Nat :=
  cond (Nat.beq e 0) x0 (cond (Nat.beq e 1) x1 (cond (Nat.beq e 2) x2 x3))

@[expose] noncomputable def slED (e : Nat) : Nat → Nat :=
  cond (Nat.beq e 0) slE0 (cond (Nat.beq e 1) slE1 (cond (Nat.beq e 2) slE2 slE3))

@[expose] def slEA (e : Nat) : Nat := sl4 e 0 2 9 11

@[expose] def slEG (e : Nat) : Nat := sl4 e 132 132 0 0

@[expose] def slEN (e : Nat) : Nat := sl4 e 100 94 100 94

@[expose] noncomputable def slEM (e : Nat) : Nat → Nat → Nat := slEm (slEA e) (slEG e)

@[expose] noncomputable def ch36409_eordC (q : Nat) : Bool :=
  chunkB (fun c => ordC (slEM (q / 32)) c (oe (slED (q / 32) 0) c)) (q % 32)

@[expose] noncomputable def ch36409_elabC (q : Nat) : Bool :=
  chunkB (labC16 16384 4 (slEM (q / 32)) (slED (q / 32) 5) (slED (q / 32) 6) (slED (q / 32) 1)
    (slED (q / 32) 2) (slEN (q / 32))) (q % 32)

@[expose] noncomputable def ch36409_elabH (e : Nat) : Bool :=
  allB 4 (fun i => Nat.blt (l16 (slED e 6) i) 16384 &&
      Nat.beq (slEM e (l16 (slED e 5) i) (l16 (slED e 6) i)) 0) &&
    allB (slEN e) (fun l => Nat.blt (l16 (slED e 2) l) 16384 &&
      Nat.beq (lbL (slED e 1) (l16 (slED e 2) l)) l) &&
    czOK16 16384 (slED e 1) (slED e 3)

#kc_each ch36409_eordC 0 128
#kc_each ch36409_elabC 0 128
#kc_each ch36409_elabH 0 4

#kc_forall_tree ch36409_eordC_all (fun q => ch36409_eordC q = true) 128
  Certificates.KernelTower.ch36409_eordC
#kc_forall_tree ch36409_elabC_all (fun q => ch36409_elabC q = true) 128
  Certificates.KernelTower.ch36409_elabC
#kc_forall_tree ch36409_elabH_all (fun e => ch36409_elabH e = true) 4
  Certificates.KernelTower.ch36409_elabH

theorem ch36409_chunk_div {e q : Nat} (hq : q < 32) : (32 * e + q) / 32 = e := by omega

theorem ch36409_chunk_mod {e q : Nat} (hq : q < 32) : (32 * e + q) % 32 = q := by omega

theorem ch36409_chunk_lt {e q : Nat} (he : e < 4) (hq : q < 32) : 32 * e + q < 128 := by omega

theorem ch36409_eord_lt (e : Nat) (he : e < 4) : e14Ord (slED e) (slEA e) (slEG e) = true := by
  have hC : ∀ q < 32, chunkB (fun c => ordC (slEM e) c (oe (slED e 0) c)) q = true := by
    intro q hq
    have h := ch36409_eordC_all (32 * e + q) (ch36409_chunk_lt he hq)
    rw [ch36409_eordC, ch36409_chunk_div hq, ch36409_chunk_mod hq] at h
    exact h
  rw [e14Ord, ordOK]
  exact allB_of_chunks hC

theorem ch36409_elab_lt (e : Nat) (he : e < 4) :
    e14Lab (slED e) (slEA e) (slEG e) (slEN e) = true := by
  have hC : ∀ q < 32, chunkB (labC16 16384 4 (slEM e) (slED e 5) (slED e 6) (slED e 1)
      (slED e 2) (slEN e)) q = true := by
    intro q hq
    have h := ch36409_elabC_all (32 * e + q) (ch36409_chunk_lt he hq)
    rw [ch36409_elabC, ch36409_chunk_div hq, ch36409_chunk_mod hq] at h
    exact h
  have hH := ch36409_elabH_all e he
  rw [ch36409_elabH, Bool.and_eq_true, Bool.and_eq_true] at hH
  rw [e14Lab, labOK16, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨⟨hH.1.1, hH.1.2⟩, allB_of_chunks (m := 32) hC⟩, hH.2⟩

theorem ch36409_e0_ord : e14Ord slE0 0 132 = true := ch36409_eord_lt 0 (by decide)
theorem ch36409_e0_lab : e14Lab slE0 0 132 100 = true := ch36409_elab_lt 0 (by decide)
theorem ch36409_e0_h : e14H slE0 0 132 = true := by decide +kernel
theorem ch36409_e0_cm : e14Cm slE0 0 132 20 32 = true := by decide +kernel
theorem ch36409_e0_l12 : e14L12 slE0 0 132 20 32 5 2 = true := by decide +kernel
theorem ch36409_e0_l30 : e14L3 slE0 0 132 5 0 = true := by decide +kernel
theorem ch36409_e0_l31 : e14L3 slE0 0 132 5 1 = true := by decide +kernel

theorem ch36409_e1_ord : e14Ord slE1 2 132 = true := ch36409_eord_lt 1 (by decide)
theorem ch36409_e1_lab : e14Lab slE1 2 132 94 = true := ch36409_elab_lt 1 (by decide)
theorem ch36409_e1_h : e14H slE1 2 132 = true := by decide +kernel
theorem ch36409_e1_cm : e14Cm slE1 2 132 16 32 = true := by decide +kernel
theorem ch36409_e1_l12 : e14L12 slE1 2 132 16 32 3 2 = true := by decide +kernel
theorem ch36409_e1_l30 : e14L3 slE1 2 132 3 0 = true := by decide +kernel
theorem ch36409_e1_l31 : e14L3 slE1 2 132 3 1 = true := by decide +kernel

theorem ch36409_e2_ord : e14Ord slE2 9 0 = true := ch36409_eord_lt 2 (by decide)
theorem ch36409_e2_lab : e14Lab slE2 9 0 100 = true := ch36409_elab_lt 2 (by decide)
theorem ch36409_e2_h : e14H slE2 9 0 = true := by decide +kernel
theorem ch36409_e2_cm : e14Cm slE2 9 0 20 32 = true := by decide +kernel
theorem ch36409_e2_l12 : e14L12 slE2 9 0 20 32 5 2 = true := by decide +kernel
theorem ch36409_e2_l30 : e14L3 slE2 9 0 5 0 = true := by decide +kernel
theorem ch36409_e2_l31 : e14L3 slE2 9 0 5 1 = true := by decide +kernel

theorem ch36409_e3_ord : e14Ord slE3 11 0 = true := ch36409_eord_lt 3 (by decide)
theorem ch36409_e3_lab : e14Lab slE3 11 0 94 = true := ch36409_elab_lt 3 (by decide)
theorem ch36409_e3_h : e14H slE3 11 0 = true := by decide +kernel
theorem ch36409_e3_cm : e14Cm slE3 11 0 16 32 = true := by decide +kernel
theorem ch36409_e3_l12 : e14L12 slE3 11 0 16 32 3 2 = true := by decide +kernel
theorem ch36409_e3_l30 : e14L3 slE3 11 0 3 0 = true := by decide +kernel
theorem ch36409_e3_l31 : e14L3 slE3 11 0 3 1 = true := by decide +kernel

theorem ch36409_e14_neg : (!e14Lvl3 16384 (slEm 0 132) (slE0 0) (slE0 1) (slE0 3) 128 (slE0 5)
    (slE0 7) 16 (slE0 14) (slE0 16) (kyL (slE0 8) 2) (pvL (slE0 9) 1) (pvL (slE0 9) 2)
    (Nat.land (slE0 22) 0) 0) = true := by
  decide +kernel

theorem ch36409_e14_neg2 : (!cmOK16 16384 (slEm 0 132) 128 (slE0 0) (slE0 1) (slE0 3)
    (kyL (slE0 8) 0) (Nat.land (slE0 10) (Nat.sub (Nat.shiftLeft 1 (Nat.mul 16 20)) 65536))
    (slE0 12) 20) = true := by
  decide +kernel

end Certificates.KernelTower
