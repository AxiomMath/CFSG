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
  hcOK16 16384 (slEm a g) 128 (D 4) && treeB 16384 4 (slEm a g) (D 5) (D 7) &&
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

@[expose] noncomputable def ch36409_iv3B (n : Nat) (iv : Nat → Nat) (K0 K1 K2 : Nat)
    (c0 c1 r0 r1 : Nat → Bool) : Bool :=
  allB n fun u => (!Nat.beq (iv u) K0 || c0 u) && (!Nat.beq (iv u) K1 || c1 u) &&
    (!Nat.beq (iv u) K2 || (r0 u && r1 u))

@[expose] noncomputable def ch36409_vr (D : Nat → Nat) (a g n1 r2 u : Nat) : Bool :=
  !Nat.beq (pvOf16 (slEm a g) (D 0) (D 1) (D 3) 128 (l16 (D 14) (e14P1 (D 16) r2)) u)
      (pvL (D 9) 1) ||
    (!Nat.beq (pvOf16 (slEm a g) (D 0) (D 1) (D 3) 128 (e14P2 (D 16) r2) u) (pvL (D 9) 2) ||
      e14Sp (slEm a g) (D 5) (D 7) (e14Im 128 (l16 (D 14) (e14P1 (D 16) r2)) (e14P2 (D 16) r2) u) 16
        (l16 (D (Nat.add 17 (Nat.add n1 r2))) u))

@[expose] noncomputable def e14CL (D : Nat → Nat) (a g c1 c2 n1 : Nat) : Bool :=
  ch36409_iv3B 16384 (ivOf (slEm a g) (D 0) (D 1) (D 3) 128) (kyL (D 8) 0) (kyL (D 8) 1)
    (kyL (D 8) 2) (fun u => Nat.blt (rkL (D 12) u) c1 && Nat.beq (l16 (D 10) (rkL (D 12) u)) u)
    (fun u => Nat.blt (rkL (D 13) u) c2 && Nat.beq (l16 (D 11) (rkL (D 13) u)) u)
    (ch36409_vr D a g n1 0) (ch36409_vr D a g n1 1)

theorem ch36409_b3 {a0 a1 a2 c0 c1 r0 r1 : Bool}
    (h : ((!a0 || c0) && (!a1 || c1) && (!a2 || (r0 && r1))) = true) :
    (!a0 || c0) = true ∧ (!a1 || c1) = true ∧ (!a2 || r0) = true ∧ (!a2 || r1) = true := by
  revert h
  cases a0 <;> cases a1 <;> cases a2 <;> cases c0 <;> cases c1 <;> cases r0 <;> cases r1 <;> decide

theorem ch36409_iv3B_parts {n : Nat} {iv : Nat → Nat} {K0 K1 K2 : Nat} {c0 c1 r0 r1 : Nat → Bool}
    (h : ch36409_iv3B n iv K0 K1 K2 c0 c1 r0 r1 = true) :
    allB n (fun u => !Nat.beq (iv u) K0 || c0 u) = true ∧
      allB n (fun u => !Nat.beq (iv u) K1 || c1 u) = true ∧
      allB n (fun u => !Nat.beq (iv u) K2 || r0 u) = true ∧
      allB n (fun u => !Nat.beq (iv u) K2 || r1 u) = true := by
  have h' := allB_true_iff.1 h
  exact ⟨allB_true_iff.2 fun u hu => (ch36409_b3 (h' u hu)).1,
    allB_true_iff.2 fun u hu => (ch36409_b3 (h' u hu)).2.1,
    allB_true_iff.2 fun u hu => (ch36409_b3 (h' u hu)).2.2.1,
    allB_true_iff.2 fun u hu => (ch36409_b3 (h' u hu)).2.2.2⟩

theorem ch36409_cm_of {D : Nat → Nat} {a g c1 c2 n1 : Nat} (h : e14CL D a g c1 c2 n1 = true) :
    e14Cm D a g c1 c2 = true := by
  have p := ch36409_iv3B_parts h
  rw [e14Cm, Bool.and_eq_true, cmOK16, cmOK16]
  exact ⟨p.1, p.2.1⟩

theorem ch36409_l3_of {D : Nat → Nat} {a g c1 c2 n1 : Nat} (h : e14CL D a g c1 c2 n1 = true) :
    e14L3 D a g n1 0 = true ∧ e14L3 D a g n1 1 = true := by
  have p := ch36409_iv3B_parts h
  have h0 := allB_true_iff.1 p.2.2.1
  have h1 := allB_true_iff.1 p.2.2.2
  rw [e14L3, e14L3, e14Lvl3, e14Lvl3, allB_true_iff, allB_true_iff]
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · rw [e14V, Bool.or_assoc, Bool.or_assoc]
    exact h0 v hv
  · rw [e14V, Bool.or_assoc, Bool.or_assoc]
    exact h1 v hv

@[expose] noncomputable def ch36409_ordS (n : Nat) (mul : Nat → Nat → Nat) (OT c : Nat) : Bool :=
  Nat.beq c 0 && Nat.beq (oe OT c) 0 ||
    !Nat.beq c 0 && Nat.blt 0 (oe OT c) && Nat.blt (mul c c) n &&
      Nat.beq (oe OT (mul c c)) (Nat.sub (oe OT c) 1)

theorem ch36409_sqK_succ (mul : Nat → Nat → Nat) (x k : Nat) :
    sqK mul x (k + 1) = sqK mul (mul x x) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change mul (sqK mul x (k + 1)) (sqK mul x (k + 1)) =
      mul (sqK mul (mul x x) k) (sqK mul (mul x x) k)
    rw [ih]

theorem ch36409_ordOK_of {n : Nat} {mul : Nat → Nat → Nat} {OT : Nat}
    (h : allB n (ch36409_ordS n mul OT) = true) : ordOK n mul OT = true := by
  have key : ∀ e c, c < n → oe OT c = e → ordC mul c e = true := by
    intro e
    induction e with
    | zero =>
      intro c hc he
      have hs := allB_true_iff.1 h c hc
      rw [ch36409_ordS, he] at hs
      cases hc0 : Nat.beq c 0
      · rw [hc0] at hs
        exact absurd hs Bool.false_ne_true
      · rw [Nat.eq_of_beq_eq_true hc0]
        rfl
    | succ e ih =>
      intro c hc he
      have hs := allB_true_iff.1 h c hc
      rw [ch36409_ordS, he] at hs
      cases hc0 : Nat.beq c 0
      · rw [hc0, Bool.false_and, Bool.false_or, Bool.and_eq_true, Bool.and_eq_true] at hs
        have hc' : mul c c < n := Nat.le_of_ble_eq_true hs.1.2
        have hoe : oe OT (mul c c) = e :=
          (Nat.eq_of_beq_eq_true hs.2).trans (Nat.add_sub_cancel e 1)
        have ihc := ih (mul c c) hc' hoe
        rw [ordC, Bool.and_eq_true] at ihc
        rw [ordC, ch36409_sqK_succ, Bool.and_eq_true]
        refine ⟨ihc.1, ?_⟩
        cases e with
        | zero =>
          change (false && Nat.beq c 0 || true && !Nat.beq c 0) = true
          rw [hc0]
          rfl
        | succ k =>
          have h2 := ihc.2
          change (false && Nat.beq (mul c c) 0 || true && !Nat.beq (sqK mul (mul c c) k) 0) =
            true at h2
          change (false && Nat.beq c 0 || true && !Nat.beq (sqK mul c (k + 1)) 0) = true
          rw [ch36409_sqK_succ]
          rw [Bool.false_and, Bool.false_or, Bool.true_and] at h2 ⊢
          exact h2
      · rw [hc0] at hs
        exact absurd hs Bool.false_ne_true
  rw [ordOK, allB_true_iff]
  exact fun c hc => key _ c hc rfl

@[expose] def sl4 (e x0 x1 x2 x3 : Nat) : Nat :=
  cond (Nat.beq e 0) x0 (cond (Nat.beq e 1) x1 (cond (Nat.beq e 2) x2 x3))

@[expose] noncomputable def slED (e : Nat) : Nat → Nat :=
  cond (Nat.beq e 0) slE0 (cond (Nat.beq e 1) slE1 (cond (Nat.beq e 2) slE2 slE3))

@[expose] def slEA (e : Nat) : Nat := sl4 e 0 2 9 11

@[expose] def slEG (e : Nat) : Nat := sl4 e 132 132 0 0

@[expose] def slEN (e : Nat) : Nat := sl4 e 100 94 100 94

@[expose] noncomputable def slEM (e : Nat) : Nat → Nat → Nat := slEm (slEA e) (slEG e)

@[expose] noncomputable def ch36409_eordC (q : Nat) : Bool :=
  chunkB (ch36409_ordS 16384 (slEM (q / 32)) (slED (q / 32) 0)) (q % 32)

@[expose] noncomputable def ch36409_elabC (q : Nat) : Bool :=
  chunkB (labC16 4 (slEM (q / 32)) (slED (q / 32) 5) (slED (q / 32) 6) (slED (q / 32) 1)
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
  have hC : ∀ q < 32, chunkB (ch36409_ordS 16384 (slEM e) (slED e 0)) q = true := by
    intro q hq
    have h := ch36409_eordC_all (32 * e + q) (ch36409_chunk_lt he hq)
    rw [ch36409_eordC, ch36409_chunk_div hq, ch36409_chunk_mod hq] at h
    exact h
  rw [e14Ord]
  exact ch36409_ordOK_of (allB_of_chunks (m := 32) hC)

theorem ch36409_elab_lt (e : Nat) (he : e < 4) :
    e14Lab (slED e) (slEA e) (slEG e) (slEN e) = true := by
  have hC : ∀ q < 32, chunkB (labC16 4 (slEM e) (slED e 5) (slED e 6) (slED e 1)
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
theorem ch36409_e0_cl : e14CL slE0 0 132 20 32 5 = true := by decide +kernel
theorem ch36409_e0_cm : e14Cm slE0 0 132 20 32 = true := ch36409_cm_of ch36409_e0_cl
theorem ch36409_e0_l12 : e14L12 slE0 0 132 20 32 5 2 = true := by decide +kernel
theorem ch36409_e0_l30 : e14L3 slE0 0 132 5 0 = true := (ch36409_l3_of ch36409_e0_cl).1
theorem ch36409_e0_l31 : e14L3 slE0 0 132 5 1 = true := (ch36409_l3_of ch36409_e0_cl).2

theorem ch36409_e1_ord : e14Ord slE1 2 132 = true := ch36409_eord_lt 1 (by decide)
theorem ch36409_e1_lab : e14Lab slE1 2 132 94 = true := ch36409_elab_lt 1 (by decide)
theorem ch36409_e1_h : e14H slE1 2 132 = true := by decide +kernel
theorem ch36409_e1_cl : e14CL slE1 2 132 16 32 3 = true := by decide +kernel
theorem ch36409_e1_cm : e14Cm slE1 2 132 16 32 = true := ch36409_cm_of ch36409_e1_cl
theorem ch36409_e1_l12 : e14L12 slE1 2 132 16 32 3 2 = true := by decide +kernel
theorem ch36409_e1_l30 : e14L3 slE1 2 132 3 0 = true := (ch36409_l3_of ch36409_e1_cl).1
theorem ch36409_e1_l31 : e14L3 slE1 2 132 3 1 = true := (ch36409_l3_of ch36409_e1_cl).2

theorem ch36409_e2_ord : e14Ord slE2 9 0 = true := ch36409_eord_lt 2 (by decide)
theorem ch36409_e2_lab : e14Lab slE2 9 0 100 = true := ch36409_elab_lt 2 (by decide)
theorem ch36409_e2_h : e14H slE2 9 0 = true := by decide +kernel
theorem ch36409_e2_cl : e14CL slE2 9 0 20 32 5 = true := by decide +kernel
theorem ch36409_e2_cm : e14Cm slE2 9 0 20 32 = true := ch36409_cm_of ch36409_e2_cl
theorem ch36409_e2_l12 : e14L12 slE2 9 0 20 32 5 2 = true := by decide +kernel
theorem ch36409_e2_l30 : e14L3 slE2 9 0 5 0 = true := (ch36409_l3_of ch36409_e2_cl).1
theorem ch36409_e2_l31 : e14L3 slE2 9 0 5 1 = true := (ch36409_l3_of ch36409_e2_cl).2

theorem ch36409_e3_ord : e14Ord slE3 11 0 = true := ch36409_eord_lt 3 (by decide)
theorem ch36409_e3_lab : e14Lab slE3 11 0 94 = true := ch36409_elab_lt 3 (by decide)
theorem ch36409_e3_h : e14H slE3 11 0 = true := by decide +kernel
theorem ch36409_e3_cl : e14CL slE3 11 0 16 32 3 = true := by decide +kernel
theorem ch36409_e3_cm : e14Cm slE3 11 0 16 32 = true := ch36409_cm_of ch36409_e3_cl
theorem ch36409_e3_l12 : e14L12 slE3 11 0 16 32 3 2 = true := by decide +kernel
theorem ch36409_e3_l30 : e14L3 slE3 11 0 3 0 = true := (ch36409_l3_of ch36409_e3_cl).1
theorem ch36409_e3_l31 : e14L3 slE3 11 0 3 1 = true := (ch36409_l3_of ch36409_e3_cl).2

theorem ch36409_e14_neg : (!e14Lvl3 16384 (slEm 0 132) (slE0 0) (slE0 1) (slE0 3) 128 (slE0 5)
    (slE0 7) 16 (slE0 14) (slE0 16) (kyL (slE0 8) 2) (pvL (slE0 9) 1) (pvL (slE0 9) 2)
    (Nat.land (slE0 22) 0) 0) = true := by
  decide +kernel

theorem ch36409_e14_neg2 : (!cmOK16 16384 (slEm 0 132) 128 (slE0 0) (slE0 1) (slE0 3)
    (kyL (slE0 8) 0) (Nat.land (slE0 10) (Nat.sub (Nat.shiftLeft 1 (Nat.mul 16 20)) 65536))
    (slE0 12) 20) = true := by
  decide +kernel

end Certificates.KernelTower
