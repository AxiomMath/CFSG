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

@[expose] noncomputable def ch36408_ordS (n : Nat) (mul : Nat → Nat → Nat) (OT c : Nat) : Bool :=
  Nat.beq c 0 && Nat.beq (oe OT c) 0 ||
    !Nat.beq c 0 && Nat.blt 0 (oe OT c) && Nat.blt (mul c c) n &&
      Nat.beq (oe OT (mul c c)) (Nat.sub (oe OT c) 1)

theorem ch36408_sqK_succ (mul : Nat → Nat → Nat) (x k : Nat) :
    sqK mul x (k + 1) = sqK mul (mul x x) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change mul (sqK mul x (k + 1)) (sqK mul x (k + 1)) =
      mul (sqK mul (mul x x) k) (sqK mul (mul x x) k)
    rw [ih]

theorem ch36408_ordOK_of {n : Nat} {mul : Nat → Nat → Nat} {OT : Nat}
    (h : allB n (ch36408_ordS n mul OT) = true) : ordOK n mul OT = true := by
  have key : ∀ e c, c < n → oe OT c = e → ordC mul c e = true := by
    intro e
    induction e with
    | zero =>
      intro c hc he
      have hs := allB_true_iff.1 h c hc
      rw [ch36408_ordS, he] at hs
      cases hc0 : Nat.beq c 0
      · rw [hc0] at hs
        exact absurd hs Bool.false_ne_true
      · rw [Nat.eq_of_beq_eq_true hc0]
        rfl
    | succ e ih =>
      intro c hc he
      have hs := allB_true_iff.1 h c hc
      rw [ch36408_ordS, he] at hs
      cases hc0 : Nat.beq c 0
      · rw [hc0, Bool.false_and, Bool.false_or, Bool.and_eq_true, Bool.and_eq_true] at hs
        have hc' : mul c c < n := Nat.le_of_ble_eq_true hs.1.2
        have hoe : oe OT (mul c c) = e :=
          (Nat.eq_of_beq_eq_true hs.2).trans (Nat.add_sub_cancel e 1)
        have ihc := ih (mul c c) hc' hoe
        rw [ordC, Bool.and_eq_true] at ihc
        rw [ordC, ch36408_sqK_succ, Bool.and_eq_true]
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
          rw [ch36408_sqK_succ]
          rw [Bool.false_and, Bool.false_or, Bool.true_and] at h2 ⊢
          exact h2
      · rw [hc0] at hs
        exact absurd hs Bool.false_ne_true
  rw [ordOK, allB_true_iff]
  exact fun c hc => key _ c hc rfl

@[expose] noncomputable def ch36408_eordC (q : Nat) : Bool :=
  chunkB (ch36408_ordS 16384 (wrEM (q / 32)) (wrED (q / 32) 0)) (q % 32)

@[expose] noncomputable def wrLcP (e c : Nat) : Bool :=
  Nat.blt (lbL (wrED e 1) c) (wrEP e 2) &&
    (Nat.blt (lbG16 (wrED e 1) c) 4 || Nat.beq c (l16 (wrED e 2) (lbL (wrED e 1) c)))

@[expose] noncomputable def wrLtT (e c : Nat) : Bool :=
  !Nat.blt (lbG16 (wrED e 1) c) 4 ||
    (fun y => Nat.beq (lbL (wrED e 1) y) (lbL (wrED e 1) c) &&
        Nat.blt (lbD16 (wrED e 1) y) (lbD16 (wrED e 1) c))
      (wrEM e (wrEM e (l16 (wrED e 5) (lbG16 (wrED e 1) c)) c)
        (l16 (wrED e 6) (lbG16 (wrED e 1) c)))

theorem ch36408_and_l {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  revert h
  cases a <;> cases b <;> decide

@[expose] def wrPi (t : Nat) : Nat := Nat.add (Nat.mul 2 (Nat.shiftRight t 7)) (Nat.land t 1)

@[expose] noncomputable def wrTT (e l : Nat) : Nat := wrCT (Nat.add (Nat.mul 256 e) l)

@[expose] noncomputable def wrCtR (e r T cz : Nat) : Bool :=
  Nat.ble 16384 (Nat.mul (Nat.mul (cntB 64 fun v =>
      Nat.beq (wrEM e (Nat.mul 2 v) r) (wrEM e r (Nat.mul 2 v))) (l16 T 0)) cz) &&
    allB (l16 T 0) (fun j => Nat.blt (l16 T (Nat.succ j)) 16384 &&
      Nat.beq (wrEM e (l16 T (Nat.succ j)) r) (wrEM e r (l16 T (Nat.succ j)))) &&
    allB (Nat.sub (l16 T 0) 1) (fun j =>
      Nat.blt (wrPi (l16 T (Nat.succ j))) (wrPi (l16 T (Nat.succ (Nat.succ j)))))

@[expose] noncomputable def wrCtB (e l : Nat) : Bool :=
  wrCtR e (l16 (wrED e 2) l) (wrTT e l) (lane (wrED e 3) 15 32767 l)

@[expose] noncomputable def ch36408_ectC (q : Nat) : Bool :=
  allFrom (Nat.mul 8 (q % 32)) 8 fun l => Nat.ble (wrEP (q / 32) 2) l || wrCtB (q / 32) l

@[expose] noncomputable def ch36408_echS (e : Nat) : Bool :=
  (allB 16384 fun c => Nat.beq (bit (wrX e) c)
      (Nat.xor (bit (wrX e) (Nat.mul 128 (Nat.shiftRight c 7)))
        (Nat.mul (bit (wrX e) 1) (Nat.land c 1)))) &&
    (allB 128 fun s => allB 128 fun t =>
      Nat.beq (bit (wrX e) (Nat.mul 128 (lane wrSM 7 127 (Nat.add (Nat.mul 128 s) t))))
        (Nat.xor (bit (wrX e) (Nat.mul 128 s)) (bit (wrX e) (Nat.mul 128 t)))) &&
    (allB 8192 fun y => Nat.blt (l16 (wrA (Nat.add (wrEP e 0) 2)) y) 8192 &&
      Nat.beq (bit (wrX e) (Nat.mul 128 (Nat.shiftRight (l16 (wrA (Nat.add (wrEP e 0) 2)) y) 6)))
        (bit (wrX e) (Nat.mul 128 (Nat.shiftRight y 6)))) &&
    Nat.blt (wrEP e 1) 8192 &&
    Nat.beq (bit (wrX e) (Nat.mul 128 (Nat.shiftRight (wrEP e 1) 6))) 0

theorem ch36408_sm0 : allB 128 (fun s => Nat.beq (lane wrSM 7 127 s) s) = true := by
  decide +kernel

theorem ch36408_enl : allB 12 (fun e => Nat.ble (wrEP e 2) 256) = true := by
  decide +kernel

@[expose] noncomputable def ch36408_elabH (e : Nat) : Bool :=
  allB 4 (fun i => Nat.blt (l16 (wrED e 6) i) 16384 &&
      Nat.beq (wrEM e (l16 (wrED e 5) i) (l16 (wrED e 6) i)) 0) &&
    allB (wrEP e 2) (fun l => Nat.blt (l16 (wrED e 2) l) 16384 &&
      Nat.beq (lbL (wrED e 1) (l16 (wrED e 2) l)) l) &&
    czOK16 16384 (wrED e 1) (wrED e 3)

@[expose] noncomputable def ch36408_echiH (e : Nat) : Bool :=
  Nat.beq (bit (wrX e) 0) 0 && Nat.beq (bit (wrX e) 128) 1 &&
    Nat.beq (bit (wrX e) (l16 (wrED e 5) 0)) 1

@[expose] noncomputable def wrCmK (e u k : Nat) : Bool :=
  (!Nat.beq k (kyL (wrED e 8) 0) ||
      Nat.blt (rkL (wrED e 12) u) (wrEP e 3) && Nat.beq (l16 (wrED e 10) (rkL (wrED e 12) u)) u) &&
    (!Nat.beq k (kyL (wrED e 8) 1) ||
      Nat.blt (rkL (wrED e 13) u) (wrEP e 4) && Nat.beq (l16 (wrED e 11) (rkL (wrED e 13) u)) u) &&
    (!Nat.beq k (kyL (wrED e 8) 2) ||
      Nat.blt (rkL (wrED e 18) u) (wrEP e 5) && Nat.beq (l16 (wrED e 17) (rkL (wrED e 18) u)) u)

@[expose] noncomputable def wrCmU (e u : Nat) : Bool :=
  wrCmK e u (ivOf (wrEM e) (wrED e 0) (wrED e 1) (wrED e 3) 128 u)

@[expose] noncomputable def wrEhU (e c : Nat) : Bool :=
  (!Nat.beq (wrEM e c 128) (wrEM e 128 c) || bitS (hmL (wrED e 4) 256) c) &&
    (Nat.beq c 0 || (Nat.blt (ptGi (wrED e 7) c) 4 && Nat.blt (ptPar (wrED e 7) c) 16384 &&
      Nat.blt (ptDep (wrED e 7) (ptPar (wrED e 7) c)) (ptDep (wrED e 7) c) &&
      Nat.beq (wrEM e (l16 (wrED e 5) (ptGi (wrED e 7) c)) (ptPar (wrED e 7) c)) c))

@[expose] noncomputable def wrHcZ (e c y z : Nat) : Bool :=
  (!Nat.beq y z || bitS (hmL (wrED e 4) 256) c) &&
    (Nat.beq c 0 || (Nat.blt (ptGi (wrED e 7) c) 4 && Nat.blt (ptPar (wrED e 7) c) 16384 &&
      Nat.blt (ptDep (wrED e 7) (ptPar (wrED e 7) c)) (ptDep (wrED e 7) c) &&
      Nat.beq (wrEM e (l16 (wrED e 5) (ptGi (wrED e 7) c)) (ptPar (wrED e 7) c)) c)) &&
    wrCmK e c (Nat.add (ocOf (wrED e 0) (wrED e 1) (wrED e 3) c)
      (Nat.shiftLeft (ocOf (wrED e 0) (wrED e 1) (wrED e 3) y) 17))

@[expose] noncomputable def wrHcU (e c : Nat) : Bool := wrHcZ e c (wrEM e c 128) (wrEM e 128 c)

theorem ch36408_hc_parts {e c : Nat} (h : wrHcU e c = true) :
    wrEhU e c = true ∧ wrCmU e c = true :=
  ch36408_and_l h

@[expose] noncomputable def wrLhU (e c : Nat) : Bool := (wrLcP e c && wrLtT e c) && wrHcU e c

@[expose] noncomputable def ch36408_elhC (q : Nat) : Bool :=
  allFrom (Nat.mul 128 (q % 128)) 128 (wrLhU (q / 128))

theorem ch36408_of_blocks {p : Nat → Bool}
    (h : ∀ q < 128, allFrom (Nat.mul 128 q) 128 p = true) : ∀ c < 16384, p c = true := by
  intro c hc
  have h1 := allB_true_iff.1 (h (c / 128) (by omega)) (c % 128) (Nat.mod_lt _ (by decide))
  have h2 : p (Nat.add (Nat.mul 128 (c / 128)) (c % 128)) = true := h1
  have hc' : Nat.add (Nat.mul 128 (c / 128)) (c % 128) = c := Nat.div_add_mod c 128
  rw [hc'] at h2
  exact h2

@[expose] noncomputable def ch36408_ehH (e : Nat) : Bool :=
  allB 256 (fun j => Nat.blt (l16 (wrED e 4) j) 16384 &&
      Nat.beq (wrEM e (l16 (wrED e 4) j) 128) (wrEM e 128 (l16 (wrED e 4) j))) &&
    allB 255 (fun j => Nat.blt (l16 (wrED e 4) j) (l16 (wrED e 4) (Nat.succ j))) &&
    allB 4 (fun i => Nat.blt (l16 (wrED e 5) i) 16384) &&
    kyOK (wrEM e) (wrED e 0) (wrED e 1) (wrED e 3) (wrED e 5) (wrED e 8) (wrED e 9)

#kc_each ch36408_eordC 0 384
#kc_each ch36408_elhC 0 1536
#kc_each ch36408_ectC 0 384
#kc_each ch36408_echS 0 12
#kc_each ch36408_elabH 0 12
#kc_each ch36408_echiH 0 12
#kc_each ch36408_ehH 0 12

#kc_forall_tree ch36408_eordC_all (fun q => ch36408_eordC q = true) 384
  Certificates.KernelTower.ch36408_eordC
#kc_forall_tree ch36408_elhC_all (fun q => ch36408_elhC q = true) 1536
  Certificates.KernelTower.ch36408_elhC
#kc_forall_tree ch36408_ectC_all (fun q => ch36408_ectC q = true) 384
  Certificates.KernelTower.ch36408_ectC
#kc_forall_tree ch36408_echS_all (fun e => ch36408_echS e = true) 12
  Certificates.KernelTower.ch36408_echS
#kc_forall_tree ch36408_elabH_all (fun e => ch36408_elabH e = true) 12
  Certificates.KernelTower.ch36408_elabH
#kc_forall_tree ch36408_echiH_all (fun e => ch36408_echiH e = true) 12
  Certificates.KernelTower.ch36408_echiH
#kc_forall_tree ch36408_ehH_all (fun e => ch36408_ehH e = true) 12
  Certificates.KernelTower.ch36408_ehH

theorem chunk_div {e q : Nat} (hq : q < 32) : (32 * e + q) / 32 = e := by omega

theorem chunk_mod {e q : Nat} (hq : q < 32) : (32 * e + q) % 32 = q := by omega

theorem chunk_lt {e q : Nat} (he : e < 12) (hq : q < 32) : 32 * e + q < 384 := by omega

theorem ch36408_eord_lt (e : Nat) (he : e < 12) : ch36408_eord e = true := by
  have hC : ∀ q < 32, chunkB (ch36408_ordS 16384 (wrEM e) (wrED e 0)) q = true := by
    intro q hq
    have h := ch36408_eordC_all (32 * e + q) (chunk_lt he hq)
    rw [ch36408_eordC, chunk_div hq, chunk_mod hq] at h
    exact h
  rw [ch36408_eord]
  exact ch36408_ordOK_of (allB_of_chunks (m := 32) hC)

theorem ch36408_lhU_lt (e : Nat) (he : e < 12) : ∀ c < 16384, wrLhU e c = true := by
  refine ch36408_of_blocks fun q hq => ?_
  have hl : 128 * e + q < 1536 := by omega
  have h := ch36408_elhC_all (128 * e + q) hl
  have hd : (128 * e + q) / 128 = e := by omega
  have hm : (128 * e + q) % 128 = q := by omega
  rw [ch36408_elhC, hd, hm] at h
  exact h

theorem ch36408_lt_lt (e : Nat) (he : e < 12) :
    ∀ c < 16384, (wrLcP e c && wrLtT e c) = true := fun c hc =>
  (ch36408_and_l (ch36408_lhU_lt e he c hc)).1

theorem ch36408_hcU_lt (e : Nat) (he : e < 12) : ∀ c < 16384, wrHcU e c = true := fun c hc =>
  (ch36408_and_l (ch36408_lhU_lt e he c hc)).2

theorem ch36408_ct_lt (e : Nat) (he : e < 12) {l : Nat} (hl : l < wrEP e 2) :
    wrCtB e l = true := by
  have hn : wrEP e 2 ≤ 256 := Nat.le_of_ble_eq_true (allB_true_iff.1 ch36408_enl e he)
  have hq : l / 8 < 32 := by omega
  have h := ch36408_ectC_all (32 * e + l / 8) (chunk_lt he hq)
  rw [ch36408_ectC, chunk_div hq, chunk_mod hq] at h
  have h2 : (Nat.ble (wrEP e 2) (Nat.add (Nat.mul 8 (l / 8)) (l % 8)) ||
      wrCtB e (Nat.add (Nat.mul 8 (l / 8)) (l % 8))) = true :=
    allB_true_iff.1 h (l % 8) (Nat.mod_lt _ (by decide))
  have e1 : Nat.add (Nat.mul 8 (l / 8)) (l % 8) = l := Nat.div_add_mod l 8
  rw [e1, Bool.or_eq_true] at h2
  rcases h2 with h2 | h2
  · exact absurd (Nat.le_of_ble_eq_true h2) (by omega)
  · exact h2

theorem ch36408_ecm_lt (e : Nat) (he : e < 12) : ch36408_ecm e = true := by
  have hA : ∀ u < 16384, wrCmU e u = true := fun u hu =>
    (ch36408_hc_parts (ch36408_hcU_lt e he u hu)).2
  simp only [ch36408_ecm, cmOK16, Bool.and_eq_true]
  refine ⟨⟨allB_true_iff.2 fun u hu => ?_, allB_true_iff.2 fun u hu => ?_⟩,
    allB_true_iff.2 fun u hu => ?_⟩
  · have h := hA u (by omega)
    simp only [wrCmU, wrCmK, Bool.and_eq_true] at h
    exact h.1.1
  · have h := hA u (by omega)
    simp only [wrCmU, wrCmK, Bool.and_eq_true] at h
    exact h.1.2
  · have h := hA u (by omega)
    simp only [wrCmU, wrCmK, Bool.and_eq_true] at h
    exact h.2

theorem ch36408_ehU_lt (e : Nat) (he : e < 12) : ∀ c < 16384, wrEhU e c = true := fun c hc =>
  (ch36408_hc_parts (ch36408_hcU_lt e he c hc)).1

#kc_each_by ch36408_eord 0 12 ch36408_eord_lt
#kc_each_by ch36408_ecm 0 12 ch36408_ecm_lt
#kc_each ch36408_el12 0 12
#kc_each ch36408_el3 0 12
#kc_each ch36408_efam 0 12

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
