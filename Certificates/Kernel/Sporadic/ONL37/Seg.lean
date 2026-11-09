module

public import Certificates.Kernel.Sporadic.ONL37.Defs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatVal

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CertificateChecks.KernelSpor.ONL37

theorem strictB_eq' (y : Nat) (k : Nat → Bool) : CFSG.KC.Enum.strictB y k = k y := by
  cases y <;> rfl

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : CFSG.KC.Enum.strictN y k = k y := by
  cases y <;> rfl

theorem wordK_cons' (mul : Nat → Nat → Nat) (L : Int → Nat) (z : Int) (u : List Int) (acc : Nat) :
    CFSG.KS.ONC.wordK mul L (z :: u) acc = CFSG.KS.ONC.wordK mul L u (mul acc (L z)) :=
  strictN_eq' (mul acc (L z)) _

theorem wordK_append' (mul : Nat → Nat → Nat) (L : Int → Nat) (u v : List Int) :
    ∀ acc, CFSG.KS.ONC.wordK mul L (u ++ v) acc =
      CFSG.KS.ONC.wordK mul L v (CFSG.KS.ONC.wordK mul L u acc) := by
  induction u with
  | nil => intro acc; rfl
  | cons z u ih => intro acc; rw [List.cons_append, wordK_cons', wordK_cons', ih]

theorem wordK_seg0 (mul : Nat → Nat → Nat) (L : Int → Nat) (W : List Int) (n acc V : Nat)
    (h : Nat.beq (CFSG.KS.ONC.wordK mul L (List.take n W) acc) V = true) :
    CFSG.KS.ONC.wordK mul L W acc = CFSG.KS.ONC.wordK mul L (List.drop n W) V := by
  conv => lhs; rw [← List.take_append_drop n W]
  rw [wordK_append', Nat.eq_of_beq_eq_true h]

theorem wordK_seg (mul : Nat → Nat → Nat) (L : Int → Nat) (W : List Int) (m n k acc V : Nat)
    (hk : m + n = k) (h : Nat.beq (CFSG.KS.ONC.wordK mul L (List.take n (List.drop m W)) acc) V = true) :
    CFSG.KS.ONC.wordK mul L (List.drop m W) acc = CFSG.KS.ONC.wordK mul L (List.drop k W) V := by
  rw [wordK_seg0 mul L (List.drop m W) n acc V h, List.drop_drop, hk]

theorem beq_of_eq' {X Y Z : Nat} (e : X = Y) (h : Nat.beq Y Z = true) : Nat.beq X Z = true :=
  e ▸ h

section
open CFSG.KC.Enum CFSG.KS CFSG.KC.Ord CFSG.RankThree.Native.ONTriple

@[expose] noncomputable def chunkA (CS0 DS0 L0 H0 CM0 RM0 ONE0 : Nat)
    (bat : Nat → Nat → (Nat → Nat) → Nat → Nat → Nat)
    (m3 : Nat → Nat → Nat → Nat → Nat → Nat → Nat)
    (FA FB : Nat → Nat) (w : List Int) (pre post : Nat) : Bool :=
  strictB CS0 fun cs => strictB DS0 fun ds => strictB L0 fun L => strictB H0 fun H =>
  strictB CM0 fun cm => strictB RM0 fun rm => strictB ONE0 fun one =>
  strictB (bat cs ds FA (nat_lit 0) (nat_lit 154)) fun a =>
  strictB (bat cs ds FB (nat_lit 0) (nat_lit 154)) fun b =>
  strictB (m3 L H cm rm (m3 L H cm rm b b) b) fun bi =>
    bAnd(Nat.beq (m3 L H cm rm a a) one, bAnd(Nat.beq (m3 L H cm rm b bi) one,
      Nat.beq (CFSG.KS.ONC.wordK (m3 L H cm rm) (CFSG.KS.ONC.seedL a a b bi) w pre) post))

end

theorem chunkK_eqA (FA FB : Nat → Nat) (w : List Int) (pre post : Nat) :
    CFSG.KS.ONC.chunkK FA FB w pre post =
      chunkA CFSG.KS.ONC.CS CFSG.KS.ONC.DS CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM
        CFSG.KS.ONC.RM CFSG.KS.ONC.ONE CFSG.KS.ONC.batK CFSG.KS.ONC.mul3 FA FB w pre post := rfl

theorem chunkA_of {CS0 DS0 L0 H0 CM0 RM0 ONE0 : Nat} {bat : Nat → Nat → (Nat → Nat) → Nat → Nat → Nat}
    {m3 : Nat → Nat → Nat → Nat → Nat → Nat → Nat} {FA FB : Nat → Nat} {w : List Int}
    {pre post A B BI : Nat}
    (hA : Nat.beq (bat CS0 DS0 FA (nat_lit 0) (nat_lit 154)) A = true)
    (hB : Nat.beq (bat CS0 DS0 FB (nat_lit 0) (nat_lit 154)) B = true)
    (hBI : Nat.beq (m3 L0 H0 CM0 RM0 (m3 L0 H0 CM0 RM0 B B) B) BI = true)
    (ha : Nat.beq (m3 L0 H0 CM0 RM0 A A) ONE0 = true)
    (hb : Nat.beq (m3 L0 H0 CM0 RM0 B BI) ONE0 = true)
    (hw : Nat.beq (CFSG.KS.ONC.wordK (m3 L0 H0 CM0 RM0) (CFSG.KS.ONC.seedL A A B BI) w pre) post =
      true) :
    chunkA CS0 DS0 L0 H0 CM0 RM0 ONE0 bat m3 FA FB w pre post = true := by
  unfold chunkA
  simp only [strictB_eq']
  rw [Nat.eq_of_beq_eq_true hA, Nat.eq_of_beq_eq_true hB, Nat.eq_of_beq_eq_true hBI, ha, hb, hw]

theorem chunkK_of {FA FB : Nat → Nat} {w : List Int} {pre post A B BI : Nat}
    (hA : Nat.beq (CFSG.KS.ONC.batK CFSG.KS.ONC.CS CFSG.KS.ONC.DS FA (nat_lit 0) (nat_lit 154)) A = true)
    (hB : Nat.beq (CFSG.KS.ONC.batK CFSG.KS.ONC.CS CFSG.KS.ONC.DS FB (nat_lit 0) (nat_lit 154)) B = true)
    (hBI : Nat.beq (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM
      (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM B B) B) BI = true)
    (ha : Nat.beq (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM A A)
      CFSG.KS.ONC.ONE = true)
    (hb : Nat.beq (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM B BI)
      CFSG.KS.ONC.ONE = true)
    (hw : Nat.beq (CFSG.KS.ONC.wordK
      (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM)
      (CFSG.KS.ONC.seedL A A B BI) w pre) post = true) :
    CFSG.KS.ONC.chunkK FA FB w pre post = true :=
  (chunkK_eqA FA FB w pre post).trans (chunkA_of hA hB hBI ha hb hw)

open CFSG.KS.ONC in
#kc_natval SA := batK CS DS FA (nat_lit 0) (nat_lit 154)
open CFSG.KS.ONC in
#kc_natval SB := batK CS DS FB (nat_lit 0) (nat_lit 154)
open CFSG.KS.ONC in
#kc_natval SBI := mul3 LL HH CM RM (mul3 LL HH CM RM SB SB) SB

theorem sA : Nat.beq (CFSG.KS.ONC.batK CFSG.KS.ONC.CS CFSG.KS.ONC.DS FA (nat_lit 0) (nat_lit 154)) SA =
    true := by
  quickRfl

theorem sB : Nat.beq (CFSG.KS.ONC.batK CFSG.KS.ONC.CS CFSG.KS.ONC.DS FB (nat_lit 0) (nat_lit 154)) SB =
    true := by
  quickRfl

theorem sBI : Nat.beq (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM
    (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM SB SB) SB) SBI = true := by
  quickRfl

theorem sa1 : Nat.beq (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM SA SA)
    CFSG.KS.ONC.ONE = true := by
  quickRfl

theorem sb1 : Nat.beq (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM SB SBI)
    CFSG.KS.ONC.ONE = true := by
  quickRfl

end CertificateChecks.KernelSpor.ONL37

end
