module

public import Certificates.Data.Kernel.Spor.ONTauK
public import Certificates.Kernel.Sporadic.ON2.Data
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatVal

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CertificateChecks.KernelSpor.ONC

theorem strictB_eqC (y : Nat) (k : Nat → Bool) : CFSG.KC.Enum.strictB y k = k y := by
  cases y <;> rfl

theorem bAnd_iffC (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = true ↔
    a = true ∧ b = true := by
  cases a <;> cases b <;> simp

theorem gensK_aux (mul : Nat → Nat → Nat) (L : Int → Nat) (one : Nat) (k : List Nat → Bool) :
    ∀ (gw : List (List Int)) (G : List Nat),
      List.rec (motive := fun _ => List Nat → Bool) (fun G => k G.reverse)
        (fun w _ ih G => CFSG.KC.Enum.strictB (CFSG.KS.ONC.wordK mul L w one) fun g => ih (g :: G)) gw G =
      k (G.reverse ++ gw.map fun w => CFSG.KS.ONC.wordK mul L w one)
  | [], G => by simp
  | w :: gw, G => by
    show CFSG.KC.Enum.strictB _ _ = _
    rw [strictB_eqC, gensK_aux mul L one k gw]
    simp

theorem gensK_eq (mul : Nat → Nat → Nat) (L : Int → Nat) (one : Nat) (gw : List (List Int))
    (k : List Nat → Bool) :
    CFSG.KS.ONC.gensK mul L one gw k = k (gw.map fun w => CFSG.KS.ONC.wordK mul L w one) := by
  unfold CFSG.KS.ONC.gensK
  rw [gensK_aux]
  simp

theorem pairsK_append (mul : Nat → Nat → Nat) (one : Nat) (G : List Nat) :
    ∀ (u v : List (List Nat × List Nat)),
      CFSG.KS.ONC.pairsK mul one G (u ++ v) = true ↔
        CFSG.KS.ONC.pairsK mul one G u = true ∧ CFSG.KS.ONC.pairsK mul one G v = true
  | [], v => by simp [CFSG.KS.ONC.pairsK]
  | p :: u, v => by
    show Bool.rec (motive := fun _ => Bool) false (CFSG.KS.ONC.pairsK mul one G (u ++ v)) _ = true ↔
      Bool.rec (motive := fun _ => Bool) false (CFSG.KS.ONC.pairsK mul one G u) _ = true ∧ _
    rw [bAnd_iffC, bAnd_iffC, pairsK_append mul one G u v]
    exact and_assoc.symm

theorem pairsK_seg {mul : Nat → Nat → Nat} {one : Nat} {G : List Nat}
    (P : List (List Nat × List Nat)) (m n k : Nat) (hk : m + n = k)
    (h1 : CFSG.KS.ONC.pairsK mul one G (List.take n (List.drop m P)) = true)
    (h2 : CFSG.KS.ONC.pairsK mul one G (List.drop k P) = true) :
    CFSG.KS.ONC.pairsK mul one G (List.drop m P) = true := by
  rw [← List.take_append_drop n (List.drop m P), pairsK_append, List.drop_drop, hk]
  exact ⟨h1, h2⟩

section
open CFSG.KC.Enum CFSG.KS CFSG.KC.Ord

@[expose] noncomputable def relsA (CS0 DS0 L0 H0 CM0 RM0 ONE0 : Nat)
    (bat : Nat → Nat → (Nat → Nat) → Nat → Nat → Nat)
    (m3 : Nat → Nat → Nat → Nat → Nat → Nat → Nat)
    (FA FB : Nat → Nat) (gw : List (List Int)) (ps : List (List Nat × List Nat)) : Bool :=
  strictB CS0 fun cs => strictB DS0 fun ds => strictB L0 fun L => strictB H0 fun H =>
  strictB CM0 fun cm => strictB RM0 fun rm => strictB ONE0 fun one =>
  strictB (bat cs ds FA (nat_lit 0) (nat_lit 154)) fun a =>
  strictB (bat cs ds FB (nat_lit 0) (nat_lit 154)) fun b =>
  strictB (m3 L H cm rm (m3 L H cm rm b b) b) fun bi =>
    bAnd(Nat.beq (m3 L H cm rm a a) one, bAnd(Nat.beq (m3 L H cm rm b bi) one,
      CFSG.KS.ONC.gensK (m3 L H cm rm) (CFSG.KS.ONC.seedL a a b bi) one gw
        fun G => CFSG.KS.ONC.pairsK (m3 L H cm rm) one G ps))

end

theorem relsK_eqA (FA FB : Nat → Nat) (gw : List (List Int)) (ps : List (List Nat × List Nat)) :
    CFSG.KS.ONC.relsK FA FB gw ps =
      relsA CFSG.KS.ONC.CS CFSG.KS.ONC.DS CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM
        CFSG.KS.ONC.RM CFSG.KS.ONC.ONE CFSG.KS.ONC.batK CFSG.KS.ONC.mul3 FA FB gw ps := rfl

theorem relsA_of {CS0 DS0 L0 H0 CM0 RM0 ONE0 : Nat} {bat : Nat → Nat → (Nat → Nat) → Nat → Nat → Nat}
    {m3 : Nat → Nat → Nat → Nat → Nat → Nat → Nat} {FA FB : Nat → Nat} {gw : List (List Int)}
    {ps : List (List Nat × List Nat)} {A B BI : Nat}
    (hA : Nat.beq (bat CS0 DS0 FA (nat_lit 0) (nat_lit 154)) A = true)
    (hB : Nat.beq (bat CS0 DS0 FB (nat_lit 0) (nat_lit 154)) B = true)
    (hBI : Nat.beq (m3 L0 H0 CM0 RM0 (m3 L0 H0 CM0 RM0 B B) B) BI = true)
    (ha : Nat.beq (m3 L0 H0 CM0 RM0 A A) ONE0 = true)
    (hb : Nat.beq (m3 L0 H0 CM0 RM0 B BI) ONE0 = true)
    (hP : CFSG.KS.ONC.pairsK (m3 L0 H0 CM0 RM0) ONE0
      (gw.map fun w => CFSG.KS.ONC.wordK (m3 L0 H0 CM0 RM0) (CFSG.KS.ONC.seedL A A B BI) w ONE0)
      ps = true) :
    relsA CS0 DS0 L0 H0 CM0 RM0 ONE0 bat m3 FA FB gw ps = true := by
  unfold relsA
  simp only [strictB_eqC]
  rw [Nat.eq_of_beq_eq_true hA, Nat.eq_of_beq_eq_true hB, Nat.eq_of_beq_eq_true hBI, ha, hb, gensK_eq,
    hP]

theorem relsK_of {FA FB : Nat → Nat} {gw : List (List Int)} {ps : List (List Nat × List Nat)}
    {A B BI : Nat}
    (hA : Nat.beq (CFSG.KS.ONC.batK CFSG.KS.ONC.CS CFSG.KS.ONC.DS FA (nat_lit 0) (nat_lit 154)) A = true)
    (hB : Nat.beq (CFSG.KS.ONC.batK CFSG.KS.ONC.CS CFSG.KS.ONC.DS FB (nat_lit 0) (nat_lit 154)) B = true)
    (hBI : Nat.beq (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM B B) B) BI = true)
    (ha : Nat.beq (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM A A) CFSG.KS.ONC.ONE = true)
    (hb : Nat.beq (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM B BI) CFSG.KS.ONC.ONE = true)
    (hP : CFSG.KS.ONC.pairsK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) CFSG.KS.ONC.ONE
      (gw.map fun w => CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL A A B BI) w CFSG.KS.ONC.ONE)
      ps = true) :
    CFSG.KS.ONC.relsK FA FB gw ps = true :=
  (relsK_eqA FA FB gw ps).trans (relsA_of hA hB hBI ha hb hP)

open CFSG.KS.ONC in
#kc_natval ONSA := batK CS DS (fun j => List.getD ONW.LA j (nat_lit 0)) (nat_lit 0) (nat_lit 154)
open CFSG.KS.ONC in
#kc_natval ONSB := batK CS DS (fun j => List.getD ONW.LB j (nat_lit 0)) (nat_lit 0) (nat_lit 154)
open CFSG.KS.ONC in
#kc_natval ONSBI := mul3 LL HH CM RM (mul3 LL HH CM RM ONSB ONSB) ONSB

theorem cA : Nat.beq (CFSG.KS.ONC.batK CFSG.KS.ONC.CS CFSG.KS.ONC.DS
    (fun j => List.getD ONW.LA j (nat_lit 0)) (nat_lit 0) (nat_lit 154)) ONSA = true := by
  quickRfl

theorem cB : Nat.beq (CFSG.KS.ONC.batK CFSG.KS.ONC.CS CFSG.KS.ONC.DS
    (fun j => List.getD ONW.LB j (nat_lit 0)) (nat_lit 0) (nat_lit 154)) ONSB = true := by
  quickRfl

theorem cBI : Nat.beq (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM
    (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM ONSB ONSB) ONSB) ONSBI =
    true := by
  quickRfl

theorem ca1 : Nat.beq (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM
    ONSA ONSA) CFSG.KS.ONC.ONE = true := by
  quickRfl

theorem cb1 : Nat.beq (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM
    ONSB ONSBI) CFSG.KS.ONC.ONE = true := by
  quickRfl

end CertificateChecks.KernelSpor.ONC

end
