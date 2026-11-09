module

public import Certificates.Data.Kernel.Fi22.LHK
public import Certificates.Kernel.Fi22LH.Sel
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Fi22LH.Prim

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22LH

open CFSG.KC.Enum CFSG.KS CFSG.KS.Fi22LH CFSG.KD.Fi22LH

theorem mu_0 : muSlW R Z P QA lb0 (fd mt 0 16383) 0 = true := by quickRfl
theorem mu_1 : muSlW R Z P QA lb0 (fd mt 0 16383) 1 = true := by quickRfl
theorem mu_2 : muSlW R Z P QA lb0 (fd mt 0 16383) 2 = true := by quickRfl
theorem mu_3 : muSlW R Z P QA lb0 (fd mt 0 16383) 3 = true := by quickRfl

@[expose] noncomputable def muStep (R Z P QA M G : Nat → Nat) (mk mq h n : Nat) : Nat :=
  nIf(Nat.blt h n,
    strictN (rowSet P QA (fd (M h) (nat_lit 0) (nat_lit 4095))) fun q => strictN (G h) fun a =>
      foldUp (nat_lit 3510) (fun f m => muHit R Z M G mk mq q a h f m) n, nat_lit 0)

@[expose] noncomputable def muTreePre (R Z P QA M G : Nat → Nat) (mk mq nm c : Nat) : Bool :=
  strictB (fd (M (nat_lit 0)) (nat_lit 0) (nat_lit 4095)) fun f0 =>
  bAnd(Nat.beq (Nat.shiftRight (M (nat_lit 0)) (nat_lit 12)) (nat_lit 0), bAnd(Nat.blt f0 (nat_lit 3510), bAnd(Nat.blt (fd (P f0) (nat_lit 14) (nat_lit 4095)) (nat_lit 3510),
  bAnd(allN f0 (fun f => notB (Nat.blt (fd (P f) (nat_lit 14) (nat_lit 4095)) (nat_lit 3510))),
  bAnd(allN nm (fun k => strictB (fd (M k) (nat_lit 0) (nat_lit 4095)) fun f =>
      bAnd(Nat.blt (fd (P f) (nat_lit 14) (nat_lit 4095)) (nat_lit 3510),
        Nat.beq (G k) (sb (rowSet P QA f)))),
  bAnd(posK (fun k => fd (M k) (nat_lit 0) (nat_lit 4095)) (fun f => fld(mq, Nat.mul (nat_lit 10) f, nat_lit 1023))
      (nat_lit 1023) (nat_lit 3510) nm,
  bAnd(allN (nat_lit 3510) (fun f => bIf(Nat.blt (fd (P f) (nat_lit 14) (nat_lit 4095)) (nat_lit 3510),
      Nat.blt (fld(mq, Nat.mul (nat_lit 10) f, nat_lit 1023)) nm, true)),
    Nat.beq c nm)))))))

theorem muTreeK_eq (R Z P QA M G : Nat → Nat) (mk mq nm : Nat) :
    muTreeK R Z P QA M G mk mq nm =
      muTreePre R Z P QA M G mk mq nm (foldUp nm (muStep R Z P QA M G mk mq) (nat_lit 1)) :=
  rfl

@[expose] noncomputable def muChunk (R Z P QA M G : Nat → Nat) (mq lo len s t : Nat) : Bool :=
  strictB masks fun mk =>
    Nat.beq (foldUp len (fun i => muStep R Z P QA M G mk mq (Nat.add lo i)) s) t

theorem muChunk_eq {R Z P QA M G : Nat → Nat} {mq lo len s t : Nat}
    (h : muChunk R Z P QA M G mq lo len s t = true) :
    foldUp len (fun i => muStep R Z P QA M G masks mq (lo + i)) s = t := by
  unfold muChunk at h
  rw [strictB_eq] at h
  exact Nat.eq_of_beq_eq_true h

theorem foldUp_step (F : Nat → Nat → Nat) (a len s t u : Nat) (ha : foldUp a F s = t)
    (hc : foldUp len (fun i => F (a + i)) t = u) : foldUp (a + len) F s = u := by
  rw [foldUp_eq] at ha hc ⊢
  rw [List.range_add, List.foldl_append, ha, List.foldl_map]
  exact hc

theorem mu_c0 : muChunk R Z P QA M G mq 0 81 1 648 = true := by quickRfl
theorem mu_c1 : muChunk R Z P QA M G mq 81 81 648 648 = true := by quickRfl
theorem mu_c2 : muChunk R Z P QA M G mq 162 81 648 648 = true := by quickRfl
theorem mu_c3 : muChunk R Z P QA M G mq 243 81 648 648 = true := by quickRfl
theorem mu_c4 : muChunk R Z P QA M G mq 324 81 648 648 = true := by quickRfl
theorem mu_c5 : muChunk R Z P QA M G mq 405 81 648 648 = true := by quickRfl
theorem mu_c6 : muChunk R Z P QA M G mq 486 81 648 648 = true := by quickRfl
theorem mu_c7 : muChunk R Z P QA M G mq 567 81 648 648 = true := by quickRfl

theorem mu_fold : foldUp 648 (muStep R Z P QA M G masks mq) (nat_lit 1) = 648 := by
  have h0 : foldUp 0 (muStep R Z P QA M G masks mq) (nat_lit 1) = 1 := rfl
  have h1 : foldUp 81 (muStep R Z P QA M G masks mq) (nat_lit 1) = 648 :=
    foldUp_step _ 0 81 _ _ _ h0 (muChunk_eq mu_c0)
  have h2 : foldUp 162 (muStep R Z P QA M G masks mq) (nat_lit 1) = 648 :=
    foldUp_step _ 81 81 _ _ _ h1 (muChunk_eq mu_c1)
  have h3 : foldUp 243 (muStep R Z P QA M G masks mq) (nat_lit 1) = 648 :=
    foldUp_step _ 162 81 _ _ _ h2 (muChunk_eq mu_c2)
  have h4 : foldUp 324 (muStep R Z P QA M G masks mq) (nat_lit 1) = 648 :=
    foldUp_step _ 243 81 _ _ _ h3 (muChunk_eq mu_c3)
  have h5 : foldUp 405 (muStep R Z P QA M G masks mq) (nat_lit 1) = 648 :=
    foldUp_step _ 324 81 _ _ _ h4 (muChunk_eq mu_c4)
  have h6 : foldUp 486 (muStep R Z P QA M G masks mq) (nat_lit 1) = 648 :=
    foldUp_step _ 405 81 _ _ _ h5 (muChunk_eq mu_c5)
  have h7 : foldUp 567 (muStep R Z P QA M G masks mq) (nat_lit 1) = 648 :=
    foldUp_step _ 486 81 _ _ _ h6 (muChunk_eq mu_c6)
  have h8 : foldUp 648 (muStep R Z P QA M G masks mq) (nat_lit 1) = 648 :=
    foldUp_step _ 567 81 _ _ _ h7 (muChunk_eq mu_c7)
  exact h8

theorem nm_eq : fd mt 70 1023 = 648 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem mu_fold' : foldUp (fd mt 70 1023) (muStep R Z P QA M G masks mq) (nat_lit 1) = 648 := by
  rw [nm_eq]
  exact mu_fold

theorem mu_pre : muTreePre R Z P QA M G masks mq (fd mt 70 1023) 648 = true := by quickRfl

theorem mu_tree : muTreeW R Z P QA M G mq (fd mt 70 1023) = true := by
  rw [muTreeW, strictB_eq, muTreeK_eq, mu_fold']
  exact mu_pre

theorem ml_ok : mlK mq ml (fd mt 70 1023) = true := by quickRfl

end CertificateChecks.KernelFi22LH
