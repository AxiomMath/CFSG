module

public import Certificates.Kernel.LocalComp.LaySeeds
public import Certificates.Data.Kernel.OpsLayMcert
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigData5
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaHNData
public import Certificates.Kernel.LocalComp.LaySnaps
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.ForallTree
meta import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigData5
meta import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaHNData
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

#lay_seeds CertificateChecks.KernelMP.HN 5 133
  CFSG.Blueprint.NativeSporadic.HNSeed1 CFSG.Blueprint.NativeSporadic.HNSeed2

meta def hn7ProgM : List CFSG.SectionRank.Native.Op :=
  CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal.hn_7_claims.prog

#lay_snaps CertificateChecks.KernelMP.HN.W7 5 133 CertificateChecks.KernelMP.HN.A
  CertificateChecks.KernelMP.HN.B hn7ProgM 265 100

#lay_snaps CertificateChecks.KernelMP.HN.WA 5 133 CertificateChecks.KernelMP.HN.A
  CertificateChecks.KernelMP.HN.B CFSG.AGLEmbedding.R3.AlphaHN.hnProg 32 100

public section

namespace CertificateChecks.KernelMP.HN

open CFSG.KC.OpsLayK CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
open CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaHN CFSG.SectionRank.Native
  CFSG.RankThree.Asc83Table.Native

theorem strictB_eq' (y : Nat) (k : Nat → Bool) : CFSG.KC.LQT.strictB y k = k y := by
  cases y <;> rfl

@[expose] noncomputable def regsAfter (c : CFSG.KC.LQT.Lay) (prog : List Op) (R : List Nat) :
    List Nat :=
  prog.foldl (fun R o => R.set (Op.tgt o) (stepV c R o)) R

theorem runC_regsAfter (c : CFSG.KC.LQT.Lay) : ∀ (prog : List Op) (R : List Nat)
    (k : List Nat → Bool), runC c prog R k = k (regsAfter c prog R)
  | [], _, _ => rfl
  | o :: prog, R, k => by
    change CFSG.KC.LQT.strictB (stepV c R o) (fun v => runC c prog (R.set (Op.tgt o) v) k) = _
    rw [strictB_eq']
    exact runC_regsAfter c prog _ k

theorem eqL_eq : ∀ {a b : List Nat}, eqL a b = true → a = b
  | [], [], _ => rfl
  | x :: a, y :: b, h => by
    simp only [eqL, Bool.and_eq_true] at h
    rw [Nat.eq_of_beq_eq_true h.1, eqL_eq h.2]
  | [], _ :: _, h => by simp [eqL] at h
  | _ :: _, [], h => by simp [eqL] at h

theorem regsAfter_append (c : CFSG.KC.LQT.Lay) (p q : List Op) (R : List Nat) :
    regsAfter c (p ++ q) R = regsAfter c q (regsAfter c p R) := by
  unfold regsAfter
  rw [List.foldl_append]

theorem regsAfter_of_chunks {c : CFSG.KC.LQT.Lay} {prog : List Op} {k m : Nat}
    {S : Nat → List Nat} (hm : prog.length ≤ m * k)
    (h : ∀ i < m, chunkL c prog k i (S i) (S (i + 1)) = true) : regsAfter c prog (S 0) = S m := by
  have key : ∀ j ≤ m, regsAfter c (prog.take (j * k)) (S 0) = S j := by
    intro j
    induction j with
    | zero => intro _; simp [regsAfter]
    | succ j ih =>
      intro hj
      have hc := h j (by omega)
      unfold chunkL at hc
      rw [runC_regsAfter] at hc
      rw [Nat.succ_mul, List.take_add, regsAfter_append, ih (by omega)]
      exact eqL_eq hc
  rw [← List.take_of_length_le hm]
  exact key m le_rfl

theorem all_of_groups {α : Type} {p : α → Bool} {fs : List α} {k m : Nat}
    (hm : fs.length ≤ m * k) (h : ∀ i < m, ((fs.drop (i * k)).take k).all p = true) :
    fs.all p = true := by
  have key : ∀ j ≤ m, (fs.take (j * k)).all p = true := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      rw [Nat.succ_mul, List.take_add, List.all_append, ih (by omega), h j (by omega)]
      rfl
  rw [← List.take_of_length_le hm]
  exact key m le_rfl

theorem mcertL_of_snaps {c : CFSG.KC.LQT.Lay} {A B : Nat} {C : MCert} {S : Nat → List Nat}
    {k m kf mf : Nat} (hprog : progOK C.nregs C.prog = true)
    (h0 : eqL (S 0) (initR c A B C.nregs) = true) (hm : C.prog.length ≤ m * k)
    (hch : ∀ i < m, chunkL c C.prog k i (S i) (S (i + 1)) = true)
    (hmf : C.facts.length ≤ mf * kf) (hf : ∀ i < mf, factsL c (S m) C.nregs C.facts kf i = true) :
    mcertL c A B C = true := by
  unfold mcertL
  rw [hprog, Bool.true_and, runC_regsAfter, ← eqL_eq h0, regsAfter_of_chunks hm hch]
  exact all_of_groups hmf hf

@[expose] noncomputable def ch7 (i : Nat) : Bool :=
  chunkL lay hn_7_claims.prog 100 i (W7.SL.getD i []) (W7.SL.getD (i + 1) [])

@[expose] noncomputable def fa7 (i : Nat) : Bool :=
  factsL lay (W7.SL.getD 19 []) hn_7_claims.nregs hn_7_claims.facts 5 i

@[expose] noncomputable def chA (i : Nat) : Bool :=
  chunkL lay hnProg 100 i (WA.SL.getD i []) (WA.SL.getD (i + 1) [])

@[expose] noncomputable def faA (i : Nat) : Bool :=
  factsL lay (WA.SL.getD 4 []) hnNregs (hnMod.modFactsE 3 hnTops hnGs) 50 i

#kc_each ch7 0 19
#kc_each fa7 0 5
#kc_each chA 0 4
#kc_each faA 0 4

#kc_forall_tree ch7_all (fun i => ch7 i = true) 19 CertificateChecks.KernelMP.HN.ch7
#kc_forall_tree fa7_all (fun i => fa7 i = true) 5 CertificateChecks.KernelMP.HN.fa7
#kc_forall_tree chA_all (fun i => chA i = true) 4 CertificateChecks.KernelMP.HN.chA
#kc_forall_tree faA_all (fun i => faA i = true) 4 CertificateChecks.KernelMP.HN.faA

theorem hn7_sizes : (progOK hn_7_claims.nregs hn_7_claims.prog &&
    eqL (W7.SL.getD 0 []) (initR lay A B hn_7_claims.nregs) &&
    decide (hn_7_claims.prog.length ≤ 19 * 100) && decide (hn_7_claims.facts.length ≤ 5 * 5)) =
    true := by
  decide +kernel

theorem alpha_sizes : (progOK hnNregs hnProg && eqL (WA.SL.getD 0 []) (initR lay A B hnNregs) &&
    decide (hnProg.length ≤ 4 * 100) &&
    decide ((hnMod.modFactsE 3 hnTops hnGs).length ≤ 4 * 50)) = true := by
  decide +kernel

theorem hn7_K : mcertL lay A B ⟨hn_7_claims.nregs, hn_7_claims.prog, hn_7_claims.facts⟩ = true := by
  have h := hn7_sizes
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact mcertL_of_snaps (S := fun i => W7.SL.getD i []) h.1.1.1 h.1.1.2 h.1.2 ch7_all h.2 fa7_all

theorem alpha_K : mcertL lay A B ⟨hnNregs, hnProg, hnMod.modFactsE 3 hnTops hnGs⟩ = true := by
  have h := alpha_sizes
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact mcertL_of_snaps (S := fun i => WA.SL.getD i []) h.1.1.1 h.1.1.2 h.1.2 chA_all h.2 faA_all

theorem hn7_neg :
    (!chunkL lay hn_7_claims.prog 100 0 (initR lay B A hn_7_claims.nregs) (W7.SL.getD 1 [])) =
      true := by
  decide +kernel

theorem alpha_neg : (!chunkL lay hnProg 100 0 (initR lay B A hnNregs) (WA.SL.getD 1 [])) = true := by
  decide +kernel

end CertificateChecks.KernelMP.HN

end
