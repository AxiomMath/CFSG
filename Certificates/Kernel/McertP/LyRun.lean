module

public import Certificates.Kernel.LocalComp.LaySeeds
public import Certificates.Data.Kernel.OpsLayMcert
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigData
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigData3
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaLyData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaWordDefs
public import Certificates.Kernel.LocalComp.LaySnaps
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.ForallTree
public import Certificates.Data.Kernel.OpsLayFill
public import Certificates.Kernel.LocalComp.LaySnapsChunksF
meta import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigData
meta import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigData3
meta import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaLyData
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

#lay_seeds CertificateChecks.KernelMP.Ly 5 111
  CFSG.Blueprint.NativeSporadic.LySeed1 CFSG.Blueprint.NativeSporadic.LySeed2

meta def ly7ProgM : List CFSG.SectionRank.Native.Op :=
  CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal.ly_7_claims.prog

#lay_snaps CertificateChecks.KernelMP.Ly.W7 5 111 CertificateChecks.KernelMP.Ly.A
  CertificateChecks.KernelMP.Ly.B ly7ProgM 18 100

#lay_snaps CertificateChecks.KernelMP.Ly.WA 5 111 CertificateChecks.KernelMP.Ly.A
  CertificateChecks.KernelMP.Ly.B CFSG.AGLEmbedding.R3.AlphaLy.lyProg 32 100

public section

namespace CertificateChecks.KernelMP.Ly

open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

@[expose] def seedIx : List Nat := [0, 1]

@[expose] def w31z : List (Nat × Nat) := mwordPow (pwToWord ly_31_claims.g.z) 31

@[expose] def w31r : List (Nat × Nat) :=
  mwordPow (pwToWord ly_31_claims.g.z) 30 ++ pwToWord [(false, 1)]

@[expose] def w31l : List (Nat × Nat) :=
  pwToWord [(false, 1)] ++ mwordPow (pwToWord ly_31_claims.g.z) 30

meta def w31zM : List (Nat × Nat) := mwordPow (pwToWord ly_31_claims.g.z) 31

meta def w31rM : List (Nat × Nat) :=
  mwordPow (pwToWord ly_31_claims.g.z) 30 ++ pwToWord [(false, 1)]

meta def w31lM : List (Nat × Nat) :=
  pwToWord [(false, 1)] ++ mwordPow (pwToWord ly_31_claims.g.z) 30

end CertificateChecks.KernelMP.Ly

#lay_wsegs_f CertificateChecks.KernelMP.Ly.Z2 5 111 CertificateChecks.KernelMP.Ly.W7.S0
  CertificateChecks.KernelMP.Ly.seedIx CertificateChecks.KernelMP.Ly.w31zM 96
#lay_wsegs_f CertificateChecks.KernelMP.Ly.Z4 5 111 CertificateChecks.KernelMP.Ly.W7.S0
  CertificateChecks.KernelMP.Ly.seedIx CertificateChecks.KernelMP.Ly.w31rM 96
#lay_wsegs_f CertificateChecks.KernelMP.Ly.Z5 5 111 CertificateChecks.KernelMP.Ly.W7.S0
  CertificateChecks.KernelMP.Ly.seedIx CertificateChecks.KernelMP.Ly.w31lM 96

namespace CertificateChecks.KernelMP.Ly

open CFSG.KC.OpsLayK CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
open CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaLy CFSG.SectionRank.Native
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

@[expose] noncomputable def fa31 (i : Nat) : Bool :=
  factsL lay (initR lay A B 2) 2 ly_31_claims.baseFacts 1 i

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

theorem evalWL_onto (c : CFSG.KC.LQT.Lay) (R : List Nat) :
    ∀ w : Word, evalWL c R w = evalOnto c R w c.ONE
  | [] => rfl
  | (r, e) :: w => by
    have ih := evalWL_onto c R w
    unfold evalOnto at ih ⊢
    rw [List.foldr_cons, strictN_eq', ← ih]
    rfl

theorem evalOnto_app (c : CFSG.KC.LQT.Lay) (R : List Nat) (u w : Word) (X : Nat) :
    evalOnto c R (u ++ w) X = evalOnto c R u (evalOnto c R w X) := by
  unfold evalOnto
  rw [List.foldr_append]

theorem factL_eq_segs {c : CFSG.KC.LQT.Lay} {R : List Nat} {n : Nat} {u w : Word} {k m : Nat}
    {W : Nat → Nat} (hok : (wordOK n u && wordOK n w) = true) (hlen : w.length ≤ m * k)
    (hlast : W m = c.ONE) (hs : ∀ i < m, wsegL c R w k i (W i) (W (i + 1)) = true)
    (h0 : Nat.beq (evalWL c R u) (W 0) = true) : factL c R n (.eq u w) = true := by
  have key : ∀ j ≤ m, evalOnto c R (w.drop ((m - j) * k)) c.ONE = W (m - j) := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [Nat.sub_zero, List.drop_eq_nil_of_le hlen, hlast]
      rfl
    | succ j ih =>
      intro hj
      have hi : m - (j + 1) + 1 = m - j := by omega
      have e : w.drop ((m - (j + 1)) * k) =
          (w.drop ((m - (j + 1)) * k)).take k ++ w.drop ((m - j) * k) := by
        rw [← hi, Nat.succ_mul, ← List.drop_drop, List.take_append_drop]
      rw [e, evalOnto_app, ih (by omega)]
      have := hs (m - (j + 1)) (by omega)
      unfold wsegL at this
      rw [hi] at this
      exact Nat.eq_of_beq_eq_true this
  have hw : evalWL c R w = W 0 := by
    rw [evalWL_onto]
    have := key m le_rfl
    rwa [Nat.sub_self, Nat.zero_mul, List.drop_zero] at this
  simp only [factL, Bool.and_eq_true] at hok ⊢
  exact ⟨hok, by rw [hw]; exact h0⟩

theorem factL_eq_symm {c : CFSG.KC.LQT.Lay} {R : List Nat} {n : Nat} {u w : Word}
    (h : factL c R n (.eq w u) = true) : factL c R n (.eq u w) = true := by
  simp only [factL, Bool.and_eq_true] at h ⊢
  refine ⟨⟨h.1.2, h.1.1⟩, ?_⟩
  rw [Nat.eq_of_beq_eq_true h.2]
  exact Nat.beq_refl _

@[expose] noncomputable def sg2 (i : Nat) : Bool :=
  wsegL lay (initR lay A B 2) w31z 96 i (Z2.WL.getD i lay.ONE) (Z2.WL.getD (i + 1) lay.ONE)

@[expose] noncomputable def sg4 (i : Nat) : Bool :=
  wsegL lay (initR lay A B 2) w31r 96 i (Z4.WL.getD i lay.ONE) (Z4.WL.getD (i + 1) lay.ONE)

@[expose] noncomputable def sg5 (i : Nat) : Bool :=
  wsegL lay (initR lay A B 2) w31l 96 i (Z5.WL.getD i lay.ONE) (Z5.WL.getD (i + 1) lay.ONE)

#kc_each sg2 0 8
#kc_each sg4 0 8
#kc_each sg5 0 8

#kc_forall_tree sg2_all (fun i => sg2 i = true) 8 CertificateChecks.KernelMP.Ly.sg2
#kc_forall_tree sg4_all (fun i => sg4 i = true) 8 CertificateChecks.KernelMP.Ly.sg4
#kc_forall_tree sg5_all (fun i => sg5 i = true) 8 CertificateChecks.KernelMP.Ly.sg5

theorem fa31_one {i : Nat} {f : MFact}
    (e : (ly_31_claims.baseFacts.drop (i * 1)).take 1 = [f])
    (h : factL lay (initR lay A B 2) 2 f = true) : fa31 i = true := by
  unfold fa31 factsL
  rw [e, List.all_cons, List.all_nil, Bool.and_true]
  exact h

#kc_each fa31 0 2
#kc_each fa31 3 4

theorem fa312 : fa31 2 = true :=
  fa31_one (f := .eq w31z []) rfl <| factL_eq_symm <|
    factL_eq_segs (k := 96) (m := 8) (W := fun i => Z2.WL.getD i lay.ONE) (by decide +kernel)
      (by decide +kernel) (List.getD_eq_default _ _ (by decide +kernel)) sg2_all
      (by decide +kernel)

theorem fa314 : fa31 4 = true :=
  fa31_one (f := .eq (pwToWord [(false, 1)] ++ pwToWord ly_31_claims.g.z) w31r) rfl <|
    factL_eq_segs (k := 96) (m := 8) (W := fun i => Z4.WL.getD i lay.ONE) (by decide +kernel)
      (by decide +kernel) (List.getD_eq_default _ _ (by decide +kernel)) sg4_all
      (by decide +kernel)

theorem fa315 : fa31 5 = true :=
  fa31_one (f := .eq w31l (pwToWord ly_31_claims.g.z ++ pwToWord [(false, 1)])) rfl <|
    factL_eq_symm <|
    factL_eq_segs (k := 96) (m := 8) (W := fun i => Z5.WL.getD i lay.ONE) (by decide +kernel)
      (by decide +kernel) (List.getD_eq_default _ _ (by decide +kernel)) sg5_all
      (by decide +kernel)

#kc_forall_tree fa31_all (fun i => fa31 i = true) 6 CertificateChecks.KernelMP.Ly.fa31

theorem ly31_sizes : (eqL (initR lay A B 2) (initR lay A B 2) &&
    decide (ly_31_claims.baseFacts.length ≤ 6 * 1)) = true := by
  decide +kernel

theorem ly31_K : mcertL lay A B ⟨2, [], ly_31_claims.baseFacts⟩ = true := by
  have h := ly31_sizes
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact mcertL_of_snaps (S := fun _ => initR lay A B 2) (k := 1) (m := 0) rfl h.1 (Nat.le_refl 0)
    (fun i hi => absurd hi (Nat.not_lt_zero i)) h.2 fa31_all

@[expose] noncomputable def ch7 (i : Nat) : Bool :=
  chunkL lay ly_7_claims.prog 100 i (W7.SL.getD i []) (W7.SL.getD (i + 1) [])

@[expose] noncomputable def fa7 (i : Nat) : Bool :=
  factsL lay (W7.SL.getD 5 []) ly_7_claims.nregs ly_7_claims.facts 3 i

@[expose] noncomputable def chA (i : Nat) : Bool :=
  chunkL lay lyProg 100 i (WA.SL.getD i []) (WA.SL.getD (i + 1) [])

@[expose] noncomputable def faA (i : Nat) : Bool :=
  factsL lay (WA.SL.getD 2 []) lyNregs (lyMod.modFactsW 3 lyTops) 40 i

#kc_each ch7 0 5
#kc_each fa7 0 4
#kc_each chA 0 2
#kc_each faA 0 8

#kc_forall_tree ch7_all (fun i => ch7 i = true) 5 CertificateChecks.KernelMP.Ly.ch7
#kc_forall_tree fa7_all (fun i => fa7 i = true) 4 CertificateChecks.KernelMP.Ly.fa7
#kc_forall_tree chA_all (fun i => chA i = true) 2 CertificateChecks.KernelMP.Ly.chA
#kc_forall_tree faA_all (fun i => faA i = true) 8 CertificateChecks.KernelMP.Ly.faA

theorem ly7_sizes : (progOK ly_7_claims.nregs ly_7_claims.prog &&
    eqL (W7.SL.getD 0 []) (initR lay A B ly_7_claims.nregs) &&
    decide (ly_7_claims.prog.length ≤ 5 * 100) && decide (ly_7_claims.facts.length ≤ 4 * 3)) =
    true := by
  decide +kernel

theorem alpha_sizes : (progOK lyNregs lyProg && eqL (WA.SL.getD 0 []) (initR lay A B lyNregs) &&
    decide (lyProg.length ≤ 2 * 100) &&
    decide ((lyMod.modFactsW 3 lyTops).length ≤ 8 * 40)) = true := by
  decide +kernel

theorem ly7_K : mcertL lay A B ⟨ly_7_claims.nregs, ly_7_claims.prog, ly_7_claims.facts⟩ = true := by
  have h := ly7_sizes
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact mcertL_of_snaps (S := fun i => W7.SL.getD i []) h.1.1.1 h.1.1.2 h.1.2 ch7_all h.2 fa7_all

theorem alpha_K : mcertL lay A B ⟨lyNregs, lyProg, lyMod.modFactsW 3 lyTops⟩ = true := by
  have h := alpha_sizes
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact mcertL_of_snaps (S := fun i => WA.SL.getD i []) h.1.1.1 h.1.1.2 h.1.2 chA_all h.2 faA_all

end CertificateChecks.KernelMP.Ly

end
