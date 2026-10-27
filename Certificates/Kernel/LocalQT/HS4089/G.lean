module

public import Certificates.Kernel.LocalQT.HS4089.A
public import Certificates.Kernel.LocalQT.HS4089.SN
public import Certificates.Kernel.LocalQT.HS4089.C1
public import Certificates.Kernel.LocalQT.HS4089.C2
public import CFSG.Certificates.Kernel.LocalQTPcOmSound
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporHSLit
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporHSCheckInputs
import Mathlib.Tactic.IntervalCases
public import Certificates.Kernel.SporSch.J4S.NoCP

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LQT.H4089

open CFSG.KC.Enum CFSG.KS CFSG.KS.PF CFSG.KC.LQT.PcW CFSG.KC.LQT.PcOm
open CFSG.QuasithinUnique.Ch1.SporLat (idTab QuotGen wordTabA ptAct OmegaSpec)
open CFSG.QuasithinUnique.Ch1.SporLat.HS (hsSTabs hsDelta)
open CFSG.QuasithinUnique.K1.SporadicPerm (hsTa hsTb hsSLP hsProg hsQp slpTabsA)
open CFSG.QuasithinUnique.Vol2Native.L239 (Wit3Ok WitPOk)
open CFSG.QuasithinUnique.Vol2Native.L239.HSPairs
open CFSG.Sporadic.HS.Native (hsData)
open CertificateChecks.KernelVec.HS (AT BT)

theorem rep_id0 : Rep 1100 11 (TF 0) (idTab 1100) := by
  have e := Nat.eq_of_beq_eq_true idc
  have h := rep_id (n := 1100) (w := 11) (by norm_num) (by norm_num)
  rw [e] at h
  exact h

theorem rep_ta : Rep 1100 11 (CFSG.KD.LQT.H4089S.TF 0) hsTa := by
  rw [ta_eq]
  exact rep_of_canon (m := 2047) (nw := 12100) (F := CFSG.KC.VecK.lk AT 32) (by rfl) (by rfl)
    canonA bindA

theorem rep_tb : Rep 1100 11 (CFSG.KD.LQT.H4089S.TF 1) hsTb := by
  rw [tb_eq]
  exact rep_of_canon (m := 2047) (nw := 12100) (F := CFSG.KC.VecK.lk BT 32) (by rfl) (by rfl)
    canonB bindB

theorem rep_nodes (j : Nat) (hj : j < 219) : Rep 1100 11 (CFSG.KD.LQT.H4089S.TF j) hsSLP[j]! := by
  have hlen : hsProg.length = 217 := rfl
  have hnd : ∀ j, 2 ≤ j → j < hsProg.length + 2 →
      CFSG.KD.LQT.H4089S.TF j = pcomp 1100 11 (mask 11) (CFSG.KD.LQT.H4089S.TF (hsProg[j - 2]!).1)
        (CFSG.KD.LQT.H4089S.TF (hsProg[j - 2]!).2) := by
    intro j h2 h3
    have h28 : j / 8 < 28 := by omega
    have h := CFSG.KD.LQT.H4089S.N.all (j / 8) h28
    unfold CFSG.KD.LQT.H4089S.famN at h
    have hlo : Nat.mul (j / 8) 8 ≤ j := by
      rw [Nat.mul_eq]
      omega
    have hhi : j < Nat.mul (j / 8) 8 + 8 := by
      rw [Nat.mul_eq]
      omega
    rw [nodesT_spec h hlo hhi h2 h3]
    exact mulW_eq_pcomp _ _ (by norm_num) (by norm_num)
  have e : hsSLP = slpTabsA hsTa hsTb hsProg := rfl
  rw [e]
  exact slp_rep (by norm_num) (by norm_num) rep_ta rep_tb CFSG.KD.LQT.H4089S.valid hnd j (by omega)

theorem rep_ab (l : Nat) (hl : l < 2) :
    Rep 1100 11 (Lab l) ((#[hsTa, hsTb] : Array (Array Nat)).getD l #[]) := by
  rw [getD_toArray (by simpa using hl)]
  interval_cases l
  · have e : Lab 0 = CFSG.KD.LQT.H4089S.TF 0 := rfl
    rw [e, List.getElem!_cons_zero]
    exact rep_ta
  · have e : Lab 1 = CFSG.KD.LQT.H4089S.TF 1 := rfl
    rw [e, List.getElem!_cons_succ, List.getElem!_cons_zero]
    exact rep_tb

theorem rep_wd {k : Nat} (ws : List Nat) (hws : ∀ l ∈ ws, l < 2)
    (h : wordPB 1100 11 2047 Lab ws (TF 0) = TF k) :
    Rep 1100 11 (TF k) (wordTabA #[hsTa, hsTb] 1100 ws) := by
  have h' := rep_word (tabs := #[hsTa, hsTb]) (L := Lab) (by norm_num) (by norm_num) rep_id0 ws
    (fun l hl => rep_ab l (hws l hl))
  have hm : wordPB 1100 11 (mask 11) Lab ws (TF 0) = TF k := h
  rw [hm] at h'
  rw [wordTabA_foldr]
  exact h'

theorem rep_m1 : Rep 1100 11 (TF 1) (wordTabA #[hsTa, hsTb] 1100 hsW1) :=
  rep_wd hsW1 (by decide) (Nat.eq_of_beq_eq_true m1)

theorem rep_m2 : Rep 1100 11 (TF 2) (wordTabA #[hsTa, hsTb] 1100 hsW2) :=
  rep_wd hsW2 (by decide) (Nat.eq_of_beq_eq_true m2)

theorem hsL1_eq : hsL1 = [hsSLP[172]!, hsSLP[185]!, hsSLP[200]!,
    wordTabA #[hsTa, hsTb] 1100 hsW1] := rfl

theorem hsL2_eq : hsL2 = [hsSLP[172]!, hsSLP[185]!, hsSLP[200]!,
    wordTabA #[hsTa, hsTb] 1100 hsW2] := rfl

theorem hlen1 : hsL1.length = 4 := by rw [hsL1_eq]; rfl

theorem hlen2 : hsL2.length = 4 := by rw [hsL2_eq]; rfl

theorem hS (Lc : Nat → Nat) (L : List (Array Nat)) (m : Array Nat)
    (hL : L = [hsSLP[172]!, hsSLP[185]!, hsSLP[200]!, m])
    (h0 : Lc 0 = CFSG.KD.LQT.H4089S.TF 172) (h1 : Lc 1 = CFSG.KD.LQT.H4089S.TF 185)
    (h2 : Lc 2 = CFSG.KD.LQT.H4089S.TF 200) {c : Nat} (h3 : Lc 3 = c) (hm : Rep 1100 11 c m) :
    ∀ l < 4, Rep 1100 11 (Lc l) L[l]! := by
  intro l hl
  rw [hL]
  interval_cases l
  · rw [h0, List.getElem!_cons_zero]
    exact rep_nodes 172 (by norm_num)
  · rw [h1, List.getElem!_cons_succ, List.getElem!_cons_zero]
    exact rep_nodes 185 (by norm_num)
  · rw [h2, List.getElem!_cons_succ, List.getElem!_cons_succ, List.getElem!_cons_zero]
    exact rep_nodes 200 (by norm_num)
  · rw [h3, List.getElem!_cons_succ, List.getElem!_cons_succ, List.getElem!_cons_succ,
      List.getElem!_cons_zero]
    exact hm

theorem hL1 : ∀ l < 4, Rep 1100 11 (L1c l) hsL1[l]! :=
  hS L1c hsL1 _ hsL1_eq rfl rfl rfl rfl rep_m1

theorem hL2 : ∀ l < 4, Rep 1100 11 (L2c l) hsL2[l]! :=
  hS L2c hsL2 _ hsL2_eq rfl rfl rfl rfl rep_m2

theorem n_eq' : hsData.n = 1100 := rfl

theorem omega1 : OmegaSpec ptAct hsL1.toArray hsDelta hsOm1 := by
  refine omegaSpec_of_cp (n := 1100) (w := 11) (Lc := L1c) (fun l hl => hL1 l (hlen1 ▸ hl))
    rfl (by decide) ?_ ?_ nodup1
  · rw [hlen1]
    exact om1
  · rw [hlen1]
    exact tree1

theorem wit3_1 : Wit3Ok hsData.n ptAct hsL1 hsOm1.lbl.toList b31 q31a q31b := by
  have ea : qtW 1100 11 2047 (TF 0) L1c q31a.w q31a.k = TF 5 := Nat.eq_of_beq_eq_true x1t
  have eb : qtW 1100 11 2047 (TF 0) L1c q31b.w q31b.k = TF 7 := Nat.eq_of_beq_eq_true y1t
  have ma : powS 1100 11 2047 (TF 0) (TF 5) q31a.m = TF 0 := Nat.eq_of_beq_eq_true x1o
  have mb : powS 1100 11 2047 (TF 0) (TF 7) q31b.m = TF 0 := Nat.eq_of_beq_eq_true y1o
  have ia : powS 1100 11 2047 (TF 0) (TF 5) (q31a.m - 1) = TF 6 := Nat.eq_of_beq_eq_true x1i
  have ib : powS 1100 11 2047 (TF 0) (TF 7) (q31b.m - 1) = TF 8 := Nat.eq_of_beq_eq_true y1i
  have iB : powS 1100 11 2047 (TF 0) (TF 3) (b31.m - 1) = TF 4 := Nat.eq_of_beq_eq_true b1i
  rw [n_eq']
  refine wit3Ok_of_cp (n := 1100) (w := 11) (m := 2047) (idn := TF 0) (len := 4) (Lc := L1c)
    (tb := TF 3) (c₁ := TF 9) (c₂ := TF 10) (by norm_num) (by norm_num) (by rfl) rep_id0 hlen1
    hL1 (by decide) rfl (Nat.eq_of_beq_eq_true b1t) (ne_of_neB b1n) (Nat.eq_of_beq_eq_true b1o)
    ?_ ?_ ?_ (Or.inl (ne_of_neB c1n))
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · rw [ea]
      exact ⟨ma, x1l⟩
    · rw [eb]
      exact ⟨mb, y1l⟩
  · rw [ea, ia, iB]
    exact Nat.eq_of_beq_eq_true c1a
  · rw [eb, ib, iB]
    exact Nat.eq_of_beq_eq_true c1b

theorem witP_1 : WitPOk hsData.n ptAct hsL1 hsOm1.lbl.toList 5 b51 q51 := by
  rw [n_eq']
  exact witPOk_of_cp (n := 1100) (w := 11) (m := 2047) (idn := TF 0) (len := 4) (Lc := L1c)
    (by norm_num) (by norm_num) (by rfl) rep_id0 hlen1 hL1 (by decide) (Nat.eq_of_beq_eq_true p1t)
    (Nat.eq_of_beq_eq_true x1t) (ne_of_neB p1n) (Nat.eq_of_beq_eq_true p1o) x1l (ne_of_neB p1c)

theorem omega2 : OmegaSpec ptAct hsL2.toArray hsDelta hsOm2 := by
  refine omegaSpec_of_cp (n := 1100) (w := 11) (Lc := L2c) (fun l hl => hL2 l (hlen2 ▸ hl))
    rfl (by decide) ?_ ?_ nodup2
  · rw [hlen2]
    exact om2
  · rw [hlen2]
    exact tree2

theorem wit3_2 : Wit3Ok hsData.n ptAct hsL2 hsOm2.lbl.toList b32 q32a q32b := by
  have ea : qtW 1100 11 2047 (TF 0) L2c q32a.w q32a.k = TF 14 := Nat.eq_of_beq_eq_true x2t
  have eb : qtW 1100 11 2047 (TF 0) L2c q32b.w q32b.k = TF 16 := Nat.eq_of_beq_eq_true y2t
  have ma : powS 1100 11 2047 (TF 0) (TF 14) q32a.m = TF 0 := Nat.eq_of_beq_eq_true x2o
  have mb : powS 1100 11 2047 (TF 0) (TF 16) q32b.m = TF 0 := Nat.eq_of_beq_eq_true y2o
  have ia : powS 1100 11 2047 (TF 0) (TF 14) (q32a.m - 1) = TF 15 := Nat.eq_of_beq_eq_true x2i
  have ib : powS 1100 11 2047 (TF 0) (TF 16) (q32b.m - 1) = TF 17 := Nat.eq_of_beq_eq_true y2i
  have iB : powS 1100 11 2047 (TF 0) (TF 12) (b32.m - 1) = TF 13 := Nat.eq_of_beq_eq_true b2i
  rw [n_eq']
  refine wit3Ok_of_cp (n := 1100) (w := 11) (m := 2047) (idn := TF 0) (len := 4) (Lc := L2c)
    (tb := TF 12) (c₁ := TF 18) (c₂ := TF 19) (by norm_num) (by norm_num) (by rfl) rep_id0 hlen2
    hL2 (by decide) rfl (Nat.eq_of_beq_eq_true b2t) (ne_of_neB b2n) (Nat.eq_of_beq_eq_true b2o)
    ?_ ?_ ?_ (Or.inr (ne_of_neB c2n))
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · rw [ea]
      exact ⟨ma, x2l⟩
    · rw [eb]
      exact ⟨mb, y2l⟩
  · rw [ea, ia, iB]
    exact Nat.eq_of_beq_eq_true c2a
  · rw [eb, ib, iB]
    exact Nat.eq_of_beq_eq_true c2b

theorem witP_2 : WitPOk hsData.n ptAct hsL2 hsOm2.lbl.toList 7 b72 q72 := by
  rw [n_eq']
  exact witPOk_of_cp (n := 1100) (w := 11) (m := 2047) (idn := TF 0) (len := 4) (Lc := L2c)
    (by norm_num) (by norm_num) (by rfl) rep_id0 hlen2 hL2 (by decide) (Nat.eq_of_beq_eq_true p2t)
    (Nat.eq_of_beq_eq_true y2t) (ne_of_neB p2n) (Nat.eq_of_beq_eq_true p2o) y2l (ne_of_neB p2c)

theorem facts :
    (OmegaSpec ptAct hsL1.toArray hsDelta hsOm1 ∧ hsOm1.lbl.size = 15 ∧
      Wit3Ok hsData.n ptAct hsL1 hsOm1.lbl.toList b31 q31a q31b ∧
      WitPOk hsData.n ptAct hsL1 hsOm1.lbl.toList 5 b51 q51) ∧
    (OmegaSpec ptAct hsL2.toArray hsDelta hsOm2 ∧ hsOm2.lbl.size = 21 ∧
      Wit3Ok hsData.n ptAct hsL2 hsOm2.lbl.toList b32 q32a q32b ∧
      WitPOk hsData.n ptAct hsL2 hsOm2.lbl.toList 7 b72 q72) :=
  ⟨⟨omega1, rfl, wit3_1, witP_1⟩, ⟨omega2, rfl, wit3_2, witP_2⟩⟩

end CFSG.KD.LQT.H4089

end
