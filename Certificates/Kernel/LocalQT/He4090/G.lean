module

public import Certificates.Kernel.LocalQT.He4090.C1
public import Certificates.Kernel.LocalQT.He4090.C2
public import Certificates.Kernel.LocalQT.He4090.C3
public import Certificates.Kernel.LocalQT.He4090.C4
public import Certificates.Kernel.LocalQT.Base.C4141
public import CFSG.Certificates.Kernel.LocalQTPcWSound

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LQT.H4090

open CFSG.KC.Enum CFSG.KS CFSG.KS.PF CFSG.KC.LQT.PcW CFSG.KS.PEnum
open CFSG.QuasithinUnique.Ch1.SporLat (idTab QuotGen wordTabA ptAct)
open CFSG.QuasithinUnique.Ch1.SporLat.He (heMwLit heLabels2 heLabels7)
open CFSG.QuasithinUnique.K1.SporadicPerm (heTa heTb heSLP heProg slpTabsA heQp)
open CFSG.QuasithinUnique.Vol2Native.L239 (CntOk Wit3Ok WitPOk)
open CFSG.QuasithinUnique.Vol2Native.L239.HePairs

theorem rep_id0 : Rep 8330 14 (TF 0) (idTab 8330) := by
  have e := Nat.eq_of_beq_eq_true idc
  have h := rep_id (n := 8330) (w := 14) (by norm_num) (by norm_num)
  rw [e] at h
  exact h

theorem rep_ta : Rep 8330 14 (CFSG.KD.LQT.C4141.TF 0) heTa := by
  rw [CFSG.KD.LQT.C4141.ta_eq]
  exact rep_of_canon (m := 16383) (nw := 116620) (F := pg 14 16383 (CFSG.KD.He4049.TF 0)) (by rfl)
    (by rfl) canonA bindA

theorem rep_tb : Rep 8330 14 (CFSG.KD.LQT.C4141.TF 1) heTb := by
  rw [CFSG.KD.LQT.C4141.tb_eq]
  exact rep_of_canon (m := 16383) (nw := 116620) (F := pg 14 16383 (CFSG.KD.He4049.TF 1)) (by rfl)
    (by rfl) canonB bindB

theorem rep_nodes (j : Nat) (hj : j < 267) : Rep 8330 14 (CFSG.KD.LQT.C4141.TF j) heSLP[j]! := by
  have hlen : heProg.length = 265 := rfl
  have hnd : ∀ j, 2 ≤ j → j < heProg.length + 2 →
      CFSG.KD.LQT.C4141.TF j = pcomp 8330 14 (mask 14) (CFSG.KD.LQT.C4141.TF (heProg[j - 2]!).1)
        (CFSG.KD.LQT.C4141.TF (heProg[j - 2]!).2) := by
    intro j h2 h3
    have h34 : j / 8 < 34 := by omega
    have h := CFSG.KD.LQT.C4141.N.all (j / 8) h34
    unfold CFSG.KD.LQT.C4141.famN at h
    have hlo : Nat.mul (j / 8) 8 ≤ j := by
      rw [Nat.mul_eq]
      omega
    have hhi : j < Nat.mul (j / 8) 8 + 8 := by
      rw [Nat.mul_eq]
      omega
    rw [nodesT_spec h hlo hhi h2 h3]
    exact mulW_eq_pcomp _ _ (by norm_num) (by norm_num)
  exact slp_rep (by norm_num) (by norm_num) rep_ta rep_tb CFSG.KD.LQT.C4141.valid hnd j (by omega)

theorem rep_ab (l : Nat) (hl : l < 2) :
    Rep 8330 14 (Lab l) ((#[heTa, heTb] : Array (Array Nat)).getD l #[]) := by
  rw [getD_toArray (by simpa using hl)]
  interval_cases l
  · have e : Lab 0 = CFSG.KD.LQT.C4141.TF 0 := rfl
    rw [e, List.getElem!_cons_zero]
    exact rep_ta
  · have e : Lab 1 = CFSG.KD.LQT.C4141.TF 1 := rfl
    rw [e, List.getElem!_cons_succ, List.getElem!_cons_zero]
    exact rep_tb

theorem rep_m2 : Rep 8330 14 (TF 1)
    (wordTabA #[heTa, heTb] 8330 [1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1]) := by
  have e0 := Nat.eq_of_beq_eq_true m2
  have e : wordPB 8330 14 (mask 14) Lab [1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1] (TF 0) =
      TF 1 := e0
  have h := rep_word (tabs := #[heTa, heTb]) (L := Lab) (by norm_num) (by norm_num) rep_id0
    [1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1] (fun l hl => rep_ab l (by simp at hl; omega))
  rw [e] at h
  rw [wordTabA_foldr]
  exact h

theorem rep_m7 : Rep 8330 14 (TF 3)
    (wordTabA #[heTa, heTb] 8330 [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1,
      0]) := by
  have e10 := Nat.eq_of_beq_eq_true m7lo
  have e1 : wordPB 8330 14 (mask 14) Lab [1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0] (TF 0) = TF 2 := e10
  have e20 := Nat.eq_of_beq_eq_true m7
  have e2 : wordPB 8330 14 (mask 14) Lab [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1] (TF 2) = TF 3 := e20
  have h1 := rep_word (tabs := #[heTa, heTb]) (L := Lab) (by norm_num) (by norm_num) rep_id0
    [1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0] (fun l hl => rep_ab l (by simp at hl; omega))
  rw [e1] at h1
  have h2 := rep_word (tabs := #[heTa, heTb]) (L := Lab) (by norm_num) (by norm_num) h1
    [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1] (fun l hl => rep_ab l (by simp at hl; omega))
  rw [e2, ← List.foldr_append] at h2
  rw [wordTabA_foldr]
  exact h2

theorem heL2_eq : heL2 = [heSLP[197]!, heSLP[207]!, heSLP[226]!, heSLP[247]!,
    wordTabA #[heTa, heTb] 8330 [1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1]] := rfl

theorem heL7_eq : heL7 = [heSLP[197]!, heSLP[207]!, heSLP[226]!, heSLP[247]!,
    wordTabA #[heTa, heTb] 8330 [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1,
      0]] := rfl

theorem hL2 : ∀ l < 5, Rep 8330 14 (L2c l) heL2[l]! := by
  intro l hl
  rw [heL2_eq]
  interval_cases l
  · have e : L2c 0 = CFSG.KD.LQT.C4141.TF 197 := rfl
    rw [e, List.getElem!_cons_zero]
    exact rep_nodes 197 (by norm_num)
  · have e : L2c 1 = CFSG.KD.LQT.C4141.TF 207 := rfl
    rw [e, List.getElem!_cons_succ, List.getElem!_cons_zero]
    exact rep_nodes 207 (by norm_num)
  · have e : L2c 2 = CFSG.KD.LQT.C4141.TF 226 := rfl
    rw [e, List.getElem!_cons_succ, List.getElem!_cons_succ, List.getElem!_cons_zero]
    exact rep_nodes 226 (by norm_num)
  · have e : L2c 3 = CFSG.KD.LQT.C4141.TF 247 := rfl
    rw [e, List.getElem!_cons_succ, List.getElem!_cons_succ, List.getElem!_cons_succ,
      List.getElem!_cons_zero]
    exact rep_nodes 247 (by norm_num)
  · have e : L2c 4 = TF 1 := rfl
    rw [e, List.getElem!_cons_succ, List.getElem!_cons_succ, List.getElem!_cons_succ,
      List.getElem!_cons_succ, List.getElem!_cons_zero]
    exact rep_m2

theorem hL7 : ∀ l < 5, Rep 8330 14 (L7c l) heL7[l]! := by
  intro l hl
  rw [heL7_eq]
  interval_cases l
  · have e : L7c 0 = CFSG.KD.LQT.C4141.TF 197 := rfl
    rw [e, List.getElem!_cons_zero]
    exact rep_nodes 197 (by norm_num)
  · have e : L7c 1 = CFSG.KD.LQT.C4141.TF 207 := rfl
    rw [e, List.getElem!_cons_succ, List.getElem!_cons_zero]
    exact rep_nodes 207 (by norm_num)
  · have e : L7c 2 = CFSG.KD.LQT.C4141.TF 226 := rfl
    rw [e, List.getElem!_cons_succ, List.getElem!_cons_succ, List.getElem!_cons_zero]
    exact rep_nodes 226 (by norm_num)
  · have e : L7c 3 = CFSG.KD.LQT.C4141.TF 247 := rfl
    rw [e, List.getElem!_cons_succ, List.getElem!_cons_succ, List.getElem!_cons_succ,
      List.getElem!_cons_zero]
    exact rep_nodes 247 (by norm_num)
  · have e : L7c 4 = TF 3 := rfl
    rw [e, List.getElem!_cons_succ, List.getElem!_cons_succ, List.getElem!_cons_succ,
      List.getElem!_cons_succ, List.getElem!_cons_zero]
    exact rep_m7

theorem hallQ : ∀ k < 5, (∀ l ∈ (nthQ q2s k).w, l < 5) ∧ 0 < (nthQ q2s k).m ∧
    powS 8330 14 16383 (TF 0) (qtW 8330 14 16383 (TF 0) L2c (nthQ q2s k).w (nthQ q2s k).k)
      (nthQ q2s k).m = TF 0 ∧
    labsK 8330 14 16383 (qtW 8330 14 16383 (TF 0) L2c (nthQ q2s k).w (nthQ q2s k).k)
      heLabels2 = true := by
  intro k hk
  have ht := QT.all k hk
  have hm := QM.all k hk
  have hl := QL.all k hk
  unfold famQT at ht
  unfold famQM at hm
  unfold famQL at hl
  have et := Nat.eq_of_beq_eq_true ht
  have em := Nat.eq_of_beq_eq_true hm
  refine ⟨by interval_cases k <;> decide, by interval_cases k <;> decide, ?_, ?_⟩
  · rw [et]
    exact em
  · rw [et]
    exact hl

theorem eqQ (k : Nat) (hk : k < 5) :
    qtW 8330 14 16383 (TF 0) L2c (nthQ q2s k).w (nthQ q2s k).k = TF (Nat.add 6 k) ∧
      powS 8330 14 16383 (TF 0) (TF (Nat.add 6 k)) (Nat.sub (nthQ q2s k).m 1) =
        TF (Nat.add 11 k) := by
  have ht := QT.all k hk
  have hi := QI.all k hk
  unfold famQT at ht
  unfold famQI at hi
  exact ⟨Nat.eq_of_beq_eq_true ht, Nat.eq_of_beq_eq_true hi⟩

theorem hmapQ (X X2 : Nat) :
    q2s.map (fun q => commS 8330 14 16383 (qtW 8330 14 16383 (TF 0) L2c q.w q.k) X
      (powS 8330 14 16383 (TF 0) (qtW 8330 14 16383 (TF 0) L2c q.w q.k) (q.m - 1)) X2) =
    [commS 8330 14 16383 (TF 6) X (TF 11) X2, commS 8330 14 16383 (TF 7) X (TF 12) X2,
      commS 8330 14 16383 (TF 8) X (TF 13) X2, commS 8330 14 16383 (TF 9) X (TF 14) X2,
      commS 8330 14 16383 (TF 10) X (TF 15) X2] := by
  have hq2 : q2s = [nthQ q2s 0, nthQ q2s 1, nthQ q2s 2, nthQ q2s 3, nthQ q2s 4] := rfl
  have t0 : qtW 8330 14 16383 (TF 0) L2c (nthQ q2s 0).w (nthQ q2s 0).k = TF 6 := (eqQ 0 (by norm_num)).1
  have t1 : qtW 8330 14 16383 (TF 0) L2c (nthQ q2s 1).w (nthQ q2s 1).k = TF 7 := (eqQ 1 (by norm_num)).1
  have t2 : qtW 8330 14 16383 (TF 0) L2c (nthQ q2s 2).w (nthQ q2s 2).k = TF 8 := (eqQ 2 (by norm_num)).1
  have t3 : qtW 8330 14 16383 (TF 0) L2c (nthQ q2s 3).w (nthQ q2s 3).k = TF 9 := (eqQ 3 (by norm_num)).1
  have t4 : qtW 8330 14 16383 (TF 0) L2c (nthQ q2s 4).w (nthQ q2s 4).k = TF 10 :=
    (eqQ 4 (by norm_num)).1
  have i0 : powS 8330 14 16383 (TF 0) (TF 6) ((nthQ q2s 0).m - 1) = TF 11 := (eqQ 0 (by norm_num)).2
  have i1 : powS 8330 14 16383 (TF 0) (TF 7) ((nthQ q2s 1).m - 1) = TF 12 := (eqQ 1 (by norm_num)).2
  have i2 : powS 8330 14 16383 (TF 0) (TF 8) ((nthQ q2s 2).m - 1) = TF 13 := (eqQ 2 (by norm_num)).2
  have i3 : powS 8330 14 16383 (TF 0) (TF 9) ((nthQ q2s 3).m - 1) = TF 14 := (eqQ 3 (by norm_num)).2
  have i4 : powS 8330 14 16383 (TF 0) (TF 10) ((nthQ q2s 4).m - 1) = TF 15 :=
    (eqQ 4 (by norm_num)).2
  rw [hq2]
  simp only [List.map_cons, List.map_nil]
  rw [t0, t1, t2, t3, t4, i0, i1, i2, i3, i4]

theorem cnt : CntOk 8330 ptAct heL2 heLabels2 r2a r2b q2s := by
  have ht1 := Nat.eq_of_beq_eq_true r1
  have ht2 := Nat.eq_of_beq_eq_true r2
  have h3 := Nat.eq_of_beq_eq_true r1c
  have h4 := Nat.eq_of_beq_eq_true r2c
  have h5 := Nat.eq_of_beq_eq_true rcm
  refine cntOk_of_cp (n := 8330) (w := 14) (m := 16383) (idn := TF 0) (len := 5) (Lc := L2c)
    (by norm_num) (by norm_num) (by rfl) rep_id0 rfl hL2 (by decide) (by decide) ht1 ht2
    (ne_of_neB r1ne) (ne_of_neB r2ne) h3 h4 h5 (ne_of_neB r21) (ne_of_neB r212) (by decide)
    ?_ ?_
  · intro q hq
    simp only [q2s, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact hallQ 0 (by norm_num)
    · exact hallQ 1 (by norm_num)
    · exact hallQ 2 (by norm_num)
    · exact hallQ 3 (by norm_num)
    · exact hallQ 4 (by norm_num)
  · intro i hi j hj hij
    have hx : ∀ t < 8, rijS 8330 14 16383 (TF 0) (TF 4) (TF 5) (Nat.div (Nat.succ t) 3)
        (Nat.mod (Nat.succ t) 3) = TF (Nat.add 16 t) ∧
        powS 8330 14 16383 (TF 0) (TF (Nat.add 16 t)) 2 = TF (Nat.add 24 t) := by
      intro t ht
      have a := X.all t ht
      have b := X2.all t ht
      unfold famX at a
      unfold famX2 at b
      exact ⟨Nat.eq_of_beq_eq_true a, Nat.eq_of_beq_eq_true b⟩
    have hcm : ∀ t < 8, (distF [commS 8330 14 16383 (TF 6) (TF (Nat.add 16 t)) (TF 11) (TF (Nat.add 24 t)),
        commS 8330 14 16383 (TF 7) (TF (Nat.add 16 t)) (TF 12) (TF (Nat.add 24 t)),
        commS 8330 14 16383 (TF 8) (TF (Nat.add 16 t)) (TF 13) (TF (Nat.add 24 t)),
        commS 8330 14 16383 (TF 9) (TF (Nat.add 16 t)) (TF 14) (TF (Nat.add 24 t)),
        commS 8330 14 16383 (TF 10) (TF (Nat.add 16 t)) (TF 15) (TF (Nat.add 24 t))] []) = true := by
      intro t ht
      have c := Cm.all t ht
      unfold famC at c
      exact c
    have key : ∀ t < 8, (q2s.map fun q => commS 8330 14 16383
        (qtW 8330 14 16383 (TF 0) L2c q.w q.k)
        (rijS 8330 14 16383 (TF 0) (TF 4) (TF 5) (Nat.div (Nat.succ t) 3) (Nat.mod (Nat.succ t) 3))
        (powS 8330 14 16383 (TF 0) (qtW 8330 14 16383 (TF 0) L2c q.w q.k) (q.m - 1))
        (powS 8330 14 16383 (TF 0)
          (rijS 8330 14 16383 (TF 0) (TF 4) (TF 5) (Nat.div (Nat.succ t) 3) (Nat.mod (Nat.succ t) 3))
          2)).Nodup := by
      intro t ht
      rw [(hx t ht).1, (hx t ht).2, hmapQ]
      exact (distF_spec (hcm t ht)).1
    interval_cases i <;> interval_cases j
    · omega
    · exact key 0 (by norm_num)
    · exact key 1 (by norm_num)
    · exact key 2 (by norm_num)
    · exact key 3 (by norm_num)
    · exact key 4 (by norm_num)
    · exact key 5 (by norm_num)
    · exact key 6 (by norm_num)
    · exact key 7 (by norm_num)

theorem wit3 : Wit3Ok 8330 ptAct heL7 heLabels7 b7a q7a q7b := by
  have htb := Nat.eq_of_beq_eq_true b7a_t
  have h2 := Nat.eq_of_beq_eq_true b7a_3
  have ea := Nat.eq_of_beq_eq_true q7a_t
  have eb := Nat.eq_of_beq_eq_true q7b_t
  have ma := Nat.eq_of_beq_eq_true q7a_m
  have mb := Nat.eq_of_beq_eq_true q7b_m
  have ia := Nat.eq_of_beq_eq_true q7a_i
  have ib := Nat.eq_of_beq_eq_true q7b_i
  have iB := Nat.eq_of_beq_eq_true b7a_i
  have e1 := Nat.eq_of_beq_eq_true c1
  have e2 := Nat.eq_of_beq_eq_true c2
  refine wit3Ok_of_cp (n := 8330) (w := 14) (m := 16383) (idn := TF 0) (len := 5) (Lc := L7c)
    (tb := TF 32) (c₁ := TF 39) (c₂ := TF 40) (by norm_num) (by norm_num) (by rfl) rep_id0 rfl hL7 (by decide) rfl htb (ne_of_neB b7a_ne) h2
    ?_ ?_ ?_ (Or.inr (ne_of_neB c11))
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · rw [ea]
      exact ⟨ma, q7a_l⟩
    · rw [eb]
      exact ⟨mb, q7b_l⟩
  · rw [ea, ia, iB]
    exact e1
  · rw [eb, ib, iB]
    exact e2

theorem witP : WitPOk 8330 ptAct heL7 heLabels7 7 b7p q7p := by
  have htb := Nat.eq_of_beq_eq_true b7p_t
  have htq := Nat.eq_of_beq_eq_true q7p_t
  have h2 := Nat.eq_of_beq_eq_true b7p_7
  exact witPOk_of_cp (n := 8330) (w := 14) (m := 16383) (idn := TF 0) (len := 5) (Lc := L7c)
    (by norm_num) (by norm_num) (by rfl) rep_id0 rfl hL7 (by decide) htb htq (ne_of_neB b7p_ne) h2
    q7b_l (ne_of_neB pq)

end CFSG.KD.LQT.H4090

end
