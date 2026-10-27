module

public import Certificates.Kernel.ONOutK3.Assemble

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONK3

open CFSG.KC.Enum CFSG.KC.ONK3 CFSG.KS.ONK3 CFSG.KS.Bfs3 CFSG.KS.BfsReplay
open CFSG.ComponentClassification.SolMax.ONOut CFSG.ONSchreier.Native
open CertificateChecks.KernelSpor.ON3 (ZT z_get tab_facts)

theorem G_lt {l : Nat} (hl : l < 3) {x : Nat} (hx : x < 245520) : G l x < 245520 :=
  (hArrs_get hl hx).2

theorem evalW_h : ∀ (w : List Nat), (∀ a ∈ w, a < 3) → ∀ x < 245520,
    evalW hArrs w x = evalWK G w x ∧ evalWK G w x < 245520
  | [], _, x, hx => ⟨rfl, hx⟩
  | a :: w, hw, x, hx => by
    obtain ⟨e, hlt⟩ := evalW_h w (fun b hb => hw b (List.mem_cons_of_mem a hb)) x hx
    have ha := hw a List.mem_cons_self
    have e1 : evalW hArrs (a :: w) x = (hArrs[a]!)[evalW hArrs w x]! := rfl
    have e2 : evalWK G (a :: w) x = G a (evalWK G w x) := rfl
    rw [e1, e2, e, (hArrs_get ha hlt).1]
    exact ⟨rfl, G_lt ha hlt⟩

theorem gword_lt : ∀ (d w x : Nat), x < 245520 → gword G d w x < 245520
  | 0, _, _, hx => hx
  | d + 1, w, x, hx => by
    rw [gword_succ]
    exact gword_lt d _ _ (by
      rcases (by omega : w % 4 < 3 ∨ w % 4 = 3) with h | h
      · exact G_lt h hx
      · rw [h]
        exact (hArrs_get (l := 2) (by decide) hx).2)

theorem evalW_v : ∀ (w : List Nat), (∀ a ∈ w, a < 3) → ∀ x < 245520,
    evalW vArrs w x = evalWK (uG G UL UW) w x ∧ evalWK (uG G UL UW) w x < 245520
  | [], _, x, hx => ⟨rfl, hx⟩
  | a :: w, hw, x, hx => by
    obtain ⟨e, hlt⟩ := evalW_v w (fun b hb => hw b (List.mem_cons_of_mem a hb)) x hx
    have ha := hw a List.mem_cons_self
    have e1 : evalW vArrs (a :: w) x = (vArrs[a]!)[evalW vArrs w x]! := rfl
    have e2 : evalWK (uG G UL UW) (a :: w) x = uG G UL UW a (evalWK (uG G UL UW) w x) := rfl
    rw [e1, e2, e, vArrs_get a ha _ hlt]
    exact ⟨rfl, gword_lt _ _ _ hlt⟩

theorem fw_eq {l : Nat} (hl : l < 2) : fw[l]! = FW l := by
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl

theorem FW_lets {l : Nat} (hl : l < 2) : ∀ a ∈ FW l, a < 3 := by
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> decide

theorem fStep_eq {l : Nat} (hl : l < 2) {x : Nat} (hx : x < 245520) :
    evalW hArrs fw[l]! x = fG G l x ∧ fG G l x < 245520 := by
  rw [fw_eq hl]
  exact evalW_h _ (FW_lets hl) x hx

theorem f_at {j : Nat} (hj : j < 60) : FAt G FL FK j := f_facts (fAll4 0 (by decide)) hj

theorem RF : R3 fStep 2 base3 60 (TF FL) (fun j => fPar (fRec FL j)) (fun j => fLab (fRec FL j))
    (fun j l => fPos (fRec FL j) l) := by
  have h0 : fAll G FL FK = true := fAll4 0 (by decide)
  have hb : ∀ j < 60, ∀ l < 2, fG G l (tA (fRec FL j)) < 2 ^ 18 ∧ fG G l (tB (fRec FL j)) < 2 ^ 18 ∧
      fG G l (tC (fRec FL j)) < 2 ^ 18 := fun j hj l hl =>
    ⟨Nat.lt_trans (fStep_eq hl (f_at hj).ltA).2 NP_lt, Nat.lt_trans (fStep_eq hl (f_at hj).ltB).2 NP_lt,
      Nat.lt_trans (fStep_eq hl (f_at hj).ltC).2 NP_lt⟩
  refine R3_congr (f_replay h0 hb) fun i hi l hl => ?_
  unfold fStep fStepK map3 TF
  rw [(fStep_eq hl (f_at hi).ltA).1, (fStep_eq hl (f_at hi).ltB).1, (fStep_eq hl (f_at hi).ltC).1]

theorem fTree_eq : fTree = (Array.ofFn (n := 60) fun i => fPar (fRec FL i.val),
    Array.ofFn (n := 60) fun i => fLab (fRec FL i.val), Array.ofFn (n := 60) fun i => TF FL i.val) :=
  bfs3_replay RF le_rfl

theorem fIm_eq : fIm = Array.ofFn (n := 60) fun i => TF FL i.val := by
  unfold fIm
  rw [fTree_eq]

theorem fIm_size : fIm.size = 60 := by rw [fIm_eq]; simp

theorem fIm_get {j : Nat} (hj : j < 60) : fIm[j]! = TF FL j := by
  rw [fIm_eq]
  exact ofFn_get3 hj

theorem fIm_inj : ∀ a < fIm.size, ∀ b < fIm.size, fIm[a]! = fIm[b]! → a = b := by
  intro a ha b hb e
  rw [fIm_size] at ha hb
  rw [fIm_get ha, fIm_get hb] at e
  exact RF.inj a ha b hb e

theorem zfIm_size : zfIm.size = 60 := by unfold zfIm; simp [fIm_size]

theorem zA_get {x : Nat} (hx : x < 245520) :
    (CFSG.ComponentClassification.SolMax.ONOut.zArr)[x]! = ZT x := (z_get x hx).1

theorem zfIm_get {j : Nat} (hj : j < 60) : zfIm[j]! = map3 ZT (TF FL j) := by
  unfold zfIm
  rw [getElem!_pos _ j (by simp [fIm_size]; exact hj), Array.getElem_map,
    ← getElem!_pos fIm j (by rw [fIm_size]; exact hj), fIm_get hj]
  unfold map3 TF
  dsimp only
  rw [zA_get (f_at hj).ltA, zA_get (f_at hj).ltB, zA_get (f_at hj).ltC]

theorem ZT_inv {x : Nat} (hx : x < 245520) : ZT (ZT x) = x := (tab_facts hx).2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem zfIm_inj : ∀ a < zfIm.size, ∀ b < zfIm.size, zfIm[a]! = zfIm[b]! → a = b := by
  intro a ha b hb e
  rw [zfIm_size] at ha hb
  rw [zfIm_get ha, zfIm_get hb] at e
  refine RF.inj a ha b hb ?_
  unfold map3 TF at e
  simp only [Prod.mk.injEq] at e
  unfold TF
  rw [← ZT_inv (f_at ha).ltA, ← ZT_inv (f_at ha).ltB, ← ZT_inv (f_at ha).ltC, e.1, e.2.1, e.2.2,
    ZT_inv (f_at hb).ltA, ZT_inv (f_at hb).ltB, ZT_inv (f_at hb).ltC]

theorem memK_spec {L x : Nat} : ∀ {n : Nat}, memK L n x = true → ∃ i < n, fld(L, Nat.mul 54 i, M54) = x
  | 0, h => (Bool.false_ne_true h).elim
  | n + 1, h => by
    change Bool.rec (motive := fun _ => Bool) (memK L n x) true
      (Nat.beq (fld(L, Nat.mul 54 n, M54)) x) = true at h
    by_cases e : fld(L, Nat.mul 54 n, M54) = x
    · exact ⟨n, Nat.lt_succ_self n, e⟩
    · rw [beqF e] at h
      obtain ⟨i, hi, e'⟩ := memK_spec h
      exact ⟨i, Nat.lt_succ_of_lt hi, e'⟩

theorem tK_triple {r r' : Nat} (h : tK r = tK r') : (tA r, tB r, tC r) = (tA r', tB r', tC r') := by
  rw [tK_eq, tK_eq] at h
  simp only [tA_eq, tB_eq, tC_eq, Prod.mk.injEq]
  omega

theorem cover : allBelowN 161280 cTest = true := by
  rw [CFSG.ONSchreier.allBelowN_iff]
  intro k hk
  unfold cTest
  rw [mSim_get k hk, mIm_get hk]
  by_cases e : sigF (nrec ONK3N k) = k
  · rw [e]
    simp only [beq_self_eq_true, Bool.not_true, Bool.false_or]
    obtain ⟨i, hi, hfi⟩ := memK_spec ((nodes_of hN hk).cover e)
    rcases Nat.lt_or_ge i 60 with h60 | h60
    · have e1 := (f_at h60).fk
      rw [hfi] at e1
      have ht : Tn ONK3N k = fIm[i]! := by rw [fIm_get h60]; exact tK_triple e1
      rw [Bool.or_eq_true]
      left
      have := (posMap3_mem fIm_size fIm_inj (Tn ONK3N k)).2 ⟨i, h60, ht.symm⟩
      exact this
    · have hi' : i - 60 < 60 := by omega
      have e1 := (f_at hi').fkz
      rw [show Nat.mul 54 (Nat.add 60 (i - 60)) = Nat.mul 54 i by
        change 54 * (60 + (i - 60)) = 54 * i; congr 1; omega, hfi] at e1
      have nl := (nodes_of hN hk)
      have ht : Tn ONK3N k = zfIm[i - 60]! := by
        rw [zfIm_get hi']
        have fa := f_at hi'
        obtain ⟨a1, a2, a3⟩ := key3_inj (Nat.lt_trans (z_get _ fa.ltA).2 NP_lt)
          (Nat.lt_trans (z_get _ fa.ltB).2 NP_lt) (Nat.lt_trans (z_get _ fa.ltC).2 NP_lt) e1.symm
        unfold Tn map3 TF
        rw [← a1, ← a2, ← a3]
      rw [Bool.or_eq_true]
      right
      exact (posMap3_mem zfIm_size zfIm_inj (Tn ONK3N k)).2 ⟨i - 60, hi', ht.symm⟩
  · have hne : (Tn ONK3N (sigF (nrec ONK3N k)) == Tn ONK3N k) = false := by
      rw [beq_eq_false_iff_ne]
      intro h
      exact e ((Tn_inj (sig_lt' hk) hk).1 h)
    rw [hne]
    rfl

end CertificateChecks.KernelSpor.ONK3

end
