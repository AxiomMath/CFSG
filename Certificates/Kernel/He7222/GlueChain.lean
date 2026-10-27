module

public import Certificates.Kernel.He7222.ChainK
public import Certificates.Kernel.He7222.FixK
public import Certificates.Kernel.He7223.GlueCent
public import CFSG.Certificates.Kernel.He7222.ChainPRep
public import CFSG.Sporadic.HeldB.InnerClass
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.OrbRow.LevelSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHe7222

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.OrbRow CFSG.KC.HeChain CFSG.KS.Raw.Orb
  CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.KD.He7222 CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.He CFSG.Sporadic.HeldB
  CFSG.Sporadic.Schreier CFSG.Monster.B.Co2.Native CertificateChecks.KernelLC.HeFix
  CertificateChecks.KernelHe7223 CertificateChecks.KernelSchreierFam.He725

@[expose] noncomputable def t1Gs (i : ℕ) : List ℕ := [t1G, t1S1, t1S2, t1S3, t1S4, t1S5, t1S6].getD i []

@[expose] noncomputable def t1Ns (i : ℕ) : List ℕ := [t1N1, t1N2, t1N3, t1N4, t1N5, t1N6].getD i []

@[expose] noncomputable def t1Tl (i : ℕ) : List ℕ := t1Ts.getD i []

theorem t1_tree : ∀ i < 7, treeK 8330 14 (mask 14) (pidn 8330 14) (t1Gs i) (getS t1Base i)
    (getLs t1Tree i) (t1Tl i) = true
  | 0, _ => ch7222t1t0
  | 1, _ => ch7222t1t1
  | 2, _ => ch7222t1t2
  | 3, _ => ch7222t1t3
  | 4, _ => ch7222t1t4
  | 5, _ => ch7222t1t5
  | 6, _ => ch7222t1t6
  | _ + 7, h => absurd h (by omega)

theorem t1_sch : ∀ i, i + 1 < 7 → schK 8330 14 (mask 14) (t1Gs i) (getS t1Base i) (getLs t1Tree i)
    (t1Tl i) (getLs t1LGens (i + 1)) (t1Ns i) (t1Gs (i + 1)) = true
  | 0, _ => ch7222t1s1
  | 1, _ => ch7222t1s2
  | 2, _ => ch7222t1s3
  | 3, _ => ch7222t1s4
  | 4, _ => ch7222t1s5
  | 5, _ => ch7222t1s6
  | _ + 6, h => absurd h (by omega)

theorem ch7222t1bl : (Nat.blt (getS t1Base 0) 8330 && Nat.blt (getS t1Base 1) 8330 &&
    Nat.blt (getS t1Base 2) 8330 && Nat.blt (getS t1Base 3) 8330 && Nat.blt (getS t1Base 4) 8330 &&
    Nat.blt (getS t1Base 5) 8330 && Nat.blt (getS t1Base 6) 8330) = true := by quickRfl

theorem t1_base_lt : ∀ i < 7, getS t1Base i < 8330 := by
  have h := ch7222t1bl
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  intro i hi
  match i, hi with
  | 0, _ => exact h0
  | 1, _ => exact h1
  | 2, _ => exact h2
  | 3, _ => exact h3
  | 4, _ => exact h4
  | 5, _ => exact h5
  | 6, _ => exact h6

theorem ch7222t1len : (Nat.beq (lenS t1T0) 42 && Nat.beq (lenS t1T1) 4 && Nat.beq (lenS t1T2) 2 &&
    Nat.beq (lenS t1T3) 4 && Nat.beq (lenS t1T4) 4 && Nat.beq (lenS t1T5) 2 &&
    Nat.beq (lenS t1T6) 2) = true := by quickRfl

theorem t1_prod : ∏ i ∈ Finset.range 7, (t1Tl i).length = 21504 := by
  have h := ch7222t1len
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, t1Tl, t1Ts, List.getD_cons_zero,
    List.getD_cons_succ, ← lenS_eq, Nat.eq_of_beq_eq_true h0, Nat.eq_of_beq_eq_true h1,
    Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4,
    Nat.eq_of_beq_eq_true h5, Nat.eq_of_beq_eq_true h6]
  rfl

theorem c1W_letters : lettersOK 2 (gw 9) = true ∧ lettersOK 2 (gw 10) = true := by decide +kernel

theorem t1_gens :
    ∀ q < (t1Gs 0).length, ∃ g ∈ centralizerIn heP heT1P,
      PRep 8330 14 ((t1Gs 0).getD q 0) g := by
  have hg := ch7222g1
  simp only [Bool.and_eq_true] at hg
  obtain ⟨⟨h0', h1'⟩, hl'⟩ := hg
  have h0 : t1G.getD 0 0 = PC5 := by rw [← getS_eq]; exact Nat.eq_of_beq_eq_true h0'
  have h1 : t1G.getD 1 0 = PC10 := by rw [← getS_eq]; exact Nat.eq_of_beq_eq_true h1'
  have hl : t1G.length = 2 := by rw [← lenS_eq]; exact Nat.eq_of_beq_eq_true hl'
  have hmem : ∀ j < 3, j < 2 → hsL.getD j 1 ∈ centralizerIn heP heT1P := by
    intro j hj hj2
    have hjm : hsL.getD j 1 ∈ hsL := by
      rw [List.getD_eq_getElem _ _ (by simp [hsL]; omega)]
      exact List.getElem_mem _
    have hc := hs_mem_CR (hsL.getD j 1) hjm
    rw [mem_centralizerIn] at hc ⊢
    refine ⟨?_, hc.2⟩
    match j, hj2 with
    | 0, _ => exact elt_mem_heP c1W_letters.1
    | 1, _ => exact elt_mem_heP c1W_letters.2
  intro q hq
  have hq2 : q < 2 := by
    change q < t1G.length at hq
    omega
  refine ⟨hsL.getD q 1, hmem q (by omega) hq2, ?_⟩
  have hr := prep_of_rep (rep_HC (j := q) (by omega))
  change PRep 8330 14 (t1G.getD q 0) _
  match q, hq2 with
  | 0, _ =>
    rw [h0]
    exact hr
  | 1, _ =>
    rw [h1]
    exact hr

theorem t1_cent_chain :
    (∀ i < 7, ∀ j < (t1Tl i).length, recP 8330 14 ((t1Tl i).getD j 0) ∈ centralizerIn heP heT1P ∧
      PRep 8330 14 ((t1Tl i).getD j 0) (recP 8330 14 ((t1Tl i).getD j 0)) ∧
      ∀ t < i, recP 8330 14 ((t1Tl i).getD j 0) (baseF (by norm_num) (getS t1Base) t) =
        baseF (by norm_num) (getS t1Base) t) ∧
    ∀ g ∈ centralizerIn heP heT1P, ∃ f : ℕ → ℕ, (∀ i < 7, f i < (t1Tl i).length) ∧
      g = ((List.range 7).map fun i => recP 8330 14 ((t1Tl i).getD (f i) 0)).prod :=
  chain_prep (by norm_num) (by norm_num) (by norm_num) 7 t1Gs (getS t1Base) (getLs t1Tree) t1Tl
    (fun i => getLs t1LGens (i + 1)) t1Ns t1_base_lt t1_tree t1_sch _ t1_gens
    (by rw [card_heP_cent1, t1_prod])

@[expose] noncomputable def a0Gs (i : ℕ) : List ℕ :=
  [a0G, a0S1, a0S2, a0S3, a0S4, a0S5, a0S6, a0S7].getD i []

@[expose] noncomputable def a0Ns (i : ℕ) : List ℕ :=
  [a0N1, a0N2, a0N3, a0N4, a0N5, a0N6, a0N7].getD i []

@[expose] noncomputable def a0Tl (i : ℕ) : List ℕ := a0Ts.getD i []

theorem a0_tree : ∀ i < 8, treeK 8330 14 (mask 14) (pidn 8330 14) (a0Gs i) (getS a0Base i)
    (getLs a0Tree i) (a0Tl i) = true
  | 0, _ => ch7222a0t0
  | 1, _ => ch7222a0t1
  | 2, _ => ch7222a0t2
  | 3, _ => ch7222a0t3
  | 4, _ => ch7222a0t4
  | 5, _ => ch7222a0t5
  | 6, _ => ch7222a0t6
  | 7, _ => ch7222a0t7
  | _ + 8, h => absurd h (by omega)

theorem a0_sch : ∀ i, i + 1 < 8 → schK 8330 14 (mask 14) (a0Gs i) (getS a0Base i) (getLs a0Tree i)
    (a0Tl i) (getLs a0LGens (i + 1)) (a0Ns i) (a0Gs (i + 1)) = true
  | 0, _ => ch7222a0s1
  | 1, _ => ch7222a0s2
  | 2, _ => ch7222a0s3
  | 3, _ => ch7222a0s4
  | 4, _ => ch7222a0s5
  | 5, _ => ch7222a0s6
  | 6, _ => ch7222a0s7
  | _ + 7, h => absurd h (by omega)

theorem ch7222a0bl : (Nat.blt (getS a0Base 0) 8330 && Nat.blt (getS a0Base 1) 8330 &&
    Nat.blt (getS a0Base 2) 8330 && Nat.blt (getS a0Base 3) 8330 && Nat.blt (getS a0Base 4) 8330 &&
    Nat.blt (getS a0Base 5) 8330 && Nat.blt (getS a0Base 6) 8330 &&
    Nat.blt (getS a0Base 7) 8330) = true := by quickRfl

theorem a0_base_lt : ∀ i < 8, getS a0Base i < 8330 := by
  have h := ch7222a0bl
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  intro i hi
  match i, hi with
  | 0, _ => exact h0
  | 1, _ => exact h1
  | 2, _ => exact h2
  | 3, _ => exact h3
  | 4, _ => exact h4
  | 5, _ => exact h5
  | 6, _ => exact h6
  | 7, _ => exact h7

theorem ch7222a0len : (Nat.beq (lenS a0T0) 105 && Nat.beq (lenS a0T1) 4 &&
    Nat.beq (lenS a0T2) 3 && Nat.beq (lenS a0T3) 2 && Nat.beq (lenS a0T4) 4 &&
    Nat.beq (lenS a0T5) 4 && Nat.beq (lenS a0T6) 2 && Nat.beq (lenS a0T7) 2) = true := by quickRfl

theorem a0_prod : ∏ i ∈ Finset.range 8, (a0Tl i).length = 161280 := by
  have h := ch7222a0len
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, a0Tl, a0Ts, List.getD_cons_zero,
    List.getD_cons_succ, ← lenS_eq, Nat.eq_of_beq_eq_true h0, Nat.eq_of_beq_eq_true h1,
    Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4,
    Nat.eq_of_beq_eq_true h5, Nat.eq_of_beq_eq_true h6, Nat.eq_of_beq_eq_true h7]
  rfl

theorem CW_letters : lettersOK 2 (CW.getD 0 []) = true ∧ lettersOK 2 (CW.getD 1 []) = true := by
  decide +kernel

theorem prep_a0 :
    PRep 8330 14 (HG.F 0) (heGenPerm 0) := by
  have h := (letRep_LU 0 (by simp [gens3])).1
  have e : gens3.getD 0 1 = heGenPerm 0 := by simp only [gens3, List.getD_cons_zero]
  rw [LU_0, e] at h
  intro x
  exact h x

theorem comm_of_commK {p q : ℕ} {g a : Equiv.Perm (Fin 8330)}
    (h : commK 8330 14 (mask 14) (8330 * 14) p q = true) (hp : PRep 8330 14 p g)
    (hq : PRep 8330 14 q a) : g * a = a * g := by
  unfold commK at h
  rw [bAnd_iff, bAnd_iff] at h
  have he := Nat.eq_of_beq_eq_true h.2.2
  have h1 := prep_pcomp (by norm_num) hp hq
  have h2 := prep_pcomp (by norm_num) hq hp
  rw [he] at h1
  exact prep_unique h1 h2

theorem a0_gens :
    ∀ q < (a0Gs 0).length, ∃ g ∈ centralizerIn heP (heGenPerm 0),
      PRep 8330 14 ((a0Gs 0).getD q 0) g := by
  have hw := ch7222w
  simp only [Bool.and_eq_true] at hw
  obtain ⟨⟨hw0, hw1⟩, hl'⟩ := hw
  have hl : a0G.length = 2 := by rw [← lenS_eq]; exact Nat.eq_of_beq_eq_true hl'
  have hcm := ch7222cm
  simp only [Bool.and_eq_true] at hcm
  have hca := commAllK_sound hcm.1
  have key : ∀ q < 2, wordEqK 8330 14 (mask 14) (pidn 8330 14) LU LUI 3 (CW.getD q [])
      (getS a0G q) = true → lettersOK 2 (CW.getD q []) = true →
      ∃ g ∈ centralizerIn heP (heGenPerm 0), PRep 8330 14 (a0G.getD q 0) g := by
    intro q hq hwq hlq
    have hrep : Rep 8330 (unpack 8330 14 (getS a0G q)) (elt (CW.getD q [])) := by
      rw [← (wordEqK_sound gA_bind kPLU hwq).1]
      exact rep_wA (lettersOK_mono (by norm_num) hlq)
    have hp := prep_of_rep hrep
    rw [getS_eq] at hp
    have hmem : a0G.getD q 0 ∈ a0G := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_mem _
    have hc := comm_of_commK (hca _ hmem) hp prep_a0
    exact ⟨_, mem_centralizerIn.2 ⟨elt_mem_heP hlq, hc⟩, hp⟩
  intro q hq
  have hq2 : q < 2 := by
    change q < a0G.length at hq
    omega
  change ∃ g ∈ centralizerIn heP (heGenPerm 0), PRep 8330 14 (a0G.getD q 0) g
  match q, hq2 with
  | 0, _ => exact key 0 (by norm_num) hw0 CW_letters.1
  | 1, _ => exact key 1 (by norm_num) hw1 CW_letters.2

theorem a0_cent_chain :
    (∀ i < 8, ∀ j < (a0Tl i).length,
      recP 8330 14 ((a0Tl i).getD j 0) ∈ centralizerIn heP (heGenPerm 0) ∧
      PRep 8330 14 ((a0Tl i).getD j 0) (recP 8330 14 ((a0Tl i).getD j 0)) ∧
      ∀ t < i, recP 8330 14 ((a0Tl i).getD j 0) (baseF (by norm_num) (getS a0Base) t) =
        baseF (by norm_num) (getS a0Base) t) ∧
    ∀ g ∈ centralizerIn heP (heGenPerm 0), ∃ f : ℕ → ℕ, (∀ i < 8, f i < (a0Tl i).length) ∧
      g = ((List.range 8).map fun i => recP 8330 14 ((a0Tl i).getD (f i) 0)).prod :=
  chain_prep (by norm_num) (by norm_num) (by norm_num) 8 a0Gs (getS a0Base) (getLs a0Tree) a0Tl
    (fun i => getLs a0LGens (i + 1)) a0Ns a0_base_lt a0_tree a0_sch _ a0_gens
    (by rw [card_heP_cent0, a0_prod])

end CertificateChecks.KernelHe7222

end
