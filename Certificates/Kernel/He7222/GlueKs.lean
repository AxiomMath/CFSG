module

public import Certificates.Kernel.He7222.GlueK
public import Certificates.Kernel.He7222.KeysK
public import Certificates.Kernel.He7222.FibK
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.OrbRow.LevelSound
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.Loops

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHe7222

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.OrbRow CFSG.KC.HeChain CFSG.KS.Raw.Orb
  CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.KD.He7222 CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.He
  CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier CFSG.Monster.B.Co2.Native
  CertificateChecks.KernelLC.HeFix CertificateChecks.KernelHe7223
  CertificateChecks.KernelSchreierFam.He725 CFSG.KS.PF

theorem incK_pair : ∀ (L : List ℕ) (b : ℕ), incK L b = true →
    L.Pairwise (· < ·) ∧ ∀ x ∈ L, b < x
  | [], _, _ => ⟨List.Pairwise.nil, fun x hx => absurd hx List.not_mem_nil⟩
  | x :: L, b, h => by
    have h' : Bool.rec (motive := fun _ => Bool) false (incK L x) (Nat.blt b x) = true := h
    cases hb : Nat.blt b x with
    | false =>
      rw [hb] at h'
      exact absurd h' (by simp)
    | true =>
      rw [hb] at h'
      change incK L x = true at h'
      obtain ⟨hp, hall⟩ := incK_pair L x h'
      have hbx : b < x := Nat.blt_eq.mp hb
      refine ⟨List.Pairwise.cons hall hp, fun y hy => ?_⟩
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hbx
      · exact lt_trans hbx (hall y hy)

theorem incAll_spec : ∀ (LL : List (List ℕ)) (i : ℕ), incAll LL = true →
    incK (LL.getD i []) 0 = true
  | [], i, _ => by
    rw [List.getD_eq_default _ _ (by simp)]
    rfl
  | L :: LL, i, h => by
    have h' : Bool.rec (motive := fun _ => Bool) false (incAll LL) (incK L 0) = true := h
    cases hb : incK L 0 with
    | false =>
      rw [hb] at h'
      exact absurd h' (by simp)
    | true =>
      rw [hb] at h'
      change incAll LL = true at h'
      rcases i with _ | i
      · exact hb
      · rw [List.getD_cons_succ]
        exact incAll_spec LL i h'

theorem prod_lprodK : ∀ T : List (List ℕ),
    ∏ i ∈ Finset.range T.length, (T.getD i []).length = lprodK T
  | [] => rfl
  | t :: T => by
    rw [List.length_cons, Finset.prod_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [prod_lprodK T]
    change _ = Nat.mul (lenS t) (lprodK T)
    rw [lenS_eq, Nat.mul_comm]
    rfl

theorem kbK_spec {B : List ℕ} (h : kbK B = true) : ∀ i < B.length, B.getD i 0 < 8330 := by
  intro i hi
  have := allN_spec h i (by rw [lenS_eq]; exact hi)
  rw [← getS_eq]
  exact Nat.blt_eq.mp this

theorem a0_kch
    (j : ℕ) (hj : j < 2) :
    (∀ i < (getLs a0QBase j).length, ∀ k < ((getLL a0KTs j).getD i []).length,
      recP 8330 14 (((getLL a0KTs j).getD i []).getD k 0) ∈
        centralizerIn heP (heGenPerm 0) ⊓ Subgroup.centralizer {rep0P (getS a0SRep j)} ∧
      PRep 8330 14 (((getLL a0KTs j).getD i []).getD k 0)
        (recP 8330 14 (((getLL a0KTs j).getD i []).getD k 0))) ∧
    (∀ g ∈ centralizerIn heP (heGenPerm 0) ⊓ Subgroup.centralizer {rep0P (getS a0SRep j)},
      ∃ f : ℕ → ℕ, (∀ i < (getLs a0QBase j).length, f i < ((getLL a0KTs j).getD i []).length) ∧
      g = ((List.range (getLs a0QBase j).length).map
        fun i => recP 8330 14 (((getLL a0KTs j).getD i []).getD (f i) 0)).prod) ∧
    ∀ z ∈ centralizerIn heP (heGenPerm 0), ∃ pos < (getLL a0KC (getS a0SRep j)).length,
      (tupP a0Ts ((getLL a0KC (getS a0SRep j)).getD pos []))⁻¹ * z ∈
        centralizerIn heP (heGenPerm 0) ⊓ Subgroup.centralizer {rep0P (getS a0SRep j)} := by
  have hrt := ch7222rt
  simp only [Bool.and_eq_true] at hrt
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨r0, r1⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hrt
  have hkeys := ch7222keys
  simp only [Bool.and_eq_true] at hkeys
  have hkb := ch7222kb
  simp only [Bool.and_eq_true] at hkb
  obtain ⟨⟨⟨⟨⟨⟨kb0, kb1⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hkb
  have hkn := ch7222kn
  simp only [Bool.and_eq_true] at hkn
  obtain ⟨⟨⟨⟨⟨⟨kn0, kn1⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hkn
  have hsr := ch7222srep
  simp only [Bool.and_eq_true] at hsr
  obtain ⟨⟨⟨⟨⟨⟨⟨s0, s1⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hsr
  have key : ∀ (r : ℕ) (G : List ℕ) (T S Nn : List (List ℕ)), getS a0SRep j = r →
      tupOK a0Ts (getLs a0RT r) = true → ca r = true →
      kg0 j G = true → kc0 j G T S Nn = true → T = getLL a0KTs j →
      kbK (getLs a0QBase j) = true →
      Nat.beq (Nat.mul (lenS (getLs a0CKeys r)) (lprodK T)) 161280 = true →
    (∀ i < (getLs a0QBase j).length, ∀ k < ((getLL a0KTs j).getD i []).length,
      recP 8330 14 (((getLL a0KTs j).getD i []).getD k 0) ∈
        centralizerIn heP (heGenPerm 0) ⊓ Subgroup.centralizer {rep0P (getS a0SRep j)} ∧
      PRep 8330 14 (((getLL a0KTs j).getD i []).getD k 0)
        (recP 8330 14 (((getLL a0KTs j).getD i []).getD k 0))) ∧
    (∀ g ∈ centralizerIn heP (heGenPerm 0) ⊓ Subgroup.centralizer {rep0P (getS a0SRep j)},
      ∃ f : ℕ → ℕ, (∀ i < (getLs a0QBase j).length, f i < ((getLL a0KTs j).getD i []).length) ∧
      g = ((List.range (getLs a0QBase j).length).map
        fun i => recP 8330 14 (((getLL a0KTs j).getD i []).getD (f i) 0)).prod) ∧
    ∀ z ∈ centralizerIn heP (heGenPerm 0), ∃ pos < (getLL a0KC (getS a0SRep j)).length,
      (tupP a0Ts ((getLL a0KC (getS a0SRep j)).getD pos []))⁻¹ * z ∈
        centralizerIn heP (heGenPerm 0) ⊓ Subgroup.centralizer {rep0P (getS a0SRep j)} := by
    intro r G T S Nn hr ht hca hkg hkc hT hb hn
    subst hT
    rw [hr]
    have hch : chainK 8330 14 (mask 14) (pidn 8330 14) G (getLs a0QBase j) (getLL a0QTree j)
        (getLL a0KTs j) S (getLL a0QLGens j) Nn = true := hkc
    have hTB := (chainK_sound hch).1
    have hpr := prod_lprodK (getLL a0KTs j)
    rw [hTB] at hpr
    have hinc := (incK_pair _ 0 (incAll_spec a0CKeys r hkeys.1.1.1)).1
    rw [← getLs_eq] at hinc
    have hkg' : kgK 8330 14 (mask 14) (pidn 8330 14) a0Ts (rep0 r) G (getLL a0KU j) = true := by
      rw [← hr]
      exact hkg
    refine k_chain (Ts := a0Ts) (TIs := a0TIs) rfl
      (fun t ht j hj => ⟨(a0_cent_chain.1 t ht j hj).1, (a0_cent_chain.1 t ht j hj).2.1⟩)
      (fun t ht j hj => tree_shr (by norm_num) (by norm_num) (a0_tree t ht) j hj) a0_inv
      (rs := stkK a0Ts (getLs a0RT r)) (s := rep0P r)
      (fun p => evK_rep (stkK_rep (n := 8330) (w := 14) rec0 ht a0_hrep) p) (prep_rep0 ht).1
      (prep_rep0 ht).2 hca hinc hkg' hch (kbK_spec hb) ?_
    rw [hpr, card_heP_cent0, ← lenS_eq]
    exact Nat.eq_of_beq_eq_true hn
  match j, hj with
  | 0, _ =>
    exact key 0 a0K0G _ _ _ (Nat.eq_of_beq_eq_true s0) r0 ch7222ca0 ch7222kga0 ch7222kca0 rfl kb0
      kn0
  | 1, _ =>
    exact key 1 a0K1G _ _ _ (Nat.eq_of_beq_eq_true s1) r1 ch7222ca1 ch7222kga1 ch7222kca1 rfl kb1
      kn1

theorem t1_kch
    (j : ℕ) (hj : j < 5) :
    (∀ i < (getLs t1QBase j).length, ∀ k < ((getLL t1KTs j).getD i []).length,
      recP 8330 14 (((getLL t1KTs j).getD i []).getD k 0) ∈
        centralizerIn heP heT1P ⊓ Subgroup.centralizer {rep1P (getS t1SRep j)} ∧
      PRep 8330 14 (((getLL t1KTs j).getD i []).getD k 0)
        (recP 8330 14 (((getLL t1KTs j).getD i []).getD k 0))) ∧
    (∀ g ∈ centralizerIn heP heT1P ⊓ Subgroup.centralizer {rep1P (getS t1SRep j)},
      ∃ f : ℕ → ℕ, (∀ i < (getLs t1QBase j).length, f i < ((getLL t1KTs j).getD i []).length) ∧
      g = ((List.range (getLs t1QBase j).length).map
        fun i => recP 8330 14 (((getLL t1KTs j).getD i []).getD (f i) 0)).prod) ∧
    ∀ z ∈ centralizerIn heP heT1P, ∃ pos < (getLL t1KC (getS t1SRep j)).length,
      (tupP t1Ts ((getLL t1KC (getS t1SRep j)).getD pos []))⁻¹ * z ∈
        centralizerIn heP heT1P ⊓ Subgroup.centralizer {rep1P (getS t1SRep j)} := by
  have hrt := ch7222rt
  simp only [Bool.and_eq_true] at hrt
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, q1⟩, q2⟩, q3⟩, -⟩, q5⟩, q6⟩ := hrt
  have hkeys := ch7222keys
  simp only [Bool.and_eq_true] at hkeys
  have hkb := ch7222kb
  simp only [Bool.and_eq_true] at hkb
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, kb0⟩, kb1⟩, kb2⟩, kb3⟩, kb4⟩ := hkb
  have hkn := ch7222kn
  simp only [Bool.and_eq_true] at hkn
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, kn0⟩, kn1⟩, kn2⟩, kn3⟩, kn4⟩ := hkn
  have hsr := ch7222srep
  simp only [Bool.and_eq_true] at hsr
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, s0⟩, s1⟩, s2⟩, s3⟩, s4⟩ := hsr
  have key : ∀ (r : ℕ) (G : List ℕ) (T S Nn : List (List ℕ)), getS t1SRep j = r →
      tupOK t1Ts (getLs t1RT r) = true → ct r = true →
      kg1 j G = true → kc1 j G T S Nn = true → T = getLL t1KTs j →
      kbK (getLs t1QBase j) = true →
      Nat.beq (Nat.mul (lenS (getLs t1CKeys r)) (lprodK T)) 21504 = true →
    (∀ i < (getLs t1QBase j).length, ∀ k < ((getLL t1KTs j).getD i []).length,
      recP 8330 14 (((getLL t1KTs j).getD i []).getD k 0) ∈
        centralizerIn heP heT1P ⊓ Subgroup.centralizer {rep1P (getS t1SRep j)} ∧
      PRep 8330 14 (((getLL t1KTs j).getD i []).getD k 0)
        (recP 8330 14 (((getLL t1KTs j).getD i []).getD k 0))) ∧
    (∀ g ∈ centralizerIn heP heT1P ⊓ Subgroup.centralizer {rep1P (getS t1SRep j)},
      ∃ f : ℕ → ℕ, (∀ i < (getLs t1QBase j).length, f i < ((getLL t1KTs j).getD i []).length) ∧
      g = ((List.range (getLs t1QBase j).length).map
        fun i => recP 8330 14 (((getLL t1KTs j).getD i []).getD (f i) 0)).prod) ∧
    ∀ z ∈ centralizerIn heP heT1P, ∃ pos < (getLL t1KC (getS t1SRep j)).length,
      (tupP t1Ts ((getLL t1KC (getS t1SRep j)).getD pos []))⁻¹ * z ∈
        centralizerIn heP heT1P ⊓ Subgroup.centralizer {rep1P (getS t1SRep j)} := by
    intro r G T S Nn hr ht hct hkg hkc hT hb hn
    subst hT
    rw [hr]
    have hch : chainK 8330 14 (mask 14) (pidn 8330 14) G (getLs t1QBase j) (getLL t1QTree j)
        (getLL t1KTs j) S (getLL t1QLGens j) Nn = true := hkc
    have hTB := (chainK_sound hch).1
    have hpr := prod_lprodK (getLL t1KTs j)
    rw [hTB] at hpr
    have hinc := (incK_pair _ 0 (incAll_spec t1CKeys r hkeys.1.1.2)).1
    rw [← getLs_eq] at hinc
    have hkg' : kgK 8330 14 (mask 14) (pidn 8330 14) t1Ts (rep1 r) G (getLL t1KU j) = true := by
      rw [← hr]
      exact hkg
    refine k_chain (Ts := t1Ts) (TIs := t1TIs) rfl
      (fun t ht j hj => ⟨(t1_cent_chain.1 t ht j hj).1, (t1_cent_chain.1 t ht j hj).2.1⟩)
      (fun t ht j hj => tree_shr (by norm_num) (by norm_num) (t1_tree t ht) j hj) t1_inv
      (rs := stkK t1Ts (getLs t1RT r)) (s := rep1P r)
      (fun p => evK_rep (stkK_rep (n := 8330) (w := 14) rec1 ht t1_hrep) p) (prep_rep1 ht).1
      (prep_rep1 ht).2 hct hinc hkg' hch (kbK_spec hb) ?_
    rw [hpr, card_heP_cent1, ← lenS_eq]
    exact Nat.eq_of_beq_eq_true hn
  match j, hj with
  | 0, _ =>
    exact key 1 t1K0G _ _ _ (Nat.eq_of_beq_eq_true s0) q1 ch7222ct1 ch7222kgt0 ch7222kct0 rfl kb0
      kn0
  | 1, _ =>
    exact key 2 t1K1G _ _ _ (Nat.eq_of_beq_eq_true s1) q2 ch7222ct2 ch7222kgt1 ch7222kct1 rfl kb1
      kn1
  | 2, _ =>
    exact key 3 t1K2G _ _ _ (Nat.eq_of_beq_eq_true s2) q3 ch7222ct3 ch7222kgt2 ch7222kct2 rfl kb2
      kn2
  | 3, _ =>
    exact key 5 t1K3G _ _ _ (Nat.eq_of_beq_eq_true s3) q5 ch7222ct5 ch7222kgt3 ch7222kct3 rfl kb3
      kn3
  | 4, _ =>
    exact key 6 t1K4G _ _ _ (Nat.eq_of_beq_eq_true s4) q6 ch7222ct6 ch7222kgt4 ch7222kct4 rfl kb4
      kn4

end CertificateChecks.KernelHe7222

end
