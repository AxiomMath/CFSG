module

public import Certificates.Kernel.He7222.GlueChain
public import Certificates.Kernel.He7222.BndK
public import Certificates.Kernel.He7222.ClsK
public import Certificates.Kernel.He7222.InvK
public import CFSG.Certificates.Kernel.He7222.CoverGrp
public import CFSG.Certificates.Kernel.He7222.ClassGrp
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.OrbRow.LevelSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHe7222

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.OrbRow CFSG.KC.HeChain CFSG.KS.Raw.Orb
  CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.KD.He7222 CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.He
  CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier CFSG.Monster.B.Co2.Native
  CertificateChecks.KernelLC.HeFix CertificateChecks.KernelHe7223

@[expose] noncomputable def rec0 (t j : ℕ) : Equiv.Perm (Fin 8330) :=
  recP 8330 14 ((a0Ts.getD t []).getD j 0)

@[expose] noncomputable def rep0P (cl : ℕ) : Equiv.Perm (Fin 8330) :=
  (tupL rec0 8 (getLs a0RT cl)).prod

theorem a0_len0 : (a0Tl 0).length = 105 := by
  rw [← lenS_eq]
  exact Nat.eq_of_beq_eq_true (show Nat.beq (lenS a0T0) 105 = true by quickRfl)

theorem a0_inv : ∀ t < 8,
    invLK 8330 14 (mask 14) (pidn 8330 14) (a0Ts.getD t []) (a0TIs.getD t []) = true
  | 0, _ => ch7222ia0
  | 1, _ => ch7222ia1
  | 2, _ => ch7222ia2
  | 3, _ => ch7222ia3
  | 4, _ => ch7222ia4
  | 5, _ => ch7222ia5
  | 6, _ => ch7222ia6
  | 7, _ => ch7222ia7
  | _ + 8, h => absurd h (by omega)

theorem a0_inv_class :
    ∀ x ∈ centralizerIn heP (heGenPerm 0), x * x = 1 → x ≠ 1 → x ≠ heGenPerm 0 →
      ∃ cl < 5, ∃ c ∈ centralizerIn heP (heGenPerm 0), x = c * rep0P cl * c⁻¹ := by
  intro x hx hx2 hx1 hxt
  obtain ⟨hch, hfac⟩ := a0_cent_chain
  have hb0 := a0_base_lt 0 (by norm_num)
  have hbF : baseF (by norm_num : 0 < 8330) (getS a0Base) 0 = ⟨getS a0Base 0, hb0⟩ := by
    unfold baseF
    rw [dif_pos hb0]
  have hcc := ch7222cc
  simp only [Bool.and_eq_true] at hcc
  have hPH : centralizerIn heP (heGenPerm 0) ≤ heP := inf_le_left
  have hτP : heGenPerm 0 ∈ centralizerIn heP (heGenPerm 0) :=
    mem_centralizerIn.2 ⟨heGenPerm_mem (by norm_num), rfl⟩
  obtain ⟨F, hF, cl, hcl, pos, hk⟩ := cover_key (n := 8330) (w := 14) (by norm_num)
    (by norm_num) (by norm_num) (H := heP) baseFaithful_heP hPH hτP prep_a0 (L := 8)
    (by norm_num) (Tl := a0Tl) hb0 (fun i hi j hj => (hch i hi j hj).2.1)
    (fun i hi h0 j hj => by
      have := (hch i hi j hj).2.2 0 h0
      rwa [hbF] at this)
    hfac (ncl := 5) (CK := a0CKeys) (Cc := a0Cc) (Cov := a0Cov)
    (fun i hi => Nat.blt_eq.mp (allN_spec hcc.1 i (by rwa [a0_len0] at hi)))
    (fun i hi => ch7222cov0 i (by rwa [a0_len0] at hi)) x hx hx2 hx1 hxt
  have hrep : ∀ t < a0Ts.length, ∀ j < (a0Ts.getD t []).length,
      recP 8330 14 ((a0Ts.getD t []).getD j 0) ∈ centralizerIn heP (heGenPerm 0) ∧
      PRep 8330 14 ((a0Ts.getD t []).getD j 0) (recP 8330 14 ((a0Ts.getD t []).getD j 0)) :=
    fun t ht j hj => ⟨(hch t ht j hj).1, (hch t ht j hj).2.1⟩
  have finish : ∀ c, tupOK a0Ts (getLs a0RT c) = true → ca c = true →
      keyF 14 F 5 = getS (getLs a0CKeys c) pos →
      ∃ g ∈ centralizerIn heP (heGenPerm 0), x = g * rep0P c * g⁻¹ := by
    intro c ht hca hkc
    have hst := stkK_rep (n := 8330) (w := 14) rec0 ht (fun t ht j hj => (hrep t ht j hj).2)
    obtain ⟨-, hixb⟩ := tupOK_spec ht
    have hrr : rep0P c ∈ centralizerIn heP (heGenPerm 0) := by
      refine Subgroup.list_prod_mem (K := centralizerIn heP (heGenPerm 0)) fun g hg => ?_
      simp only [tupL, List.mem_map, List.mem_range] at hg
      obtain ⟨t, ht', rfl⟩ := hg
      exact (hrep t ht' _ (hixb t ht')).1
    exact class_conj (n := 8330) (w := 14) (by norm_num) (by norm_num) (by norm_num)
      baseFaithful_heP hPH (Ts := a0Ts) (TIs := a0TIs) rfl hrep
      (fun t ht j hj => tree_shr (by norm_num) (by norm_num) (a0_tree t ht) j hj)
      a0_inv (rs := stkK a0Ts (getLs a0RT c)) (rr := rep0P c) (fun p => evK_rep hst p) hrr hca hx
      hF hkc
  have hrt := ch7222rt
  simp only [Bool.and_eq_true] at hrt
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨r0, r1⟩, r2⟩, r3⟩, r4⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hrt
  refine ⟨cl, hcl, ?_⟩
  match cl, hcl with
  | 0, _ => exact finish 0 r0 ch7222ca0 hk
  | 1, _ => exact finish 1 r1 ch7222ca1 hk
  | 2, _ => exact finish 2 r2 ch7222ca2 hk
  | 3, _ => exact finish 3 r3 ch7222ca3 hk
  | 4, _ => exact finish 4 r4 ch7222ca4 hk

theorem prep_t1 :
    PRep 8330 14 PT1 heT1P := by
  have h := rep_heT1
  rw [heT1_eq] at h
  exact prep_of_rep h

@[expose] noncomputable def rec1 (t j : ℕ) : Equiv.Perm (Fin 8330) :=
  recP 8330 14 ((t1Ts.getD t []).getD j 0)

@[expose] noncomputable def rep1P (cl : ℕ) : Equiv.Perm (Fin 8330) :=
  (tupL rec1 7 (getLs t1RT cl)).prod

theorem t1_len0 : (t1Tl 0).length = 42 := by
  rw [← lenS_eq]
  exact Nat.eq_of_beq_eq_true (show Nat.beq (lenS t1T0) 42 = true by quickRfl)

theorem t1_inv : ∀ t < 7,
    invLK 8330 14 (mask 14) (pidn 8330 14) (t1Ts.getD t []) (t1TIs.getD t []) = true
  | 0, _ => ch7222it0
  | 1, _ => ch7222it1
  | 2, _ => ch7222it2
  | 3, _ => ch7222it3
  | 4, _ => ch7222it4
  | 5, _ => ch7222it5
  | 6, _ => ch7222it6
  | _ + 7, h => absurd h (by omega)

theorem t1_inv_class :
    ∀ x ∈ centralizerIn heP heT1P, x * x = 1 → x ≠ 1 → x ≠ heT1P →
      ∃ cl < 7, ∃ c ∈ centralizerIn heP heT1P, x = c * rep1P cl * c⁻¹ := by
  intro x hx hx2 hx1 hxt
  obtain ⟨hch, hfac⟩ := t1_cent_chain
  have hb0 := t1_base_lt 0 (by norm_num)
  have hbF : baseF (by norm_num : 0 < 8330) (getS t1Base) 0 = ⟨getS t1Base 0, hb0⟩ := by
    unfold baseF
    rw [dif_pos hb0]
  have hcc := ch7222cc
  simp only [Bool.and_eq_true] at hcc
  have hPH : centralizerIn heP heT1P ≤ heP := inf_le_left
  have hτP : heT1P ∈ centralizerIn heP heT1P := mem_centralizerIn.2 ⟨heT1P_mem, rfl⟩
  obtain ⟨F, hF, cl, hcl, pos, hk⟩ := cover_key (n := 8330) (w := 14) (by norm_num)
    (by norm_num) (by norm_num) (H := heP) baseFaithful_heP hPH hτP prep_t1 (L := 7)
    (by norm_num) (Tl := t1Tl) hb0 (fun i hi j hj => (hch i hi j hj).2.1)
    (fun i hi h0 j hj => by
      have := (hch i hi j hj).2.2 0 h0
      rwa [hbF] at this)
    hfac (ncl := 7) (CK := t1CKeys) (Cc := t1Cc) (Cov := t1Cov)
    (fun i hi => Nat.blt_eq.mp (allN_spec hcc.2 i (by rwa [t1_len0] at hi)))
    (fun i hi => ch7222cov1 i (by rwa [t1_len0] at hi)) x hx hx2 hx1 hxt
  have hrep : ∀ t < t1Ts.length, ∀ j < (t1Ts.getD t []).length,
      recP 8330 14 ((t1Ts.getD t []).getD j 0) ∈ centralizerIn heP heT1P ∧
      PRep 8330 14 ((t1Ts.getD t []).getD j 0) (recP 8330 14 ((t1Ts.getD t []).getD j 0)) :=
    fun t ht j hj => ⟨(hch t ht j hj).1, (hch t ht j hj).2.1⟩
  have finish : ∀ c, tupOK t1Ts (getLs t1RT c) = true → ct c = true →
      keyF 14 F 5 = getS (getLs t1CKeys c) pos →
      ∃ g ∈ centralizerIn heP heT1P, x = g * rep1P c * g⁻¹ := by
    intro c ht hct hkc
    have hst := stkK_rep (n := 8330) (w := 14) rec1 ht (fun t ht j hj => (hrep t ht j hj).2)
    obtain ⟨-, hixb⟩ := tupOK_spec ht
    have hrr : rep1P c ∈ centralizerIn heP heT1P := by
      refine Subgroup.list_prod_mem (K := centralizerIn heP heT1P) fun g hg => ?_
      simp only [tupL, List.mem_map, List.mem_range] at hg
      obtain ⟨t, ht', rfl⟩ := hg
      exact (hrep t ht' _ (hixb t ht')).1
    exact class_conj (n := 8330) (w := 14) (by norm_num) (by norm_num) (by norm_num)
      baseFaithful_heP hPH (Ts := t1Ts) (TIs := t1TIs) rfl hrep
      (fun t ht j hj => tree_shr (by norm_num) (by norm_num) (t1_tree t ht) j hj)
      t1_inv (rs := stkK t1Ts (getLs t1RT c)) (rr := rep1P c) (fun p => evK_rep hst p) hrr hct hx
      hF hkc
  have hrt := ch7222rt
  simp only [Bool.and_eq_true] at hrt
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, r0⟩, r1⟩, r2⟩, r3⟩, r4⟩, r5⟩, r6⟩ := hrt
  refine ⟨cl, hcl, ?_⟩
  match cl, hcl with
  | 0, _ => exact finish 0 r0 ch7222ct0 hk
  | 1, _ => exact finish 1 r1 ch7222ct1 hk
  | 2, _ => exact finish 2 r2 ch7222ct2 hk
  | 3, _ => exact finish 3 r3 ch7222ct3 hk
  | 4, _ => exact finish 4 r4 ch7222ct4 hk
  | 5, _ => exact finish 5 r5 ch7222ct5 hk
  | 6, _ => exact finish 6 r6 ch7222ct6 hk

end CertificateChecks.KernelHe7222

end
