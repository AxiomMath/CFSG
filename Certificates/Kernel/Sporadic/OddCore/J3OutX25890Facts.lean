module

public import Certificates.Kernel.Sporadic.OddCore.J3OutX25890
public import Certificates.Kernel.Sporadic.OddCore.J3OutSylF
public import Certificates.Kernel.Fin76bAut.Core
public import CFSG.Certificates.Kernel.TC2Outer0Sound
public import CFSG.Certificates.Kernel.Spor.RecMulSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2Table
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWIso2

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.J3OutX25890

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.RecMul
open CFSG.KS.MulH CFSG.KS.EAut CFSG.EvenSporadicStandard.Fin76b CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CertificateChecks.KernelSpor.OddCore
open CertificateChecks.KernelSpor.J3OutSyl
open CFSG.Sporadic.Schreier (j3P)
open CFSG.Monster.B.Co2.Native (siftA)
open CFSG.KS.Raw.Orb (PRep prep_of_rep)

@[expose] noncomputable def gX (j : ℕ) : Equiv.Perm (Fin 6156) := tp 6156 (j3CentTbl (j + 1))

theorem permOK_cent {k : ℕ} (hk : k < 31) :
    CFSG.Sporadic.SmallOddCore.permOK 6156 (j3CentTbl k) = true :=
  List.all_eq_true.1 j3_permOK_all k (List.mem_range.2 hk)

theorem prep_cent {k : ℕ} (hk : k < 31) : PRep 6156 13 (J3CentP k) (tp 6156 (j3CentTbl k)) := by
  apply prep_of_rep
  rw [← j3CentTbl_eq hk]
  exact co2Rep_natArr_iff.2 (rep_tp (permOK_cent hk))

theorem exists_rec : ∃ x : ℕ → Equiv.Perm (Fin 6156), x 0 = 1 ∧
    (∀ i < 256, PRep 6156 13 (J3XS.T i) (x i)) ∧
    (∀ i, 0 < i → i < 256 → parOf J3XS.PL i < i ∧ labOf J3XS.PL i < 8 ∧
      x i = x (parOf J3XS.PL i) * gX (labOf J3XS.PL i)) ∧
    (∀ i < 256, ∀ j < 8, r32 J3XS.POS (i * 8 + j) < 256 ∧
      x (r32 J3XS.POS (i * 8 + j)) = x i * gX j) ∧
    (∀ a < 256, ∀ b < 256, x a = x b → a = b) := by
  have h := penumRight_rec (cap := 256) (g := gX) (by norm_num) (by norm_num)
    (fun j hj => (gen hj).2.2) (fun j hj => by rw [(gen hj).2.1]; exact prep_cent (by omega))
    base.2.2.2.2.2.2 s_pe
  rwa [hcnt] at h

@[expose] noncomputable def xS : ℕ → Equiv.Perm (Fin 6156) := exists_rec.choose

theorem xS_zero : xS 0 = 1 := exists_rec.choose_spec.1

theorem prep_xS {i : ℕ} (hi : i < 256) : PRep 6156 13 (J3XS.T i) (xS i) :=
  exists_rec.choose_spec.2.1 i hi

theorem xS_tree : ∀ i, 0 < i → i < 256 → parOf J3XS.PL i < i ∧ labOf J3XS.PL i < 8 ∧
    xS i = xS (parOf J3XS.PL i) * gX (labOf J3XS.PL i) :=
  exists_rec.choose_spec.2.2.1

theorem xS_pos : ∀ i < 256, ∀ j < 8, r32 J3XS.POS (i * 8 + j) < 256 ∧
    xS (r32 J3XS.POS (i * 8 + j)) = xS i * gX j :=
  exists_rec.choose_spec.2.2.2.1

theorem xS_inj : ∀ a < 256, ∀ b < 256, xS a = xS b → a = b :=
  exists_rec.choose_spec.2.2.2.2

theorem gX_mem {j : ℕ} (hj : j < 8) : gX j ∈ j3S := by
  have hm : j3CentTbl (j + 1) ∈ j3SylowGenTbls := by
    unfold j3SylowGenTbls
    exact List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩
  exact subset_closure ⟨j3CentTbl (j + 1), List.mem_toArray.2 hm, rfl⟩

theorem xS_mem {i : ℕ} (hi : i < 256) : xS i ∈ j3S := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [xS_zero]
      exact one_mem _
    · obtain ⟨h1, h2, h3⟩ := xS_tree i hpos hi
      rw [h3]
      exact mul_mem (ih _ h1 (by omega)) (gX_mem h2)

theorem reach {b : ℕ} (hb : b < 256) : reachRf J3XS.PL 5 b = true := by
  have h := kBase25890
  rw [Bool.and_eq_true] at h
  exact List.all_eq_true.1 h.1 b (List.mem_range.2 hb)

theorem mulJ3K_spec {a b : ℕ} (ha : a < 256) (hb : b < 256) :
    mulJ3K a b < 256 ∧ xS (mulJ3K a b) = xS a * xS b :=
  mulRf_spec xS_zero xS_tree xS_pos 5 a b ha hb (reach hb)

theorem xS_one : xS 1 = tp 6156 (j3CentTbl 9) := by
  have h := kBase25890
  rw [Bool.and_eq_true] at h
  refine prep_unique (prep_xS (by norm_num)) ?_
  rw [Nat.eq_of_beq_eq_true h.2]
  exact prep_cent (by norm_num)

theorem cK0 : canonK 6156 13 (mask 13) (6156 * 13) (J3CentP 0) = true := by
  have h := j3_perm (k := 0) (by norm_num)
  unfold j3Perm invEqK at h
  obtain ⟨h1, -, h3⟩ := CFSG.KS.Raw.Orb.permOK_facts h
  unfold canonK
  simp only [bAnd_iff]
  exact ⟨base.1, Nat.beq_eq.mpr h1,
    CFSG.KS.Raw.Orb.allN_iff.2 fun i hi => Nat.blt_eq.mpr (h3 i hi).1⟩

theorem sift_wd {j : ℕ} (hj : j < 8) :
    siftA 6156 CFSG.Sporadic.Schreier.PairJ3.levels CFSG.Sporadic.Schreier.PairJ3.baseArr 0
      (unpack 6156 13 (wdVal j)) = true :=
  CertificateChecks.KernelSporSch.J3KT.sift_of
    (List.all_eq_true.1 kWord25890 j (List.mem_range.2 hj))

theorem gX_inner {j : ℕ}
    (hj : j < 8) : (oddJ3 j = false → gX j ∈ j3P) ∧ (oddJ3 j = true → gX j * j3u ∈ j3P) := by
  have hD := j3_groupData
  have hs := sift_wd hj
  have c1 : canonK 6156 13 (mask 13) (6156 * 13) (J3CentP (j + 1)) = true := by
    rw [← (gen hj).2.1]
    exact (gen hj).1
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have e : wdVal j = J3CentP (j + 1) := by simp [wdVal, h]
    rw [e, ← j3CentTbl_eq (by omega)] at hs
    exact (hD.sift _ _ (rep_tp (permOK_cent (by omega)))).1 hs
  · have e : wdVal j = pcomp 6156 13 (mask 13) (J3CentP (j + 1)) (J3CentP 0) := by
      simp [wdVal, h]
    have ht : natArr (compT 6156 (j3CentTbl (j + 1)) (j3CentTbl 0)) =
        unpack 6156 13 (wdVal j) := by
      rw [tbl_unpack (k := j + 1) (by omega), tbl_unpack (k := 0) (by norm_num), compT_unpack c1 cK0,
        natArr_tabT (CFSG.KC.BfsPin.canonK_pcomp c1 cK0), e]
    rw [← ht] at hs
    exact (hD.sift _ _ (Rep.compT (rep_tp (permOK_cent (by omega)))
      (rep_tp (permOK_cent (by norm_num))))).1 hs

theorem xS_mem_P
    {a : ℕ} (ha : a < 256) (h : innJ3K a = true) : xS a ∈ j3P := by
  obtain ⟨hU2, -, -, hmap, -⟩ := ctuc_j3_normalizing_involution_permutation_model
  have hu : ∀ p ∈ j3P, j3u * p * j3u⁻¹ ∈ j3P := fun p hp => by
    rw [← hmap]
    exact ⟨p, hp, rfl⟩
  have hu2 : j3u * j3u = 1 := by rw [← pow_two, hU2]
  have hodd : oddRf J3XS.PL oddJ3 5 a = false := by simpa [innJ3K] using h
  exact (oddRf_spec (P := j3P) hu2 hu xS_zero xS_tree (fun j hj => gX_inner hj) 5 a ha
    (reach ha)).1 hodd

theorem eListX_eq25890 : TableX.eListX 256 innJ3K mulJ3K 1 = EL25890 :=
  of_decide_eq_true kEL25890

theorem getD_mem25890 {j : ℕ} (hj : j < 32) : SIG25890.getD j 0 ∈ SIG25890 := by
  rw [List.getD_eq_getElem _ _ (by simpa [SIG25890] using hj)]
  exact List.getElem_mem _

theorem card_aut25890 {G : Type*} [Group G] {elt : ℕ → G}
    (hinj : ∀ a b, a < 256 → b < 256 → elt a = elt b → a = b)
    (hmul : ∀ a b, a < 256 → b < 256 → mulJ3K a b < 256 ∧ elt a * elt b = elt (mulJ3K a b))
    (h0 : elt 0 = 1) (E : Subgroup G)
    (hE : ∀ x, x ∈ E ↔ ∃ a ∈ TableX.eListX 256 innJ3K mulJ3K 1, elt a = x)
    (hlt : ∀ a ∈ TableX.eListX 256 innJ3K mulJ3K 1, a < 256) : Nat.card (MulAut ↥E) = 1920 := by
  have hk := kLab25890
  simp only [lab25890, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    decide_eq_true_eq, List.contains_iff_mem] at hk
  obtain ⟨⟨⟨⟨⟨⟨htab, hsub⟩, hsup⟩, -⟩, hnd⟩, hs0⟩, hs21⟩ := hk
  rw [eListX_eq25890] at hE hlt
  have hSlt : ∀ j < 32, SIG25890.getD j 0 < 256 := fun j hj => hlt _ (hsub _ (getD_mem25890 hj))
  have hL : ELabelling E (elt 1) W16.mulE0 21 (fun j => elt (SIG25890.getD j 0)) :=
    { mem := fun k hk => (hE _).2 ⟨_, hsub _ (getD_mem25890 hk), rfl⟩
      surj := by
        intro e he
        obtain ⟨a, ha, rfl⟩ := (hE e).1 he
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (hsup a ha)
        refine ⟨j, by simpa [SIG25890] using hj, ?_⟩
        rw [List.getD_eq_getElem _ _ hj]
      inj := by
        intro a ha b hb h
        have e := hinj _ _ (hSlt a ha) (hSlt b hb) h
        have ha' : a < SIG25890.length := by simpa [SIG25890] using ha
        have hb' : b < SIG25890.length := by simpa [SIG25890] using hb
        rw [List.getD_eq_getElem _ _ ha', List.getD_eq_getElem _ _ hb'] at e
        exact (hnd.getElem_inj_iff).1 e
      lt := W16.mulE0_lt
      mul := by
        intro a ha b hb
        rw [CertificateChecks.KernelFin76bAut.ch24614ET a ha b hb, htab a ha b hb]
        exact ((hmul _ _ (hSlt a ha) (hSlt b hb)).2).symm
      one := by rw [hs0, h0]
      tI_lt := by norm_num
      at_tI := by rw [hs21] }
  exact (CertificateChecks.KernelFin76bAut.rec_all_of_labelling hL).2.2

theorem outerFacts25890
    {Y : Type} [Group Y] [Finite (MulAut Y)]
    (φ : Equiv.Perm (Fin 6156) → MulAut Y) (t : Y) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (hmul : ∀ x ∈ j3S, ∀ y ∈ j3S, φ (x * y) = φ x * φ y)
    (hinj : ∀ x ∈ j3S, ∀ y ∈ j3S, φ x = φ y → x = y)
    (ht0 : φ (tp 6156 (j3CentTbl 9)) = MulAut.conj t)
    (hInn : ∀ x ∈ j3S, x ∈ j3P → ∃ y : Y, φ x = MulAut.conj y)
    (hInv : ∀ x ∈ j3S, x ∈ j3P → x * x = 1 → x ≠ 1 → ∃ c : Y, φ x = MulAut.conj (c * t * c⁻¹)) :
    ∃ K E : Subgroup (MulAut Y), OuterEFacts Y K t E := by
  have hinjE : ∀ a b, a < 256 → b < 256 → φ (xS a) = φ (xS b) → a = b := fun a b ha hb h =>
    xS_inj a ha b hb (hinj _ (xS_mem ha) _ (xS_mem hb) h)
  have hmulE : ∀ a b, a < 256 → b < 256 →
      mulJ3K a b < 256 ∧ φ (xS a) * φ (xS b) = φ (xS (mulJ3K a b)) := by
    intro a b ha hb
    obtain ⟨h1, h2⟩ := mulJ3K_spec ha hb
    refine ⟨h1, ?_⟩
    rw [h2, hmul _ (xS_mem ha) _ (xS_mem hb)]
  have h0 : φ (xS 0) = 1 := by
    have h := hmul 1 (one_mem _) 1 (one_mem _)
    rw [one_mul] at h
    rw [xS_zero]
    exact mul_left_cancel (h.symm.trans (mul_one _).symm)
  have hsq : ∀ a, a < 256 → mulJ3K a a = 0 → xS a * xS a = 1 := fun a ha h => by
    rw [← (mulJ3K_spec ha ha).2, h, xS_zero]
  have hne : ∀ a, a < 256 → a ≠ 0 → xS a ≠ 1 := fun a ha h0 h =>
    h0 (xS_inj a ha 0 (by norm_num) (h.trans xS_zero.symm))
  obtain ⟨K, E, hf, -⟩ := exists_outerEFacts_of_card (elt := fun a => φ (xS a)) ht2 ht1 hinjE
    hmulE h0 ⟨by norm_num, by rw [xS_one]; exact ht0⟩
    (fun a ha h => hInn _ (xS_mem ha) (xS_mem_P ha h))
    (fun a ha h _ hm h0 => hInv _ (xS_mem ha) (xS_mem_P ha h) (hsq a ha hm) (hne a ha h0))
    (CFSG.KC.TC2Outer.checkSpec0_of_check0 kOuter25890) (card_aut25890 hinjE hmulE h0)
  exact ⟨K, E, hf⟩

end CertificateChecks.KernelSpor.J3OutX25890

end
