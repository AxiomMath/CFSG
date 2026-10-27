module

public import Certificates.Kernel.G2Three.Sec1T3Checks
public import Certificates.Kernel.G2Three.Sec1T3BChecks
public import Certificates.Kernel.G2Three.Sec1T3AChecks
public import Certificates.Kernel.G2Three.Sec1T3MChecks
public import Certificates.Kernel.G2Three.Sec1T3Cos
public import Certificates.Kernel.G2Three.Sec1T5Glue
public import CFSG.Certificates.Kernel.G2Three.Sec1T3Flag
public import CFSG.Certificates.Kernel.G2Three.Sec1T3F11
public import CFSG.Certificates.Kernel.G2Three.Sec1T3F12
public import CFSG.Certificates.Kernel.G2Three.Sec1T3F13
public import CFSG.Certificates.Kernel.Misc.Coset.TableFact
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.Mat3Sound
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.ModelL

public section

namespace CFSG.KD.G2Three.Sec1T3.Glue

open Subgroup CFSG.KC.Loop CFSG.KD.G2Three CFSG.KD.G2Three.Sec1 CFSG.KD.G2Three.Sec1T3
  CFSG.KC.G2Three CFSG.KC.G2Three.Sec1 CFSG.KC.G2Three.Sec1T3 CFSG.KD.G2Three.Sec1.T5Glue
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.OddStandard.HigherRank.G2Three.Sec1Proof
  CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab CFSG.CosetTable CFSG.KC.MiscCoset CFSG.KS.Mat3

set_option exponentiation.threshold 512

theorem rt0 : ∀ s < 6, rtA RT 0 s = s + 1 := by
  intro s hs
  interval_cases s <;> exact Nat.eq_of_beq_eq_true (by quickRfl)

theorem s3_one : X3 0 = ONEP := Nat.eq_of_beq_eq_true s3m_one

theorem s3_cl : ∀ i < 128, ∀ s < 6, X3 (rtA RT i s) = MULF (X3 i) (gS3 s) := by
  intro i hi s hs
  have e1 : (6 * i + s) / 6 = i := by omega
  have e2 : (6 * i + s) % 6 = s := by omega
  have key : X3 (rtA RT ((6 * i + s) / 6) ((6 * i + s) % 6)) =
      MULF (X3 ((6 * i + s) / 6)) (gS3 ((6 * i + s) % 6)) := by
    by_cases a : 6 * i + s < 192
    · exact closR_at s3m_clos0 (by norm_num) _ (by omega) (by omega)
    by_cases b : 6 * i + s < 384
    · exact closR_at s3m_clos1 (by norm_num) _ (by omega) (by omega)
    by_cases c : 6 * i + s < 576
    · exact closR_at s3m_clos2 (by norm_num) _ (by omega) (by omega)
    · exact closR_at s3m_clos3 (by norm_num) _ (by omega) (by omega)
  rwa [e1, e2] at key

theorem s3_tabAll : ∀ i < 128, atR (rowT PT i) 0 = i ∧
    ∀ j < 127, atR (rowT PT i) (j + 1) = rtA RT (atR (rowT PT i) (parA PA j)) (parA PB j) := by
  have hs : ∀ k < 8, tabK PT RT PA PB (16 * k) 16 = true := by
    intro k hk
    interval_cases k
    exacts [s3_tab0, s3_tab1, s3_tab2, s3_tab3, s3_tab4, s3_tab5, s3_tab6, s3_tab7]
  intro i hi
  exact tabK_spec (hs (i / 16) (by omega)) (by norm_num) i (by omega) (by omega)

theorem s3_colAll : ∀ i < 128, ∀ j < 128, atR (rowT PC j) i = atR (rowT PT i) j := by
  have hs : ∀ k < 4, colK PT PC (32 * k) 32 = true := by
    intro k hk
    interval_cases k
    exacts [s3_col0, s3_col1, s3_col2, s3_col3]
  intro i hi
  exact colK_spec (hs (i / 32) (by omega)) (by norm_num) i (by omega) (by omega)

variable {G : Type} [Group G] [Finite G] (m : G23Model G)

theorem encF_gen : ∀ s < 6, EncF m.ρ (gS3 s) (sGen (frameOf m) s) := by
  intro s hs
  by_cases h5 : s < 5
  · have e : gS3 s = Q5U s := by
      change nIf(Nat.blt s 5, Q5U s, SIGF) = Q5U s
      have hb : Nat.blt s 5 = true := by rw [Nat.blt_eq]; exact h5
      rw [hb]
    have e' : CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.gen5 m s = sGen (frameOf m) s :=
      if_pos h5
    rw [e, ← e']
    exact encF_of_enc m.ρ (enc_gen5 m (by omega))
  · have hs5 : s = 5 := by omega
    subst hs5
    rw [sGen_five]
    exact encF_SIGF m.ρ m.ρ_gS

theorem s3_real : ∃ elt : ℕ → G, RealT elt PT PC IV SQ ∧ ∀ s < 6, elt (s + 1) = sGen (frameOf m) s := by
  have hinvsq := s3_invSq
  rw [Bool.and_eq_true] at hinvsq
  obtain ⟨e, hR, hrt⟩ := flag_realT m.inj (encF_gen m) s3_one s3_cl
    (parR_spec s3m_par (by norm_num)) (sort_inj s3m_sort (by norm_num)) s3_tabAll s3_colAll
    (invK_spec hinvsq.1) (sqK_spec hinvsq.2)
  refine ⟨e, hR, fun s hs => ?_⟩
  have := hrt 0 (by norm_num) s hs
  rwa [rt0 s hs, hR.one, one_mul] at this

variable {m}

theorem hasB_M128 {i : ℕ} (hi : i < 128) : hasB M128 i = true := by
  have e : M128 = 2 ^ 128 - 1 := pow_sub_one_eq 128
  rw [hasB_eq, e, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true hi

theorem s3_repSs {elt : ℕ → G} (hR : RealT elt PT PC IV SQ)
    (hg : ∀ s < 6, elt (s + 1) = sGen (frameOf m) s) :
    RepM elt M128 ((frameOf m).Sσ : Set G) := by
  have h := s3a_f11
  unfold f11K at h
  simp only [bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨-, -, -, c6, p6⟩ := h
  have hM := f11_Ss hR hg c6
  set M := closK PC [1, 2, 3, 4, 5, 6] 5
  have hsub : mset elt M ⊆ elt '' (Set.Iio 128) := by
    rintro _ ⟨i, hi, -, rfl⟩
    exact ⟨i, hi, rfl⟩
  have hc1 : (mset elt M).ncard = 128 := by
    rw [pop_sound hR.inj (repM_mset hR.inj M), p6]
  have hc2 : (elt '' Set.Iio 128).ncard = 128 := by
    rw [Set.InjOn.ncard_image (s := Set.Iio 128) (fun i hi j hj h => hR.inj i hi j hj h)]
    simp [Set.ncard_eq_toFinset_card']
  have heq : mset elt M = elt '' Set.Iio 128 :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hc1, hc2]) ((Set.finite_Iio 128).image _)
  rw [← hM, heq]
  refine ⟨fun i hi => ⟨fun _ => ⟨i, hi, rfl⟩, fun _ => hasB_M128 hi⟩, ?_⟩
  rintro _ ⟨i, hi, rfl⟩
  exact ⟨i, hi, rfl⟩

@[expose] noncomputable def LOall : List ℕ :=
  ((LO0 ++ LO1) ++ (LO2 ++ LO3)) ++ ((LO4 ++ LO5) ++ (LO6 ++ LO7))

theorem LO_len : LO0.length = 51 ∧ LO1.length = 51 ∧ LO2.length = 51 ∧ LO3.length = 51 ∧
    LO4.length = 51 ∧ LO5.length = 51 ∧ LO6.length = 51 ∧ LO7.length = 51 := by
  decide +kernel

theorem s3_rowsAll : rowsOK PT PC IV SQ GM LMP LGN OR LOall 0 = true := by
  obtain ⟨l0, l1, l2, l3, l4, l5, l6, l7⟩ := LO_len
  simp only [LOall, rowsOK_append, List.length_append, l0, l1, l2, l3, l4, l5, l6, l7,
    Bool.and_eq_true]
  exact ⟨⟨⟨s3_lat0, s3_lat1⟩, s3_lat2, s3_lat3⟩, ⟨s3_lat4, s3_lat5⟩, s3_lat6, s3_lat7⟩

theorem s3_idxAll : idxAll LOall = 2 ^ 408 - 2 := by
  have h := Nat.eq_of_beq_eq_true s3_idx
  have e : Nat.sub (Nat.shiftLeft 1 408) 2 = 2 ^ 408 - 2 := by
    change 1 <<< 408 - 2 = _
    rw [Nat.shiftLeft_eq, one_mul]
  rw [e] at h
  simp only [LOall, idxAll_append]
  exact h

theorem s3_rowLtAll : rowsLtK 408 LOall = true := by
  have h := s3_rowLt
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  simp only [LOall, rowsLtK_append, h0, h1, h2, h3, h4, h5, h6, h7, Bool.and_self]

theorem s3_lat {elt : ℕ → G} (hR : RealT elt PT PC IV SQ)
    (hg : ∀ s < 6, elt (s + 1) = sGen (frameOf m) s) :
    (∀ k < 408, ∃ K : Subgroup G, K ≤ (frameOf m).Sσ ∧ RepM elt (latM LMP k) (K : Set G)) ∧
      ∀ K ≤ (frameOf m).Sσ, ∃ k < 408, RepM elt (latM LMP k) (K : Set G) := by
  have hb := s3_base
  simp only [Bool.and_eq_true] at hb
  obtain ⟨⟨hGM, -⟩, h0⟩ := hb
  have hrep := s3_repSs hR hg
  rw [← Nat.eq_of_beq_eq_true hGM] at hrep
  have h2 : IsPGroup 2 (frameOf m).Sσ := by
    refine IsPGroup.of_card (n := 7) ?_
    have hc := pop_sound hR.inj hrep
    rw [Nat.eq_of_beq_eq_true hGM] at hc
    have : pop M128 = 128 := Nat.eq_of_beq_eq_true (by quickRfl)
    rw [this] at hc
    have e7 : (2 : ℕ) ^ 7 = 128 := by norm_num
    rw [e7, ← hc]
    exact Nat.card_coe_set_eq _
  have hn : LOall.length = 408 := by
    obtain ⟨l0, l1, l2, l3, l4, l5, l6, l7⟩ := LO_len
    simp only [LOall, List.length_append, l0, l1, l2, l3, l4, l5, l6, l7]
  exact lat_sound (N := 408) hR hrep h2 s3_rowsAll s3_idxAll (Nat.eq_of_beq_eq_true h0) hn s3_ord
    s3_rowLtAll (by norm_num) (by norm_num)

theorem ws11_enc : ws11.map encW = CFSG.KBRoute.F442054a.rels := by decide +kernel

theorem s3_pg11 : Finite (PG 6 ws11) ∧ Nat.card (PG 6 ws11) ≤ 128 := by
  have h := CFSG.KBFact.F442054a
  rw [← ws11_enc, (by decide +kernel : CFSG.KBRoute.F442054a.T1.words = [])] at h
  exact TableFact.card ws11 (by norm_num) h

theorem s3_fact11 : (frameOf m).Fact11 m.L := by
  obtain ⟨elt, hR, hg⟩ := s3_real m
  exact fact11_of_twin hR hg s3a_f11 s3_pg11 (frame_S_le m) m.card_L m.card_G

theorem s3_fact12 : (frameOf m).Fact12 := by
  obtain ⟨elt, hR, hg⟩ := s3_real m
  exact fact12_of_twin hR (fun s hs => hg s (by omega)) s3a_f12

theorem s3_fact13 : (frameOf m).Fact13 := by
  obtain ⟨elt, hR, hg⟩ := s3_real m
  exact fact13_of_twin hR hg s3a_f13

end CFSG.KD.G2Three.Sec1T3.Glue

end
