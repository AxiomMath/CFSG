
module

public import Certificates.Kernel.MaxD2.HSU35E.Checks
public import Certificates.Kernel.MaxD2.HSU35E.HeisGlue
public import CFSG.Certificates.Kernel.MaxD2.HeisEqSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HSFiveOvergroupsBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMaxD2.HSU35E

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.KS.PEnum CFSG.KS.Row
open CFSG.PSL3Four.Native CFSG.AGLEmbeddingD2 CFSG.RankThree.Native
open Certificates.MaxD2Perm Certificates.MaxD2Heis Certificates.HSOver
open CFSG.ComponentClassification.PSL3Four (TabRep)

theorem zz_canon : Cn 100 7 zz :=
  he_rt_canon hypsEP ((zK_spec hypsEP.hZ).2 1 (by decide)).1

theorem zz_ne_one {z : Equiv.Perm (Fin 100)} (hz : TabRep (unpack 100 7 zz) z) : z ≠ 1 := by
  rintro rfl
  have t2 : TabRep (unpack 100 7 (pidn 100 7)) (1 : Equiv.Perm (Fin 100)) := by
    rw [← id_u HSU.k_sz]
    exact TabRep.idTab
  have e := u_inj zz_canon (pidn_canon HSU.k_sz) (hz.tab_eq t2)
  have h := ch19831_mv
  unfold mvK at h
  rw [Bool.and_eq_true] at h
  have h1 := h.1
  rw [e, Nat.beq_refl] at h1
  exact absurd h1 (by decide)

section

theorem hsP_z : ∃ z ∈ CFSG.AGLEmbedding.MaxD2.Rsub hsFiveDataP [hs100A, hs100B] ⊓
    Subgroup.centralizer (CFSG.AGLEmbedding.MaxD2.Rsub hsFiveDataP [hs100A, hs100B] :
      Set (Equiv.Perm (Fin hsFiveDataP.n))), TabRep (unpack 100 7 zz) z := by
  obtain ⟨hInv, hR, -⟩ := hsP_heisParts
  have hgi := CFSG.AGLEmbedding.MaxD2.giT_rep (S := [hs100A, hs100B]) (D := hsFiveDataP)
    hsFiveDataP_hS hInv
  have hZ' := CFSG.AGLEmbedding.MaxD2.enum_Z (S := [hs100A, hs100B]) (D := hsFiveDataP)
    hsFiveDataP_hS hgi hR
  exact hZ'.sound _ ((he_mem_zT hypsEP).2 ⟨1, by decide, rfl⟩)

@[expose] noncomputable def gP (i : ℕ) : Equiv.Perm (Fin 100) :=
  (CFSG.AGLEmbedding.MaxD2.repElts hsOverDataP [hs100A, hs100B]).getD i 1

theorem hsOverP_inv : checkInv hsOverDataP = true := by
  have h := HSP.hsOverP_over
  simp only [Certificates.OverD2Perm.checkOver, Bool.and_eq_true] at h
  exact h.1.1.1

theorem gP_tab {i : ℕ} (hi : i < 20) :
    TabRep (unpack 100 7 (HSP.REP i)) (gP i) ∧ TabRep (unpack 100 7 (HSP.REPI i)) (gP i)⁻¹ := by
  have hgi := CFSG.AGLEmbedding.MaxD2.giT_rep (S := [hs100A, hs100B]) (D := hsOverDataP)
    hsFiveDataP_hS hsOverP_inv
  have hs : (repT hsOverDataP).size = 20 := c_rep_size HSP.hypsC
  have hsi : (repI hsOverDataP).size = 20 := c_repi_size HSP.hypsC
  have h1 := CFSG.AGLEmbedding.MaxD2.repT_rep (S := [hs100A, hs100B]) (D := hsOverDataP)
    hsFiveDataP_hS hgi i
  have h2 := CFSG.AGLEmbedding.MaxD2.repI_rep (S := [hs100A, hs100B]) (D := hsOverDataP)
    hsFiveDataP_hS hgi (c_invsRep HSP.hypsC) i
  have e1 : (repT hsOverDataP).getD i (idTab hsOverDataP.n) = (repT hsOverDataP)[i]! := by
    simp [hs, hi]
  have e2 : (repI hsOverDataP).getD i (idTab hsOverDataP.n) = (repI hsOverDataP)[i]! := by
    simp [hsi, hi]
  rw [e1, c_rep_get HSP.hypsC (by exact hi : i < HSP.KP.nr)] at h1
  rw [e2, c_repi_get HSP.hypsC (by exact hi : i < HSP.KP.nr)] at h2
  exact ⟨h1, h2⟩

theorem hsP_cover : ∀ y ∈ CFSG.AGLEmbedding.MaxD2.Gsub (D := hsFiveDataP) [hs100A, hs100B],
    ∃ i ≤ 19, y ∈ CFSG.AGLEmbedding.MaxD2.dcoset
      (CFSG.AGLEmbedding.MaxD2.Nsub hsFiveDataP [hs100A, hs100B]) (gP i) := by
  have h := HSP.hsOverP_over
  simp only [Certificates.OverD2Perm.checkOver, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hInv, hN⟩, -⟩, hMax⟩ := h
  simp only [Certificates.OverD2Perm.checkOverMax, Bool.and_eq_true, beq_iff_eq] at hMax
  obtain ⟨⟨⟨⟨⟨hfp, hinvs⟩, hsum⟩, hdisj⟩, -⟩, -⟩ := hMax
  have hgi := CFSG.AGLEmbedding.MaxD2.giT_rep (S := [hs100A, hs100B]) (D := hsOverDataP)
    hsFiveDataP_hS hInv
  have hcard : Nat.card (CFSG.AGLEmbedding.MaxD2.Gsub (D := hsOverDataP) [hs100A, hs100B]) =
      hsOverDataP.gOrder := by
    change Nat.card (Subgroup.closure {g | g ∈ [hs100A, hs100B]}) = 44352000
    rw [hsP_closure_eq]
    exact card_hs100P
  have hc := CFSG.AGLEmbedding.MaxD2.cover_of_dcoset_check (S := [hs100A, hs100B])
    (D := hsOverDataP) hsFiveDataP_hS hgi hcard hN hfp hinvs hsum hdisj
  have hl : hsOverDataP.repW.length = 19 := rfl
  intro y hy
  obtain ⟨i, hi, hyi⟩ := hc y hy
  exact ⟨i, by omega, hyi⟩

theorem hsP_heisEq : CFSG.AGLEmbedding.MaxD2.HeisDataEq 5 2 3 12 hs100P hsOR0 ∧
    hsON0 = hs100P ⊓ Subgroup.normalizer (hsOR0 : Set (Equiv.Perm (Fin 100))) ∧
    Nat.card hsON0 = 2000 := by
  obtain ⟨hInv, hR, hN, hNorm, hZ, hExp, hComm, hTorus, hCent⟩ := hsP_heisParts
  have hgi := CFSG.AGLEmbedding.MaxD2.giT_rep (S := [hs100A, hs100B]) (D := hsFiveDataP)
    hsFiveDataP_hS hInv
  have hp : hsFiveDataP.p.Prime := by
    change Nat.Prime 5
    norm_num
  obtain ⟨z, hzZ, hzT⟩ := hsP_z
  have hmvA := ch19831_mv
  unfold mvK at hmvA
  rw [Bool.and_eq_true] at hmvA
  have hle := CFSG.AGLEmbedding.MaxD2.normalizer_center_le_of_reps (S := [hs100A, hs100B])
    (D := hsFiveDataP) hsFiveDataP_hS hgi hp hR hNorm hZ hExp hzZ (zz_ne_one hzT) gP 19 rfl
    hsP_cover 4 rfl (by
      intro i h1 h2 k hk
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      have hm := (PK.allN_iff.1 hmvA.2) i' (by omega)
      obtain ⟨tg, tgi⟩ := gP_tab (i := i' + 1) (by omega)
      have hc := c_rep_perm HSP.hypsC (i := i' + 1) (by change i' + 1 < 20; omega)
      exact movesK_perm HSU.k_sz hc.1 hc.2 zz_canon tg tgi hzT hm k hk)
  have h := CFSG.AGLEmbedding.MaxD2.heisDataEq_of_parts (S := [hs100A, hs100B])
    (D := hsFiveDataP) hsFiveDataP_hS hgi hp
    ⟨4, 0, by change (2000 : ℕ) = 5 ^ 3 * (2 ^ 4 * 3 ^ 0); norm_num⟩
    hR hN hNorm hZ hExp hComm hTorus hCent hle
  have hc := CFSG.AGLEmbedding.MaxD2.card_N (S := [hs100A, hs100B]) (D := hsFiveDataP)
    hsFiveDataP_hS hgi hN
  rw [Rsub_hsFiveDataP, Gsub_hsP, Nsub_hsFiveDataP] at h
  rw [Nsub_hsFiveDataP] at hc
  exact ⟨h.1, by rw [inf_comm]; exact h.2.symm, hc⟩

theorem hsR_z : ∃ z ∈ CFSG.AGLEmbedding.MaxD2.Rsub hsFiveDataR [hs100A, hs100B, hs100U] ⊓
    Subgroup.centralizer (CFSG.AGLEmbedding.MaxD2.Rsub hsFiveDataR [hs100A, hs100B, hs100U] :
      Set (Equiv.Perm (Fin hsFiveDataR.n))), TabRep (unpack 100 7 zz) z := by
  obtain ⟨hInv, hR, -⟩ := hsR_heisParts
  have hgi := CFSG.AGLEmbedding.MaxD2.giT_rep (S := [hs100A, hs100B, hs100U]) (D := hsFiveDataR)
    hsFiveDataR_hS hInv
  have hZ' := CFSG.AGLEmbedding.MaxD2.enum_Z (S := [hs100A, hs100B, hs100U]) (D := hsFiveDataR)
    hsFiveDataR_hS hgi hR
  exact hZ'.sound _ ((he_mem_zT hypsER).2 ⟨1, by decide, rfl⟩)

@[expose] noncomputable def gR (i : ℕ) : Equiv.Perm (Fin 100) :=
  (CFSG.AGLEmbedding.MaxD2.repElts hsOverDataR [hs100A, hs100B, hs100U]).getD i 1

theorem gR_tab {i : ℕ} (hi : i < 15) :
    TabRep (unpack 100 7 (HSOver.REP i)) (gR i) ∧
      TabRep (unpack 100 7 (HSOver.REPI i)) (gR i)⁻¹ := by
  have h := HSOver.hsOver_maximal
  simp only [Certificates.OverD2Perm.checkMaximal, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hInv, -⟩, -⟩, hMax⟩ := h
  simp only [checkMax, Bool.and_eq_true, beq_iff_eq] at hMax
  obtain ⟨⟨⟨⟨-, hinvs⟩, -⟩, -⟩, -⟩ := hMax
  have hgi := CFSG.AGLEmbedding.MaxD2.giT_rep (S := [hs100A, hs100B, hs100U])
    (D := hsOverDataR) hsFiveDataR_hS hInv
  have hs : (repT hsOverDataR).size = 15 := rep_size HSOver.hypsM
  have hsi : (repI hsOverDataR).size = 15 := repi_size HSOver.hypsM
  have h1 := CFSG.AGLEmbedding.MaxD2.repT_rep (S := [hs100A, hs100B, hs100U])
    (D := hsOverDataR) hsFiveDataR_hS hgi i
  have h2 := CFSG.AGLEmbedding.MaxD2.repI_rep (S := [hs100A, hs100B, hs100U])
    (D := hsOverDataR) hsFiveDataR_hS hgi hinvs i
  have e1 : (repT hsOverDataR).getD i (idTab hsOverDataR.n) = (repT hsOverDataR)[i]! := by
    simp [hs, hi]
  have e2 : (repI hsOverDataR).getD i (idTab hsOverDataR.n) = (repI hsOverDataR)[i]! := by
    simp [hsi, hi]
  rw [e1, rep_get HSOver.hypsM (by exact hi : i < HSOver.KH.nr)] at h1
  rw [e2, repi_get HSOver.hypsM (by exact hi : i < HSOver.KH.nr)] at h2
  exact ⟨h1, h2⟩

theorem hsR_cover : ∀ y ∈ CFSG.AGLEmbedding.MaxD2.Gsub (D := hsFiveDataR) [hs100A, hs100B, hs100U],
    ∃ i ≤ 14, y ∈ CFSG.AGLEmbedding.MaxD2.dcoset
      (CFSG.AGLEmbedding.MaxD2.Nsub hsFiveDataR [hs100A, hs100B, hs100U]) (gR i) := by
  have h := HSOver.hsOver_maximal
  simp only [Certificates.OverD2Perm.checkMaximal, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hInv, hN⟩, -⟩, hMax⟩ := h
  simp only [checkMax, Bool.and_eq_true, beq_iff_eq] at hMax
  obtain ⟨⟨⟨⟨hfp, hinvs⟩, hsum⟩, hdisj⟩, -⟩ := hMax
  have hgi := CFSG.AGLEmbedding.MaxD2.giT_rep (S := [hs100A, hs100B, hs100U])
    (D := hsOverDataR) hsFiveDataR_hS hInv
  have hcard : Nat.card (CFSG.AGLEmbedding.MaxD2.Gsub (D := hsOverDataR)
      [hs100A, hs100B, hs100U]) = hsOverDataR.gOrder := by
    change Nat.card (Subgroup.closure {g | g ∈ [hs100A, hs100B, hs100U]}) = 88704000
    rw [hsR_closure_eq]
    exact card_hs100R
  have hc := CFSG.AGLEmbedding.MaxD2.cover_of_dcoset_check (S := [hs100A, hs100B, hs100U])
    (D := hsOverDataR) hsFiveDataR_hS hgi hcard hN hfp hinvs hsum hdisj
  have hl : hsOverDataR.repW.length = 14 := rfl
  intro y hy
  obtain ⟨i, hi, hyi⟩ := hc y hy
  exact ⟨i, by omega, hyi⟩

theorem hsR_heisEq : CFSG.AGLEmbedding.MaxD2.HeisDataEq 5 2 3 12 hs100R hsOR0 ∧
    hs100R ⊓ Subgroup.normalizer (hsOR0 : Set (Equiv.Perm (Fin 100))) =
      CFSG.AGLEmbedding.MaxD2.Nsub hsFiveDataR [hs100A, hs100B, hs100U] ∧
    Nat.card (CFSG.AGLEmbedding.MaxD2.Nsub hsFiveDataR [hs100A, hs100B, hs100U]) = 4000 := by
  obtain ⟨hInv, hR, hN, hNorm, hZ, hExp, hComm, hTorus, hCent⟩ := hsR_heisParts
  have hgi := CFSG.AGLEmbedding.MaxD2.giT_rep (S := [hs100A, hs100B, hs100U]) (D := hsFiveDataR)
    hsFiveDataR_hS hInv
  have hp : hsFiveDataR.p.Prime := by
    change Nat.Prime 5
    norm_num
  obtain ⟨z, hzZ, hzT⟩ := hsR_z
  have hmvA := ch19832_mv
  unfold mvK at hmvA
  rw [Bool.and_eq_true] at hmvA
  have hle := CFSG.AGLEmbedding.MaxD2.normalizer_center_le_of_reps
    (S := [hs100A, hs100B, hs100U]) (D := hsFiveDataR) hsFiveDataR_hS hgi hp hR hNorm hZ hExp hzZ
    (zz_ne_one hzT) gR 14 rfl hsR_cover 4 rfl (by
      intro i h1 h2 k hk
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      have hm := (PK.allN_iff.1 hmvA.2) i' (by omega)
      obtain ⟨tg, tgi⟩ := gR_tab (i := i' + 1) (by omega)
      have hc := rep_perm HSOver.hypsM (i := i' + 1) (by change i' + 1 < 15; omega)
      exact movesK_perm HSU.k_sz hc.1 hc.2 zz_canon tg tgi hzT hm k hk)
  have h := CFSG.AGLEmbedding.MaxD2.heisDataEq_of_parts (S := [hs100A, hs100B, hs100U])
    (D := hsFiveDataR) hsFiveDataR_hS hgi hp
    ⟨5, 0, by change (4000 : ℕ) = 5 ^ 3 * (2 ^ 5 * 3 ^ 0); norm_num⟩
    hR hN hNorm hZ hExp hComm hTorus hCent hle
  have hc := CFSG.AGLEmbedding.MaxD2.card_N (S := [hs100A, hs100B, hs100U]) (D := hsFiveDataR)
    hsFiveDataR_hS hgi hN
  rw [Rsub_hsFiveDataR, Gsub_hsR] at h
  exact ⟨h.1, by rw [inf_comm]; exact h.2, hc⟩

end

end CertificateChecks.KernelMaxD2.HSU35E

end
