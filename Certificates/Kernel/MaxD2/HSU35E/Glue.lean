
module

public import Certificates.Kernel.MaxD2.HSU35E.Checks
public import Certificates.Kernel.MaxD2.HSU35E.HeisGlue
public import CFSG.Certificates.Kernel.MaxD2.BlockSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HSFiveU35Base
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HSFiveOvergroupsBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMaxD2.HSU35E

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.KS.PEnum CFSG.KS.Row
open CFSG.PSL3Four.Native CFSG.AGLEmbeddingD2
open Certificates.MaxD2Perm Certificates.MaxD2Heis Certificates.HSU35
open CFSG.ComponentClassification.PSL3Four (TabRep Enumerates)

section

theorem tab_xy (k : Nat) (hk : k < 2) :
    TabRep (unpack 100 7 (HSU.GP k)) (hsU35S.getD k 1) := by
  have h := hsU35_gsU k
  have e : dataU.gT.getD k (idTab dataU.n) = dataU.gT[k]! := by
    have hs : dataU.gT.size = 2 := rfl
    simp [hs, hk]
  rw [e, HSU.gT_bind k hk] at h
  exact h

theorem tab_t0 : TabRep (unpack 100 7 (HSP.NE.G 2)) hsOT0 := by
  have e : wT hsFiveDataP hsFiveDataP.tW = unpack 100 7 (HSP.NE.G 2) := he_wT_u hypsEP ch19831_tw
  have h := hsU35_wT hsFiveTW
  rw [show wT hsFiveDataP hsFiveTW = wT hsFiveDataP hsFiveDataP.tW from rfl, e] at h
  exact h

@[expose] def omSet : Set (Fin 100) := {p | r32 OM p = 1}

theorem om_parts : rowBitK 100 OM = true ∧ r32 OM 0 = 1 := by
  have h := ch19850_om
  rw [Bool.and_eq_true] at h
  exact ⟨h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem om_le (p : Fin 100) : r32 OM p ≤ 1 := rowBitK_sound om_parts.1 p p.2

theorem om_fix {σ : Equiv.Perm (Fin 100)} (h : ∀ p : Fin 100, r32 OM (σ p) = Nat.xor (r32 OM p) 0)
    (p : Fin 100) : σ p ∈ omSet ↔ p ∈ omSet := by
  simp only [omSet, Set.mem_setOf_eq]
  have e : Nat.xor (r32 OM p) 0 = r32 OM p := Nat.xor_zero _
  rw [h p, e]

theorem om_swap {σ : Equiv.Perm (Fin 100)} (h : ∀ p : Fin 100, r32 OM (σ p) = Nat.xor (r32 OM p) 1)
    (p : Fin 100) : σ p ∈ omSet ↔ p ∉ omSet := by
  simp only [omSet, Set.mem_setOf_eq]
  rw [h p]
  have := om_le p
  rcases (by omega : r32 OM p = 0 ∨ r32 OM p = 1) with e | e <;> rw [e] <;> decide

theorem hsU35E_card_le : Nat.card hsOUA ≤ 126000 := by
  have h0 := ch19850_blk
  unfold blkK at h0
  rw [Bool.and_eq_true, Bool.and_eq_true] at h0
  obtain ⟨b0, b1, b2⟩ := h0
  have hx := tab_xy 0 (by decide)
  have hy := tab_xy 1 (by decide)
  rw [hsU35S_eq] at hx hy
  have hA : ∀ g ∈ ({hsOX, hsOY} : Set (Equiv.Perm (Fin 100))), ∀ p, g p ∈ omSet ↔ p ∈ omSet := by
    rintro g (rfl | rfl) p
    · exact om_fix (blockK_perm hx b0) p
    · exact om_fix (blockK_perm hy b1) p
  have hle := two_mul_card_le_of_block omSet hA hsOUA_le_UA2
    (by unfold hsOUA2; exact Subgroup.subset_closure (by simp) : hsOT0 ∈ hsOUA2)
    (om_swap (blockK_perm tab_t0 b2)) (p₀ := (0 : Fin 100)) om_parts.2
  rw [card_hsOUA2] at hle
  have e : Subgroup.closure ({hsOX, hsOY} : Set (Equiv.Perm (Fin 100))) = hsOUA := rfl
  rw [e] at hle
  omega

theorem rep0 : (CFSG.AGLEmbedding.MaxD2.repElts dataU hsU35S).getD 0 1 = 1 := rfl

theorem rep1 : (CFSG.AGLEmbedding.MaxD2.repElts dataU hsU35S).getD 1 1 = hsOW := by
  rw [← hsU35_w]
  rfl

theorem hsU35E_sum : ∑ i ∈ Finset.range 2, Nat.card hsONU * Nat.card hsONU /
    Nat.card (CFSG.AGLEmbedding.MaxD2.conjStab hsONU
      ((CFSG.AGLEmbedding.MaxD2.repElts dataU hsU35S).getD i 1)) = 126000 := by
  obtain ⟨-, -, hN, -, -, -, -, -, -, -, hMax⟩ := hsU35_parts_heis
  simp only [checkMax, Bool.and_eq_true, beq_iff_eq] at hMax
  obtain ⟨⟨⟨⟨hfp, hinvs⟩, hsum⟩, -⟩, -⟩ := hMax
  have h := CFSG.AGLEmbedding.MaxD2.sum_eq hsU35_gsU hsU35_giU hN hfp hinvs hsum
  rw [hsU35_Nsub] at h
  exact h

theorem hsU35E_disj : ∀ i ≤ 1, ∀ j ≤ 1, i < j → ∀ a ∈ hsONU,
    ((CFSG.AGLEmbedding.MaxD2.repElts dataU hsU35S).getD i 1)⁻¹ * a *
      (CFSG.AGLEmbedding.MaxD2.repElts dataU hsU35S).getD j 1 ∉ hsONU := by
  intro i hi j hj hij a ha hm
  obtain rfl : i = 0 := by omega
  obtain rfl : j = 1 := by omega
  rw [rep0, rep1, inv_one, one_mul] at hm
  apply hsOW_not_mem
  have e : hsOW = a⁻¹ * (a * hsOW) := by group
  rw [e]
  exact hsONU.mul_mem (hsONU.inv_mem ha) hm

theorem hsU35E_gmem : ∀ i ≤ 1, (CFSG.AGLEmbedding.MaxD2.repElts dataU hsU35S).getD i 1 ∈ hsOUA := by
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · rw [rep0]
    exact hsOUA.one_mem
  · rw [rep1]
    exact hsOW_mem

theorem hsU35E_card_ge : 126000 ≤ Nat.card hsOUA := by
  have h := sum_dcoset_le hsONU_le_UA (fun i => (CFSG.AGLEmbedding.MaxD2.repElts dataU hsU35S).getD i 1)
    1 hsU35E_gmem hsU35E_disj
  rw [hsU35E_sum] at h
  exact h

theorem hsU35E_card : Nat.card hsOUA = 126000 := le_antisymm hsU35E_card_le hsU35E_card_ge

theorem hsU35E_cover : ∀ y ∈ hsOUA, y ∈ hsONU ∨ y ∈ CFSG.AGLEmbedding.MaxD2.dcoset hsONU hsOW := by
  intro y hy
  obtain ⟨i, hi, hyi⟩ := CFSG.AGLEmbedding.MaxD2.exists_dcoset_of_sum hsONU_le_UA
    (fun i => (CFSG.AGLEmbedding.MaxD2.repElts dataU hsU35S).getD i 1) 1 hsU35E_gmem
    (by rw [hsU35E_sum, hsU35E_card]) hsU35E_disj y hy
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · left
    obtain ⟨a, ha, b, hb, rfl⟩ := hyi
    rw [rep0, mul_one]
    exact hsONU.mul_mem ha hb
  · right
    have e := rep1
    simp only at hyi
    rw [e] at hyi
    exact hyi

theorem tab_w : TabRep (unpack 100 7 (HSU.REP 1)) hsOW := by
  have h := CFSG.AGLEmbedding.MaxD2.repT_rep hsU35_gsU hsU35_giU 1
  have hs : (repT dataU).size = 2 := c_rep_size HSU.hypsH.toHypsC
  have e : (repT dataU).getD 1 (idTab dataU.n) = (repT dataU)[1]! := by simp [hs]
  rw [rep1, e, c_rep_get HSU.hypsH.toHypsC (by decide : 1 < HSU.KH.nr)] at h
  exact h

theorem tab_wi : TabRep (unpack 100 7 (HSU.REPI 1)) hsOW⁻¹ := by
  have h := CFSG.AGLEmbedding.MaxD2.repI_rep hsU35_gsU hsU35_giU (c_invsRep HSU.hypsH.toHypsC) 1
  have hs : (repI dataU).size = 2 := c_repi_size HSU.hypsH.toHypsC
  have e : (repI dataU).getD 1 (idTab dataU.n) = (repI dataU)[1]! := by simp [hs]
  rw [rep1, e, c_repi_get HSU.hypsH.toHypsC (by decide : 1 < HSU.KH.nr)] at h
  exact h

theorem tab_t : TabRep (unpack 100 7 (HSU.TT 0)) hsOT := by
  have h := CFSG.AGLEmbedding.MaxD2.wT_rep hsU35_gsU hsU35_giU dataU.tW
  rw [c_wT_u HSU.hypsH.toHypsC HSU.k_tw, show dataU.tW = xyTW from rfl, hsU35_t] at h
  exact h

theorem tab_ti : TabRep (unpack 100 7 (HSU.TT 1)) hsOT⁻¹ :=
  tab_t.inv (size_u _) (inv_comp HSU.k_tp)

theorem hsU35E_cu : ∀ r ∈ hsOR0, hsOW * (r * hsOT) * hsOW⁻¹ * hsOT⁻¹ ∉ hsOR0 := by
  intro r hr hq
  obtain ⟨-, hR, -, -, -, -, hExp, -, -, -, -⟩ := hsU35_parts_heis
  have hexp := CFSG.AGLEmbedding.MaxD2.exp_R hsU35_gsU hsU35_giU hR hExp
  rw [hsU35_Rsub] at hexp
  have hR' := CFSG.AGLEmbedding.MaxD2.enum_RH hsU35_gsU hsU35_giU hR
  rw [hsU35_Rsub] at hR'
  obtain ⟨k, hk, hkr⟩ := hR'.exists_pos hr
  obtain ⟨eR, -⟩ := h_rEnum_eq HSU.hypsH
  rw [eR, rec_size] at hk
  rw [eR, rec_get hk] at hkr
  have hkr' : TabRep (unpack 100 7 (HSU.RE.T k)) r := hkr
  have hcr : Cn 100 7 (HSU.RE.T k) := h_rt_canon HSU.hypsH hk
  have hcw := c_rep_perm HSU.hypsH.toHypsC (by decide : 1 < HSU.KH.nr)
  have hcw1 : Cn 100 7 (HSU.REP 1) := hcw.1
  have hcw2 : Cn 100 7 (HSU.REPI 1) := hcw.2
  have hct := perm_canon HSU.k_tp HSU.k_sz
  have q1 := tab_pcomp hcw1 hcr tab_w hkr'
  have q2 := tab_pcomp (cc hcw1 hcr) hct.1 q1 tab_t
  have q3 := tab_pcomp (cc (cc hcw1 hcr) hct.1) hcw2 q2 tab_wi
  have q4 := tab_pcomp (cc (cc (cc hcw1 hcr) hct.1) hcw2) hct.2 q3 tab_ti
  have hne := powNe_perm HSU.k_sz (cc (cc (cc (cc hcw1 hcr) hct.1) hcw2) hct.2) q4
    ((PK.allN_iff.1 ch19850_cu) k hk)
  apply hne
  have e : hsOW * r * hsOT * hsOW⁻¹ * hsOT⁻¹ = hsOW * (r * hsOT) * hsOW⁻¹ * hsOT⁻¹ := by group
  rw [e]
  exact hexp _ hq

theorem hsONU_le_closure :
    hsONU ≤ Subgroup.closure ((hsOR0 : Set (Equiv.Perm (Fin 100))) ∪ {hsOT}) := by
  have hu : hsOU0 ∈ hsOR0 := by
    unfold hsOR0
    exact Subgroup.subset_closure (by simp)
  have hv : hsOV0 ∈ hsOR0 := by
    unfold hsOR0
    exact Subgroup.subset_closure (by simp)
  unfold hsONU
  rw [Subgroup.closure_le]
  rintro g (rfl | rfl | rfl)
  · exact Subgroup.subset_closure (Or.inl hu)
  · exact Subgroup.subset_closure (Or.inl hv)
  · exact Subgroup.subset_closure (Or.inr rfl)

theorem hsU35E_cent :
    hsOUA ⊓ Subgroup.centralizer ({hsOT} : Set (Equiv.Perm (Fin 100))) = Subgroup.zpowers hsOT :=
  centralizer_eq_zpowers_of_dcosets hsU35_mem_U.1 hsOT_mem_normalizer hsONU_le_closure
    hsU35E_cover hsOT_commute_R0 hsU35E_cu

end

end CertificateChecks.KernelMaxD2.HSU35E

end
