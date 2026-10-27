
module

public import Certificates.Kernel.Sporadic.L2C.G1Base
public import CFSG.Sporadic.SuzRecog.LevelTwoCoverElim

public section

namespace CertificateChecks.KernelSpor.L2CG

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.Sporadic.SuzRecog.LevelTwo CFSG.Sporadic.SuzRecog.LevelTwoCover
open CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.ElimCert
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.L2K CertificateChecks.KernelSpor.L2CK
open CertificateChecks.KernelSpor.L2G (sB band bif_true nbeq nblt nble nblt_f nble_f allN_get)

theorem nbC_lt (HB : BaseH) {u k : Nat} (hl : u % 2997 < 2835) (hk : k < 36) : nbC u k < 8991 := by
  have := nbK_lt HB hl hk
  rw [nbC_eq]
  omega

theorem nbC_mod (HB : BaseH) {u k : Nat} (hl : u % 2997 < 2835) (hk : k < 36) :
    nbC u k % 2997 = nbK (u % 2997) k := by
  have := nbK_lt HB hl hk
  rw [nbC_eq]
  omega

theorem adjB_listed {u w j : Nat} (hu : u < 8991) (hl : u % 2997 < 2835) (hj : j < 36)
    (e : nbC u j = w) (hne : u ≠ w) : adjB nbrC u w = true := by
  unfold adjB
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true]
  exact ⟨hne, Or.inl (occB_iff.2 ⟨j, by rw [nbrC_size hu hl]; exact hj, by rw [nbrC_low hu hl hj, e]⟩)⟩

theorem adjB_comm (u w : Nat) : adjB nbrC u w = adjB nbrC w u := by
  unfold adjB
  rw [bne_comm, Bool.or_comm]

theorem list_of (HB : BaseH) {u : Nat} (hu : u < 8991) (hl : u % 2997 < 2835) {k : Nat}
    (hk : k < 36)
    (h : listR u (u / 2997) (L2NB.F (u % 2997)) (L2CV.F (u % 2997)) (L2CR u) k = true) :
    CFSG.KC.RankElim.listOK 8991 nbrC tParC rkK apK bpK (triC nbrC) u k = true := by
  have hy8 := nbC_lt HB hl hk
  unfold listR at h
  rw [sB, sB, sB] at h
  change bIf(Nat.beq (rkK u k) 0,
    bIf(bAnd(Nat.blt 0 (nbC u k), Nat.beq (tParC (nbC u k)) u), true,
      bAnd(Nat.blt 0 u, Nat.beq (tParC u) (nbC u k))),
    strictB (apK u k) fun a => strictB (bpK u k) fun b => strictB (nbC u a) fun z =>
    bAnd(Nat.blt a 36, bAnd(Nat.blt b 36, bAnd(Nat.blt (rkK u a) (rkK u k),
    bAnd(Bool.not (Nat.beq u z), bAnd(Bool.not (Nat.beq u (nbC u k)),
      bIf(Nat.blt (Nat.mod z 2997) 2835,
        bAnd(Nat.ble 2835 (Nat.mod (nbC u k) 2997),
          bAnd(Nat.beq (nbC z b) (nbC u k), Nat.blt (rkK z b) (rkK u k))),
        bAnd(Nat.blt (Nat.mod (nbC u k) 2997) 2835,
          bAnd(Nat.beq (nbC (nbC u k) b) z, Nat.blt (rkK (nbC u k) b) (rkK u k)))))))))) = true at h
  unfold CFSG.KC.RankElim.listOK
  simp only [nbrC_low hu hl hk, nbrC_size hu hl]
  by_cases h0 : rkK u k = 0
  · rw [h0, Nat.beq_refl] at h
    have h' : bIf(bAnd(Nat.blt 0 (nbC u k), Nat.beq (tParC (nbC u k)) u), true,
        bAnd(Nat.blt 0 u, Nat.beq (tParC u) (nbC u k))) = true := h
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, h0, true_and]
    left
    right
    rw [L2G.bIf_or, Bool.or_eq_true, band, band, nblt, nblt, nbeq, nbeq] at h'
    exact h'
  · rw [Q3AG.nbeq_false h0, sB, sB, sB] at h
    rw [band, band, band, band, band] at h
    obtain ⟨ha, hb, hra, huz, huy, hbr⟩ := h
    rw [nblt] at ha hb hra
    rw [not_true] at huz huy
    rw [bif_true] at hbr
    have huz' := nbeq_f huz
    have huy' := nbeq_f huy
    have hz8 := nbC_lt HB hl ha
    have hzm := nbC_mod HB hl ha
    have hym := nbC_mod HB hl hk
    simp only [nbrC_low hu hl ha]
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne,
      ne_eq]
    right
    by_cases hzt : nbC u (apK u k) % 2997 < 2835
    · have hb' := hbr.1 (nblt.2 hzt)
      rw [band, band, nble, nbeq, nblt] at hb'
      obtain ⟨hyt, hzy, hrz⟩ := hb'
      change 2835 ≤ nbC u k % 2997 at hyt
      have hzy' : nbC u (apK u k) ≠ nbC u k := fun e => by rw [e] at hzt; omega
      refine ⟨⟨⟨⟨⟨⟨⟨by omega, ha⟩, hz8⟩, huz'⟩, hzy'⟩, hra⟩, Or.inl ⟨⟨by rw [nbrC_size hz8 hzt]; exact hb,
        by rw [nbrC_low hz8 hzt hb]; exact hzy⟩, hrz⟩⟩, ?_⟩
      unfold triC
      simp only [Bool.and_eq_true, beq_iff_eq]
      refine ⟨⟨⟨adjB_listed hu hl ha rfl huz', adjB_listed hz8 hzt hb hzy hzy'⟩,
        adjB_listed hu hl hk rfl huy'⟩, ?_⟩
      split_ifs <;> omega
    · have hb' := hbr.2 (nblt_f hzt)
      rw [band, band, nblt, nbeq, nblt] at hb'
      obtain ⟨hyt, hzy, hrz⟩ := hb'
      change nbC u k % 2997 < 2835 at hyt
      have hzy' : nbC u (apK u k) ≠ nbC u k := fun e => by rw [e] at hzt; omega
      refine ⟨⟨⟨⟨⟨⟨⟨by omega, ha⟩, hz8⟩, huz'⟩, hzy'⟩, hra⟩, Or.inr ⟨⟨by rw [nbrC_size hy8 hyt]; exact hb,
        by rw [nbrC_low hy8 hyt hb]; exact hzy⟩, hrz⟩⟩, ?_⟩
      unfold triC
      simp only [Bool.and_eq_true, beq_iff_eq]
      refine ⟨⟨⟨adjB_listed hu hl ha rfl huz', ?_⟩, adjB_listed hu hl hk rfl huy'⟩, ?_⟩
      · rw [adjB_comm]
        exact adjB_listed hy8 hyt hb hzy (Ne.symm hzy')
      · split_ifs <;> omega

@[expose] def RowH : Prop := ∀ u < 8991, rowK u = true

theorem coverElim_of (HB : BaseH) (H : RowH) : CoverElim := by
  refine ⟨tParC, tDepC, rkK, apK, bpK, ?_⟩
  unfold CFSG.KC.RankElim.ok
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq]
  refine ⟨⟨by norm_num, fun x hx => ?_⟩, fun u hu k hk => ?_⟩
  · have h := H x hx
    unfold rowK rowG at h
    rw [band] at h
    have ht := h.1
    unfold treeC at ht
    by_cases h0 : x = 0
    · exact Or.inl h0
    · rw [Q3AG.nbeq_false h0, sB, band, band, nblt, nblt] at ht
      obtain ⟨hp, hd, ha⟩ := ht
      refine Or.inr ⟨⟨hp, hd⟩, ?_⟩
      rw [adjB_nbrC hp hx]
      exact ha
  · by_cases hl : u % 2997 < 2835
    · rw [nbrC_size hu hl] at hk
      have h := H u hu
      unfold rowK rowG at h
      rw [band] at h
      have h2 := h.2
      rw [sB, show Nat.blt (Nat.mod u 2997) 2835 = true from nblt.2 hl, sB, sB, sB, sB] at h2
      exact list_of HB hu hl hk (allN_get h2 hk)
    · rw [nbrC_of_ge hu (by omega)] at hk
      simp at hk

end CertificateChecks.KernelSpor.L2CG

end
