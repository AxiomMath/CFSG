module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import Certificates.Kernel.M24.Words
import Certificates.Kernel.M24.Lce
import CFSG.Certificates.Kernel.J4.M24Checks.M24RG
import CFSG.Certificates.Kernel.Common.Harness
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CertificateChecks.KernelBounds

open CFSG.KM24 CFSG.KM24.Words CFSG.Certificates

theorem m24_rsOk : rsOk CFSG.KD.M24R.T CFSG.KD.M24R.P (nat_lit 4) (nat_lit 24) CFSG.KD.M24R.R0
    CFSG.KD.M24R.A0 CFSG.KD.M24R.G0
    [(CFSG.KD.M24R.B0, (nat_lit 120), CFSG.KD.M24R.A1, CFSG.KD.M24R.G1),
      (CFSG.KD.M24R.B1, (nat_lit 120), CFSG.KD.M24R.A2, CFSG.KD.M24R.G2),
      (CFSG.KD.M24R.B2, (nat_lit 1), CFSG.KD.M24R.A3, CFSG.KD.M24R.G3)]
    CFSG.KD.M24R.N CFSG.KD.M24R.Rn (nat_lit 96) (nat_lit 7) = true :=
  rsOk_intro CFSG.KJ4.M24G.ranges CFSG.KJ4.M24G.init (rsChain_cons CFSG.KJ4.M24G.rep0
    (rsChain_cons CFSG.KJ4.M24G.rep1 (rsChain_cons CFSG.KJ4.M24G.rep2
      (rsChain_nil CFSG.KJ4.M24G.next))))

theorem m24_gens : TauCeti.Sporadic.m24Presentation.generatorCount = 2 := by
  simp [TauCeti.GroupPresentation.generatorCount, TauCeti.Sporadic.m24Presentation_generatorNames]

theorem m24_small : sigSmall CFSG.KBAlt.M24.rels = true := by quickRfl

theorem m24 : Finite TauCeti.SporadicName.M24.Group ∧
    Nat.card TauCeti.SporadicName.M24.Group ≤ 244823040 := by
  change Finite TauCeti.Sporadic.m24Presentation.Group ∧
    Nat.card TauCeti.Sporadic.m24Presentation.Group ≤ 244823040
  set P := TauCeti.Sporadic.m24Presentation
  have hR0 : ∀ r ∈ CFSG.KD.M24R.R0, pval (KB.tcGen P) r = 1 := by
    intro r hr
    rw [eqRL_eq _ _ CFSG.KBAlt.M24.r0_bind, encRels_eq, List.mem_map] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    obtain ⟨hs, hl⟩ := sigSmall_spec _ m24_small w hw
    rw [pval_encRel _ w hs hl]
    exact KB.sword_rels P CFSG.KBAlt.M24.rels_eq w hw
  obtain ⟨h, hRn, -, hne, hidx⟩ := rsOk_sound m24_rsOk (KB.tcGen P) hR0
  have hA : Subgroup.closure (KB.tcGen P '' {g | 2 * g < 4}) = ⊤ := by
    have e : {g | 2 * g < 4} = {g | g < P.generatorCount} := by
      ext g
      simp only [Set.mem_ofPred_eq, m24_gens, P]
      omega
    rw [e, KB.closure_tcGen P]
  have hrels : ∀ r < 29, LCE.bval h (CFSG.KC.LceS.wWord (CFSG.KD.M24B.selRT r))
      (CFSG.KC.LceS.wLen (CFSG.KD.M24B.selRT r)) = 1 := by
    intro r hr
    rw [bval_rtBind h (by norm_num) CFSG.KJ4.M24G.rt_bind r hr]
    apply hRn
    apply getR_mem
    rw [← lenR_eq, Nat.beq_eq.mp CFSG.KJ4.M24G.rn_len]
    exact hr
  obtain ⟨hl0, hl⟩ := LCE.lceOk_sound CertificateChecks.KernelBounds.M24.lce_ok h hrels
  have hST : CFSG.KD.M24B.selST 0 = 8196 := Nat.beq_eq.mp CFSG.KJ4.M24G.st0
  have hW : CFSG.KC.LceS.wWord 8196 = 2 := Nat.beq_eq.mp (by quickRfl)
  have hL : CFSG.KC.LceS.wLen 8196 = 1 := Nat.beq_eq.mp (by quickRfl)
  have hl2 : CFSG.KC.wLet 2 0 = 2 := Nat.beq_eq.mp (by quickRfl)
  have hb : LCE.bval h (CFSG.KC.LceS.wWord 8196) (CFSG.KC.LceS.wLen 8196) = h 1 := by
    rw [hW, hL]
    simp [LCE.bval, LCE.letV, hl2]
  have hK : Subgroup.closure ((fun j => LCE.bval h (CFSG.KC.LceS.wWord (CFSG.KD.M24B.selST j))
      (CFSG.KC.LceS.wLen (CFSG.KD.M24B.selST j))) '' {j | j < 1}) = Subgroup.zpowers (h 1) := by
    rw [Subgroup.zpowers_eq_closure]
    congr 1
    ext x
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_singleton_iff, Nat.lt_one_iff]
    constructor
    · rintro ⟨j, rfl, rfl⟩
      rw [hST, hb]
    · rintro rfl
      exact ⟨0, rfl, by rw [hST, hb]⟩
  have hH : Subgroup.closure (h '' {g | 2 * g < 14}) = Subgroup.closure (h '' {i | i < 7}) := by
    congr 2
    ext g
    simp only [Set.mem_ofPred_eq]
    omega
  rw [hK, hH] at hl0 hl
  have hpow : h 1 ^ 23 = 1 := by
    obtain ⟨hn, hlet⟩ := mAnd_eq_true CFSG.KJ4.M24G.pow7
    have h7 := hrels 7 (by norm_num)
    change LCE.bval h (Nat.shiftRight (CFSG.KD.M24B.selRT 7) 12)
      (Nat.land (Nat.shiftRight (CFSG.KD.M24B.selRT 7) 2) 1023) = 1 at h7
    rw [Nat.beq_eq.mp hn, bval_allLet h hlet] at h7
    have e : LCE.letV h 3 = (h 1)⁻¹ := rfl
    rw [e, inv_pow, inv_eq_one] at h7
    exact h7
  have hord : orderOf (h 1) ∣ 23 := orderOf_dvd_of_pow_eq_one hpow
  have hKc : Nat.card (Subgroup.zpowers (h 1)) ≤ 23 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) hord
  have : Finite (Subgroup.zpowers (h 1)) := Nat.finite_of_card_ne_zero (by
    rw [Nat.card_zpowers]
    exact (Nat.pos_of_dvd_of_pos hord (by norm_num)).ne')
  obtain ⟨hHf, hHc⟩ := card_le_relIndex_mul hl0
  rw [hA] at hne hidx
  obtain ⟨hTf, hTc⟩ := card_le_relIndex_mul hne
  refine ⟨Finite.of_equiv _ Subgroup.topEquiv.toEquiv, ?_⟩
  rw [← Subgroup.card_top]
  calc Nat.card (⊤ : Subgroup P.Group)
      ≤ _ := hTc
    _ ≤ 24 * (443520 * 23) := Nat.mul_le_mul hidx
        (hHc.trans (Nat.mul_le_mul hl hKc))
    _ = 244823040 := by norm_num

end CertificateChecks.KernelBounds

end
