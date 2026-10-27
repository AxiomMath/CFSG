module

public import Certificates.Kernel.L34FU.Chk
public import Certificates.Kernel.L34FU.Data
public import Certificates.Kernel.LocalComp.L34E16F
public import Certificates.Kernel.L34W.Glue
public import CFSG.Certificates.Kernel.L34FUSound
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CertificateChecks.KernelL34FU

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.L34FU
open CFSG.KC.L34W CFSG.KC.L34W.OCS CFSG.KC.L34KSnd CFSG.KC.L34FU.Snd
open CertificateChecks.KernelLC CertificateChecks.KernelLC.L34X CertificateChecks.KernelL34W
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real
open CFSG.ComponentClassification.TBLit.L34FU

theorem psy_parts : PSY.k = 6 ∧ (∀ j < 4, PSY.G j = ETE.G j) ∧ PSY.G 4 = L34R.G 4 ∧
    PSY.G 5 = L34R.G 5 := by
  obtain ⟨h1, h2, h3, h4⟩ := (by simpa only [bAnd_iff] using ch23204_gens :
    Nat.beq PSY.k 6 = true ∧ allN 4 (fun j => Nat.beq (PSY.G j) (ETE.G j)) = true ∧
      Nat.beq (PSY.G 4) (L34R.G 4) = true ∧ Nat.beq (PSY.G 5) (L34R.G 5) = true)
  exact ⟨Nat.eq_of_beq_eq_true h1, fun j hj => Nat.eq_of_beq_eq_true (allN_spec h2 j hj),
    Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4⟩

theorem psy_hd : penumHdK (pidn 42 6) PSY.cnt 256 PSY.T PSY.PL = true ∧ PSY.cnt = 256 := by
  obtain ⟨h1, h2⟩ := (by simpa only [bAnd_iff] using ch23204_hd :
    penumHdK (pidn 42 6) PSY.cnt 256 PSY.T PSY.PL = true ∧ Nat.beq PSY.cnt 256 = true)
  exact ⟨h1, Nat.eq_of_beq_eq_true h2⟩

theorem word_parts {j : Nat} (hj : j < 4) :
    wordTab (wT₀.getD j []) = unpack 42 6 (PSY.G j) ∧ Cn (PSY.G j) := by
  rw [psy_parts.2.1 j hj, L34E16.parts.2.1 j hj, lget2_eq]
  exact L34E16.wordTab_unpack _

theorem gensP : GensOK 42 6 PSY.k PSY.G fuPGens := by
  refine ⟨by rw [psy_parts.1]; rfl, fun j hj => ?_⟩
  rw [psy_parts.1] at hj
  match j, hj with
  | 0, _ => exact word_parts (j := 0) (by decide)
  | 1, _ => exact word_parts (j := 1) (by decide)
  | 2, _ => exact word_parts (j := 2) (by decide)
  | 3, _ => exact word_parts (j := 3) (by decide)
  | 4, _ => exact ⟨by rw [psy_parts.2.2.1]; exact L34Cert.e5, by
      rw [psy_parts.2.2.1]; exact L34Cert.cnG (by decide)⟩
  | 5, _ => exact ⟨by rw [psy_parts.2.2.2]; exact L34Cert.e6, by
      rw [psy_parts.2.2.2]; exact L34Cert.cnG (by decide)⟩

theorem ptP : ∀ i < PSY.cnt, penumPtK 42 6 (mask 6) (42 * 6) false PSY.G PSY.GI PSY.k PSY.cnt
    PSY.T PSY.PL PSY.POS PSY.SRT PSY.SRI i = true := fun i hi =>
  penumSl_spec ch23204_sl i (Nat.zero_le _) (by rw [psy_hd.2] at hi; omega) hi

theorem encP : enumOK 42 fuPGens (penumRec 42 6 PSY.cnt PSY.T PSY.PL) = true :=
  (penumK_left_sound L34E16.hsz gensP psy_hd.1 ptP).2

@[expose] def genSet : Set (Equiv.Perm (Fin 42)) :=
  {wordPerm (wT₀.getD 0 []), wordPerm (wT₀.getD 1 []), wordPerm (wT₀.getD 2 []),
    wordPerm (wT₀.getD 3 []), g₅, g₆}

noncomputable abbrev P : Subgroup (Equiv.Perm (Fin 42)) := Subgroup.closure genSet

theorem enumerates_P : Enumerates P (penumRec 42 6 PSY.cnt PSY.T PSY.PL).tabs.toList := by
  refine enumerates_closure (fun a ha => ?_) (fun j hj => ?_) encP
  · simp only [genSet, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by decide, tabRep_wordTab _⟩
    · exact ⟨1, by decide, tabRep_wordTab _⟩
    · exact ⟨2, by decide, tabRep_wordTab _⟩
    · exact ⟨3, by decide, tabRep_wordTab _⟩
    · exact ⟨4, by decide, tabRep_g₅⟩
    · exact ⟨5, by decide, tabRep_g₆⟩
  · have hj' : j < 6 := hj
    match j, hj' with
    | 0, _ => exact ⟨wordPerm (wT₀.getD 0 []), by simp [genSet], tabRep_wordTab _⟩
    | 1, _ => exact ⟨wordPerm (wT₀.getD 1 []), by simp [genSet], tabRep_wordTab _⟩
    | 2, _ => exact ⟨wordPerm (wT₀.getD 2 []), by simp [genSet], tabRep_wordTab _⟩
    | 3, _ => exact ⟨wordPerm (wT₀.getD 3 []), by simp [genSet], tabRep_wordTab _⟩
    | 4, _ => exact ⟨g₅, by simp [genSet], tabRep_g₅⟩
    | 5, _ => exact ⟨g₆, by simp [genSet], tabRep_g₆⟩

theorem card_P : Nat.card P = 256 := by
  rw [enumerates_P.card, Array.length_toList, penumRec_eq, Array.size_ofFn, psy_hd.2]

theorem pow8_of_mem_P {g : Equiv.Perm (Fin 42)} (hg : g ∈ P) : g ^ 8 = 1 := by
  obtain ⟨t, ht, hrep⟩ := enumerates_P.complete g hg
  obtain ⟨q, hq, rfl⟩ := mem_penumRec ht
  exact ex8_of (penumPt_canon (ptP q hq)) hrep
    (allN_spec ch23204_exp q (by rw [← psy_hd.2]; exact hq))

theorem P_le_R : P ≤ R := by
  refine Subgroup.closure_le _ |>.2 fun a ha => ?_
  simp only [genSet, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  · exact S_le_R (wordPerm_mem _)
  · exact S_le_R (wordPerm_mem _)
  · exact S_le_R (wordPerm_mem _)
  · exact S_le_R (wordPerm_mem _)
  · exact g₅_mem_R
  · exact g₆_mem_R

theorem index_of_card {G : Type*} [Group G] (H : Subgroup G) {a b c : ℕ} (hH : Nat.card H = a)
    (hG : Nat.card G = b) (hab : c * a = b) (ha : 0 < a) : H.index = c := by
  have h := H.index_mul_card
  rw [hH, hG, ← hab] at h
  exact Nat.eq_of_mul_eq_mul_right ha h

theorem pow8_of_mem_R {ρ : Equiv.Perm (Fin 42)} (hρ : ρ ∈ R)
    (h16 : ρ ^ 16 = 1) : ρ ^ 8 = 1 := by
  let x : R := ⟨ρ, hρ⟩
  have hx16 : x ^ 16 = 1 := Subtype.ext (by simpa [x] using h16)
  have hZ : IsPGroup 2 (Subgroup.zpowers x) := by
    have hd : orderOf x ∣ 2 ^ 4 := orderOf_dvd_of_pow_eq_one hx16
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hk])
  obtain ⟨Q, hQ⟩ := hZ.exists_le_sylow
  have hcP : Nat.card (P.subgroupOf R) = 256 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe P_le_R).toEquiv, card_P]
  have hidx : (P.subgroupOf R).index = 945 :=
    index_of_card _ hcP card_R (by norm_num) (by norm_num)
  have hcP' : Nat.card (P.subgroupOf R) = 2 ^ 8 := by rw [hcP]; norm_num
  let PS : Sylow 2 R := (IsPGroup.of_card hcP').toSylow (by rw [hidx]; decide)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq R PS Q
  have hxQ : x ∈ (Q : Subgroup R) := hQ (Subgroup.mem_zpowers x)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxQ
  obtain ⟨y, hy, hyx⟩ := hxQ
  have hyP : (y : Equiv.Perm (Fin 42)) ∈ P := by
    have : y ∈ (P.subgroupOf R) := by simpa [PS] using hy
    exact Subgroup.mem_subgroupOf.1 this
  have hy8 : y ^ 8 = 1 := Subtype.ext (by simpa using pow8_of_mem_P hyP)
  have hxe : x = g * y * g⁻¹ := by rw [← hyx]; rfl
  have hx8 : x ^ 8 = 1 := by rw [hxe, conj_pow, hy8, mul_one, mul_inv_cancel]
  simpa [x] using congrArg Subtype.val hx8

theorem g₄_comm_r₄ : g₄ * r₄ = r₄ * g₄ := by
  have hg : g₄T = unpack 42 6 (L34R.G 3) := L34Cert.g_eq (k := 3) (by decide)
  have c3 : Cn (L34R.G 3) := L34Cert.cnG (by decide)
  have c4 : Cn (RP 3) := L34Cert.cnRP (by decide)
  have h : (comp 42 g₄T (r₄T ()) == comp 42 (r₄T ()) g₄T) = true := by
    rw [hg, L34Cert.r4_eq, CFSG.KC.L34W.OCS.comp_eq c3 c4, CFSG.KC.L34W.OCS.comp_eq c4 c3,
      CFSG.KC.L34KSnd.beq_unpack (CFSG.KC.L34W.OCS.cn_pc c3 c4) (CFSG.KC.L34W.OCS.cn_pc c4 c3)]
    exact ch23204_g4
  exact ((tabRep_g₄.comp tabRep_r₄).beq_iff (tabRep_r₄.comp tabRep_g₄)).mp h

theorem sixteen_witness {t i : ℕ} (ht : t < 64) (hi : i < 36)
    (h2 : wordPerm (tg t) * repPerm i * (wordPerm (tg t) * repPerm i) = 1)
    (hr : wordPerm (tg t) * repPerm i * r₂ = r₂ * (wordPerm (tg t) * repPerm i))
    (hc : ∃ c ∈ R, wordPerm (tg t) * repPerm i = c * r₄ * c⁻¹) :
    ∃ x ∈ allM, betaRepM 1 x = x ∧ pow4X (mulM x (betaYM t i x)) = (0, 2, 0) := by
  obtain ⟨hrT, hy⟩ := rT_eq gensG y_k ht hi
  have hrep : TabRep (unpack 42 6 (YT (64 * i + t))) (wordPerm (tg t) * repPerm i) := by
    rw [← hrT]
    exact (tabRep_wordTab (tg t)).comp (tabRep_repTab hi)
  have c2 : Cn (L34R.G 4) := L34Cert.cnG (by decide)
  have hR2 : TabRep (unpack 42 6 (L34R.G 4)) r₂ := by rw [← L34Cert.e5]; exact tabRep_g₅
  obtain ⟨c, hcR, hce⟩ := hc
  have hρR : wordPerm (tg t) * repPerm i ∈ R := by
    rw [hce]
    exact R.mul_mem (R.mul_mem hcR r₄_mem_R) (R.inv_mem hcR)
  have hconj : IsConj (⟨wordPerm (tg t) * repPerm i, hρR⟩ : R) r₄R := by
    rw [isConj_comm, isConj_iff]
    exact ⟨⟨c, hcR⟩, Subtype.ext (by simp [hce, r₄R, mul_assoc])⟩
  obtain ⟨t', ht', hrep'⟩ := (conjClass₄.1 _).1 hconj
  have hO : (orbitR r₄T).tabs = CFSG.KC.L34K.pts 42 6 280 (L34O.T 3) := L34Cert.hO3.1
  rw [hO] at ht'
  obtain ⟨q, hq, hqe⟩ := CFSG.KC.L34Scan2.mem_pts ht'
  have hcand : candK (L34R.G 4) (L34O.T 3) (YT (64 * i + t)) = true := by
    refine candK_of hy c2 ?_ ?_ (fun q hq => L34Cert.hOc 3 (by decide) q hq) ⟨q, hq, ?_⟩
    · have h' := hR2.comp hrep
      rw [← hr] at h'
      exact (hrep.comp hR2).tab_eq h'
    · have h' := hrep.comp hrep
      rw [h2] at h'
      exact h'.tab_eq TabRep.idTab
    · rw [← hqe]
      exact hrep'.tab_eq hrep
  exact witness_of t1Of alOf bounds_k ht hi (sixK_spec ch23204_six ht hi hcand)

theorem facts23204 :
    (∀ ρ ∈ R, ρ ^ 16 = 1 → ρ ^ 8 = 1) ∧ g₄ * r₄ = r₄ * g₄ ∧
      ∀ t < 64, ∀ i < 36,
        wordPerm (tg t) * repPerm i * (wordPerm (tg t) * repPerm i) = 1 →
        wordPerm (tg t) * repPerm i * r₂ = r₂ * (wordPerm (tg t) * repPerm i) →
        (∃ c ∈ R, wordPerm (tg t) * repPerm i = c * r₄ * c⁻¹) →
        ∃ x ∈ allM, betaRepM 1 x = x ∧ pow4X (mulM x (betaYM t i x)) = (0, 2, 0) :=
  ⟨fun _ hρ h16 => pow8_of_mem_R hρ h16, g₄_comm_r₄,
    fun _ ht _ hi h2 hr hc => sixteen_witness ht hi h2 hr hc⟩

end CertificateChecks.KernelL34FU

end
