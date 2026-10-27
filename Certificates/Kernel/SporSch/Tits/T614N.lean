module

public import CFSG.Sporadic.Schreier.TitsAbel
public import CFSG.Sporadic.Schreier.TitsCentral
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ExcTitsGroup
public import CFSG.Certificates.Kernel.Spor.RawTreeDefs
public import CFSG.Sporadic.Schreier.TitsInvCheckInputs

public section

namespace CertificateChecks.KernelSporSch.T614

open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Certificates CFSG.Certificates.Native CFSG.Certificates.ChainArrays

theorem prodH_rep {a b c d e : ℕ} (ha : a < titsHLevels[0]!.pts.size)
    (hb : b < titsHLevels[1]!.pts.size) (hc : c < titsHLevels[2]!.pts.size)
    (hd : d < titsHLevels[3]!.pts.size) (he : e < titsHLevels[4]!.pts.size) :
    ∃ g ∈ titsH, Rep 1755 (prod5 1755 titsHLevels a b c d e) g := by
  have hA := titsH_chainArrays
  have hF := chainCheckFacts titsLocalChains_check.1
  have hQ := titsQH_facts.1
  have h5 : titsQH.baseCount = 5 := by
    show (finList 1755 titsHBase).length = 5
    simp [finList, titsHBase]
  have hm : ∀ i, i < 5 → ∀ {k : ℕ},
      k < (lev 1755 titsHArrs (baseArr 1755 titsHBase) i).pts.size →
      levT 1755 titsHArrs (baseArr 1755 titsHBase) i k ∈ titsH := fun i hi k hk => by
    rw [← titsQH_facts.2.2.1, ← titsQH.levelSubgroup_zero_eq_original hQ]
    exact titsQH.levelSubgroup_antitone 0 i (Nat.zero_le _) (hA.levT_mem hF (by omega) hk)
  have hr : ∀ i, i < 5 → ∀ {k : ℕ},
      k < (lev 1755 titsHArrs (baseArr 1755 titsHBase) i).pts.size →
      Rep 1755 (lev 1755 titsHArrs (baseArr 1755 titsHBase) i).tr[k]!
        (levT 1755 titsHArrs (baseArr 1755 titsHBase) i k) :=
    fun i hi k hk => hA.rep_levT hF (by omega) hk
  refine ⟨levT 1755 titsHArrs (baseArr 1755 titsHBase) 0 a *
      levT 1755 titsHArrs (baseArr 1755 titsHBase) 1 b *
      levT 1755 titsHArrs (baseArr 1755 titsHBase) 2 c *
      levT 1755 titsHArrs (baseArr 1755 titsHBase) 3 d *
      levT 1755 titsHArrs (baseArr 1755 titsHBase) 4 e, ?_, ?_⟩
  · exact mul_mem (mul_mem (mul_mem (mul_mem (hm 0 (by norm_num) ha) (hm 1 (by norm_num) hb))
      (hm 2 (by norm_num) hc)) (hm 3 (by norm_num) hd)) (hm 4 (by norm_num) he)
  · exact rep_compA (rep_compA (rep_compA (rep_compA (hr 0 (by norm_num) ha)
      (hr 1 (by norm_num) hb)) (hr 2 (by norm_num) hc)) (hr 3 (by norm_num) hd))
      (hr 4 (by norm_num) he)

theorem mem_normalizer_of_gens {g : Equiv.Perm (Fin 1755)}
    (h : ∀ i < 3, g * titsSGen i * g⁻¹ ∈ titsS) :
    g ∈ Subgroup.normalizer (titsS : Set (Equiv.Perm (Fin 1755))) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : titsS.map (MulAut.conj g).toMonoidHom ≤ titsS := by
    rw [Subgroup.map_le_iff_le_comap]
    conv_lhs => rw [titsS_eq_closure]
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    simpa [MulAut.conj_apply] using h i i.2
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem nhs_check_k : all5 1755 titsHLevels (fun a =>
    !(allLt 3 fun i => inS (conjArr a titsSArrs[i]!)) || inS a) = true := by
  unfold all5
  refine allLt_iff.2 fun a ha => allLt_iff.2 fun b hb => allLt_iff.2 fun c hc =>
    allLt_iff.2 fun d hd => allLt_iff.2 fun e he => ?_
  obtain ⟨g, hgH, hrep⟩ := prodH_rep ha hb hc hd he
  cases h : allLt 3 (fun i => inS (conjArr (prod5 1755 titsHLevels a b c d e) titsSArrs[i]!))
  · simp only [h, Bool.not_false, Bool.true_or]
  · have hconj : ∀ i < 3, g * titsSGen i * g⁻¹ ∈ titsS := fun i hi =>
      (mem_titsS_iff_sift (a := conjArr (prod5 1755 titsHLevels a b c d e) titsSArrs[i]!)
        (rep_compA (rep_compA hrep (titsSGen_rep hi)) (CFSG.KS.Raw.rep_invCand hrep))).1
        (allLt_spec h hi)
    have hgS := mem_titsS_of_normalizes_D (titsH_le_titsD hgH) (mem_normalizer_of_gens hconj)
    simp only [(mem_titsS_iff_sift hrep).2 hgS, Bool.or_true]

end CertificateChecks.KernelSporSch.T614

end
