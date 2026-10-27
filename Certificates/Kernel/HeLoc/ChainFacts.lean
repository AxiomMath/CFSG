module

public import Certificates.Kernel.Sporadic.RawGenOrb
public import CFSG.Certificates.Kernel.Spor.RawOrbSound
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.RankThree.Native.FiveKit
public import CFSG.RankThree.PartOne.KS.PKit
public import CFSG.Sporadic.HeldB.OuterArith
public import CFSG.Sporadic.HeldB.AutModelCore
public import CFSG.Sporadic.Schreier.PairChain
public import CFSG.Certificates.SchreierChainOrderGenerators
public import CFSG.Certificates.NativeSchreierArrays
public import CFSG.Sporadic.HeldB.OuterArithCheck
public import CFSG.RankThree.PartOne.KS.PKitLines
public import CFSG.Sporadic.He
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CertificateChecks.KernelHeLoc

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Certificates CFSG.Certificates.Native CFSG.Sporadic.HeldB CFSG.RankThree.Native
open CFSG.RankThree.PartOne

theorem eqA_of_rep {t u : Array Nat} {g : Equiv.Perm (Fin 8330)} (ht : Rep 8330 t g)
    (hu : Rep 8330 u g) : eqA 8330 t u = true := (eqA_iff ht hu).2 rfl

theorem rep_heUArr : Rep 8330 heUArr heAutU :=
  rep_hePowA rep_heAutR 5

theorem closure_three_eq :
    Subgroup.closure {heGenPerm 0, heGenPerm 1, heAutU} = heAutGroup := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · exact heP_le_heAutGroup (heGenPerm_mem (by norm_num))
    · exact heP_le_heAutGroup (heGenPerm_mem (by norm_num))
    · exact heAutU_mem_heAutGroup
  · rw [heAutGroup, sup_le_iff, heP, Subgroup.closure_le, Subgroup.zpowers_le]
    refine ⟨?_, Subgroup.subset_closure (by simp)⟩
    rintro x (rfl | rfl)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)

variable {S : Array (Array Nat)} {bs : List (Fin 8330)} {W : Array (List Int)} {D : List (List Int)}
  {kS nb BP NS : Nat} {PS PSI LR : Nat → Nat}

theorem case_chain
    (hb : Binds 8330 14 PS kS nb BP S (bs.map Fin.val).toArray)
    (hh : headK 8330 14 (mask 14) (8330 * 14) (pidn 8330 14) PS PSI kS 3 D nb BP = true)
    (ho : OrbsOK 8330 14 PS PSI LR kS nb BP NS 64) (hN : 8330 ≤ NS * 64)
    (hp : allN kS (fun j => permOK 8330 14 (mask 14) (8330 * 14) (PS j) (PSI j)) = true)
    (hW : W = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 3 kS D)
    (hprod : ((List.range nb).map fun i => rcnt (LR i)).prod = 8060774400)
    (h0 : S[0]! = heGen 0) (h1 : S[1]! = heGen 1) (h2 : Rep 8330 S[2]! heAutU) (hk : 3 ≤ kS) :
    caseChainOK3 8330 S (bs.map Fin.val).toArray W (heGen 0) (heGen 1) heUArr = true := by
  have hS : S.size = kS := hb.2.2.2.1
  have hcard : Nat.card (Subgroup.closure (Set.range fun j : Fin 3 => permOfArr 8330 S[j.val]!)) ≤
      (rawOrbitSizes 8330 S (bs.map Fin.val).toArray).prod := by
    rw [rawOrbitSizesK_orb hb hp ho hN, hprod, ← card_heAutGroup]
    apply Subgroup.card_le_of_le
    rw [Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    fin_cases j
    · change permOfArr 8330 S[0]! ∈ heAutGroup
      rw [h0]
      exact heP_le_heAutGroup (heGenPerm_mem (by norm_num))
    · change permOfArr 8330 S[1]! ∈ heAutGroup
      rw [h1]
      exact heP_le_heAutGroup (heGenPerm_mem (by norm_num))
    · change permOfArr 8330 S[2]! ∈ heAutGroup
      rw [permOfArr_eq_of_rep h2]
      exact heAutU_mem_heAutGroup
  have hc := rawChainK_of_card_orb 1 hb hh ho hN hcard
  have hk' : 3 ≤ S.size := by omega
  rw [caseChainOK3, ← hW] at *
  rw [hc, h0, h1, eqA_of_rep h2 rep_heUArr]
  have e : ∀ t : Array Nat, eqA 8330 t t = true := fun t => by
    unfold eqA
    rw [allLt_iff]
    intro i _
    exact beq_self_eq_true _
  rw [e, e]
  rfl

theorem case_sift_iff
    (hn : 1 ≤ 8330) (hk : 3 ≤ S.size) (hbs : bs.Nodup)
    (hc : caseChainOK3 8330 S (bs.map Fin.val).toArray W (heGen 0) (heGen 1) heUArr = true)
    {g : Array Nat} {G : Equiv.Perm (Fin 8330)} (hG : Rep 8330 g G) :
    siftA 8330 (rawLevels 8330 S (bs.map Fin.val).toArray) (bs.map Fin.val).toArray 0 g = true ↔
      G ∈ heAutGroup := by
  obtain ⟨hc', e0, e1, e2⟩ := caseChainOK3_parts hc
  have hA : ChainArrays (RawSchreierDatum.ofArrays 8330 hn S 3 hk bs hbs W) (S.extract 0 3) S
      (bs.map Fin.val).toArray W := chainArrays_ofArrays (chainCheckFacts hc').strong_inv
  rw [siftA_iff_mem_originalSubgroup hA (by norm_num) hc' hG,
    originalSubgroup_ofArrays_three hc' (rep_heGen (by norm_num)) (rep_heGen (by norm_num))
      rep_heUArr e0 e1 e2, closure_three_eq]

theorem case_faithful
    (hn : 1 ≤ 8330) (hk : 3 ≤ S.size) (hbs : bs.Nodup)
    (hc : caseChainOK3 8330 S (bs.map Fin.val).toArray W (heGen 0) (heGen 1) heUArr = true) :
    CFSG.Sporadic.Schreier.BaseFaithful heAutGroup (bs.map Fin.val) ∧
      ∀ j < S.size, permOfArr 8330 S[j]! ∈ heAutGroup := by
  obtain ⟨hc', e0, e1, e2⟩ := caseChainOK3_parts hc
  have hA : ChainArrays (RawSchreierDatum.ofArrays 8330 hn S 3 hk bs hbs W) (S.extract 0 3) S
      (bs.map Fin.val).toArray W := chainArrays_ofArrays (chainCheckFacts hc').strong_inv
  have hQ := (validSchreier_of_chainOK hA (by norm_num) hc').1
  have horig : (RawSchreierDatum.ofArrays 8330 hn S 3 hk bs hbs W).originalSubgroup = heAutGroup := by
    rw [originalSubgroup_ofArrays_three hc' (rep_heGen (by norm_num)) (rep_heGen (by norm_num))
      rep_heUArr e0 e1 e2, closure_three_eq]
  refine ⟨?_, fun j hj => ?_⟩
  · have h := CFSG.Sporadic.Schreier.baseFaithful_of_valid hQ
    rwa [horig, RawSchreierDatum.ofArrays_base_toList] at h
  · have h := RawSchreierDatum.strong_get_mem_originalSubgroup _ hQ ⟨j, hj⟩
    rwa [RawSchreierDatum.ofArrays_strong_get, horig] at h

end CertificateChecks.KernelHeLoc

end
