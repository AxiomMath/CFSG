module

public import Certificates.Kernel.UnitarySix.Sec3.Elt3603
public import CFSG.Certificates.Kernel.U6Sec3ChainSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.RankThree.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.UnitarySix.YamadaD

theorem coordN_L' {L : List ℕ} (hL : ∀ t ∈ L, canonK 693 10 (mask 10) (693 * 10) t = true) :
    coordNAt (unpack 693 10 (prodL 693 10 (mask 10) L)) = coordNL L := by
  have hX := prodL_canon hL
  have hka := pt1_lt _ (ptL_lt hL (by norm_num : 1 < 693))
  have hl : chA1.gens.length = 9 := rfl
  have hl1 : chK1.gens.length = 5 := rfl
  have h1 : (chA1.O.all fun s => kNA (compA 693 (unpack 693 10 (prodL 693 10 (mask 10) L)) s) ==
      (kNA (unpack 693 10 (prodL 693 10 (mask 10) L)) ^^^ kNA s)) =
      (List.range 9).all fun j => pgP (ptL 10 (mask 10) L (pg 10 (mask 10) (CA1.S j) 1)) ==
        Nat.xor (pgP (ptL 10 (mask 10) L 1)) (pgP (pg 10 (mask 10) (CA1.S j) 1)) := by
    rw [chA1_K.O_all, hl]
    refine range_all_congr fun j hj => ?_
    have hj' := PermK.canon (chA1_P j (hl ▸ hj))
    rw [kNA, CFSG.Monster.B.Co2.compA_get (by norm_num), unpack_get (by norm_num : 1 < 693),
      prodL_get hL (canon_lt hj' (by norm_num)),
      pt1_eq _ (ptL_lt hL (canon_lt hj' (by norm_num))), kNA_L hL, kNA,
      unpack_get (by norm_num : 1 < 693), pt1_eq _ (canon_lt hj' (by norm_num))]
    rfl
  have h2 : siftA 693 lvZ chZ.B 0 (unpack 693 10 (prodL 693 10 (mask 10) L)) =
      sfZ (prodL 693 10 (mask 10) L) := by
    unfold lvZ
    rw [chZ_K.sift' hX]
    rfl
  have h3 : ((List.range 5).all fun j =>
      kNA (conjA 693 chK1.O[j]! (unpack 693 10 (prodL 693 10 (mask 10) L))) ==
        bmulVec 8 8 (wedgeGensN.getD j #[]) (kNA (unpack 693 10 (prodL 693 10 (mask 10) L)))) =
      (List.range 5).all fun j =>
        pgP (pg 10 (mask 10) (CK1.S j) (ptL 10 (mask 10) L (pg 10 (mask 10) (CK1.SI j) 1))) ==
          pg 10 (mask 10) sec3WN (256 * j + pgP (ptL 10 (mask 10) L 1)) := by
    refine range_all_congr fun j hj => ?_
    have hj5 : j < chK1.gens.length := hl1 ▸ hj
    have hP := chK1_P j hj5
    rw [← chK1_K.hO j hj5, kNA, conj_get hL hP (by norm_num), pt1_eq _ (canon_lt (PermK.canon hP)
      (ptL_lt hL (canon_lt (PermK.canon_inv hP) (by norm_num)))), kNA_L hL, wN_eq j hj _ hka]
  unfold coordNAt coordNL
  rw [h1, h2, h3, kNA_L hL, strictB_eq, strictB_eq]

open CFSG.Monster.B.Co2 in
theorem coordN_k' : ∀ x ∈ chA1.grp, ∃ a, Rep 693 a x ∧ coordNAt a = true := by
  have hk : prodLazyK 693 (693 * 10) CA1.LR CA1.TR coordNL 1 0 [] = true := by
    refine coordN_all fun s hs => ?_
    interval_cases s
    exacts [kCN0, kCN1, kCN2, kCN3]
  intro x hx
  obtain ⟨L, hL, hR, hf⟩ :=
    chA1_K.forall_lazy' tabs_k (by unfold ChainData.GensOK; decide) (by decide) hk x hx
  exact ⟨_, hR, (coordN_L' hL).trans hf⟩

open CFSG.Monster.B.Co2 in
theorem coordW_k' : ∀ x ∈ chA4.grp, ∃ a, Rep 693 a x ∧ coordWAt a = true := by
  intro x hx
  obtain ⟨L, hL, hR, hf⟩ :=
    chA4_K.forall_lazy' tabs_k (by unfold ChainData.GensOK; decide) (by decide) kCW_parts.1 x hx
  exact ⟨_, hR, (coordW_L hL).trans hf⟩

open CFSG.Monster.B.Co2 in
theorem coordWPair_k' : ∀ x ∈ chA4.grp, ∀ y ∈ chA4.grp, ∃ a b, Rep 693 a x ∧ Rep 693 b y ∧
    coordWPairAt a b = true := by
  intro x hx y hy
  obtain ⟨L, hL, hR, hf⟩ :=
    chA4_K.forall_lazy' tabs_k (by unfold ChainData.GensOK; decide) (by decide) kCW_parts.2 x hx
  obtain ⟨L', hL', hR', hf'⟩ :=
    chA4_K.forall_lazy' tabs_k (by unfold ChainData.GensOK; decide) (by decide) hf y hy
  exact ⟨_, _, hR, hR', (coordWPair_L hL hL').trans hf'⟩

end CertificateChecks.KernelU6.Sec3
