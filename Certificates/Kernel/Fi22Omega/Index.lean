module

public import Certificates.Kernel.Fi22Omega.Roots
public import CFSG.Certificates.Kernel.Fi22Omega.Count
public import CFSG.Certificates.SuborbitCoatom

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22Omega

open Equiv CFSG.KC.Fi22Omega CFSG.KC.Benes CFSG.KC.Enum CFSG.KC.I242 CFSG.KS CFSG.KS.Raw
  CFSG.KC.BfsPin CertificateChecks.KernelI242 CertificateChecks.KernelSpor
  CFSG.Monster.B.Fischer CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.Certificates CFSG.Certificates.SetOrbit
open scoped Pointwise

@[expose] noncomputable def cosW (j : Nat) : Perm (Fin 3510) :=
  wordP (fi22GenPerm 0) (fi22GenPerm 1) 128 (MS (Nat.add 10 j))

@[expose] noncomputable def blockSets (c : Nat) : Set (Set (Fin 3510)) :=
  nodeSet '' {i | i < 61776 ∧ blkF (recAt T i) = c}

theorem nodes_blk {i : Nat} (hi : i < 61776) : blkF (recAt T i) < 4 :=
  (nodeOK_sound (nodes_ok i hi)).2.2.1

theorem nodeSet_root {b : Nat} (hb : b < 4) :
    ∃ g ∈ fi22P, nodeSet (MS b) = g • ptSet 3510 fi22OmegaU0 := by
  rw [u0_eq]
  rcases b with _ | c
  · exact ⟨1, fi22P.one_mem, (one_smul _ _).symm⟩
  · exact ⟨_, wordP_mem 128 _, root_mem (c := c) (by omega)⟩

theorem hGrp_le_P :
    hGrp ≤ fi22P :=
  hGrp_le.trans i242Y_le_P

theorem node_mem
    {i : Nat} (hi : i < 61776) :
    nodeSet i ∈ MulAction.orbit fi22P (ptSet 3510 fi22OmegaU0) := by
  obtain ⟨h, hh, e⟩ := node_orbit i hi
  obtain ⟨g, hg, e'⟩ := nodeSet_root (nodes_blk hi)
  refine ⟨⟨h * g, fi22P.mul_mem (hGrp_le_P hh) hg⟩, ?_⟩
  change (h * g) • ptSet 3510 fi22OmegaU0 = nodeSet i
  rw [e, e', mul_smul]

theorem cosW_maps {j k : Nat} (hj : j < 6) (hk : k < 3)
    {x : Fin 3510} (hx : x ∈ maskSet (MS (Nat.add 7 k))) :
    cosW j x ∈ maskSet (MS (Nat.add 7 (piOf j k))) :=
  coset_maps hj hk hx

theorem piOf_lt : ∀ j < 6, ∀ k < 3, piOf j k < 3 := by decide +kernel

theorem piOf_inj : ∀ i < 6, ∀ j < 6, (∀ k < 3, piOf i k = piOf j k) → i = j := by decide +kernel

theorem cosW_fix {j : Nat} (hj : j < 6) :
    cosW j • ptSet 3510 fi22OmegaU0 = ptSet 3510 fi22OmegaU0 := by
  rw [u0_eq]
  refine smul_eq_of_maps fun x hx => ?_
  obtain ⟨k, hk, hO⟩ := mem_orb hx
  exact orb_sub (piOf_lt j hj k hk) (cosW_maps hj hk hO)

theorem i242Y_le_stabO {k : Nat} (hk : k < 3) :
    i242Y ≤ MulAction.stabilizer (Perm (Fin 3510)) (maskSet (MS (Nat.add 7 k))) := by
  rw [i242Y_eq, Subgroup.closure_le]
  rintro _ ⟨r, hr, rfl⟩
  rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
  refine smul_eq_of_maps fun x hx => ?_
  have hm := mapsOK_sound (allN_spec (allN_spec yFix r hr) k hk) x (mem_u0L (orb_sub hk hx)) hx
  have hy : ((i242y r) x : Nat) = pg 12 4095 (Y.S r) x := by
    rw [← i242_rep_y hr x, yArr_eq hr, unpack_get3510 x.2]
  rw [wordPt_one, ← hy] at hm
  exact hm

theorem cosW_inj {i j : Nat}
    (hi : i < 6) (hj : j < 6) (hd : (cosW i)⁻¹ * cosW j ∈ i242Y) : i = j := by
  refine piOf_inj i hi j hj fun k hk => ?_
  obtain ⟨x, hx⟩ := orb_nonempty hk
  have hdx : ((cosW i)⁻¹ * cosW j) x ∈ maskSet (MS (Nat.add 7 k)) := by
    have hs := MulAction.mem_stabilizer_iff.1 (i242Y_le_stabO hk hd)
    rw [← hs]
    exact Set.smul_mem_smul_set hx
  have h1 := cosW_maps hi hk hdx
  have h2 := cosW_maps hj hk hx
  have e : cosW i (((cosW i)⁻¹ * cosW j) x) = cosW j x := by simp
  rw [e] at h1
  exact orbs_disj (piOf_lt i hi k hk) (piOf_lt j hj k hk) h1 h2

@[expose] noncomputable def cosP (j : Fin 6) : fi22P := ⟨cosW j, wordP_mem 128 _⟩

theorem card_le :
    6 * Nat.card i242Y ≤ Nat.card (MulAction.stabilizer fi22P (ptSet 3510 fi22OmegaU0)) := by
  have hDM : i242Y.subgroupOf fi22P ≤ MulAction.stabilizer fi22P (ptSet 3510 fi22OmegaU0) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def]
    exact MulAction.mem_stabilizer_iff.1 (i242Y_le_stab hx)
  have h := card_mul_le_of_cosets hDM cosP (fun j => by
      rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def]
      exact cosW_fix j.2)
    (fun i j hij => by
      rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at hij
      exact Fin.ext (cosW_inj i.2 j.2 hij))
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe i242Y_le_P).toEquiv] at h

theorem nodeSet_inj {i j : Nat} (hi : i < 61776) (hj : j < 61776) (e : nodeSet i = nodeSet j) :
    i = j :=
  nodes_inj nodes_ok hi hj e

theorem orbit_index :
    MulAction.orbit fi22P (ptSet 3510 fi22OmegaU0) = nodeSet '' {i | i < 61776} ∧
      (MulAction.stabilizer fi22P (ptSet 3510 fi22OmegaU0)).index = 61776 := by
  refine orbit_eq_of_card _ nodeSet (fun i hi => node_mem hi)
    (fun i hi j hj e => nodeSet_inj hi hj e) ?_
  have h := card_le
  rw [i242_card_Y] at h
  rw [card_fi22P]
  omega

theorem index_eq :
    (MulAction.stabilizer fi22P (ptSet 3510 fi22OmegaU0)).index = 61776 :=
  orbit_index.2

theorem blockSets_ncard {c : Nat} (hc : c < 4) :
    (blockSets c).ncard = [1, 37800, 22400, 1575].getD c 0 := by
  rw [blockSets, Set.InjOn.ncard_image (fun i hi j hj e => nodeSet_inj hi.1 hj.1 e)]
  have e : {i | i < 61776 ∧ blkF (recAt T i) = c} =
      ↑((Finset.range 61776).filter fun i => blkF (recAt T i) = c) := by
    ext i
    simp
  rw [e, Set.ncard_coe_finset]
  exact cntOK_sound cnt (fun i hi => nodes_blk hi) c hc

theorem nodeSet_eq_root {i : Nat} (hi : i < 61776) :
    ∃ h ∈ hGrp, nodeSet i = h • nodeSet (MS (blkF (recAt T i))) :=
  node_orbit i hi

theorem hGrp_fix {h : Perm (Fin 3510)} (hh : h ∈ hGrp) :
    h • ptSet 3510 fi22OmegaU0 = ptSet 3510 fi22OmegaU0 :=
  MulAction.mem_stabilizer_iff.1 (i242Y_le_stab (hGrp_le hh))

theorem blockSets_zero :
    blockSets 0 = {ptSet 3510 fi22OmegaU0} := by
  have hfwd : ∀ y ∈ blockSets 0, y = ptSet 3510 fi22OmegaU0 := by
    rintro _ ⟨i, ⟨hi, hb⟩, rfl⟩
    obtain ⟨h, hh, e⟩ := nodeSet_eq_root hi
    rw [e, hb]
    change h • maskSet (rootM 0) = _
    rw [← u0_eq]
    exact hGrp_fix hh
  ext y
  rw [Set.mem_singleton_iff]
  refine ⟨hfwd y, fun hy => ?_⟩
  obtain ⟨z, hz⟩ := Set.nonempty_of_ncard_ne_zero (s := blockSets 0)
    (by rw [blockSets_ncard (by decide)]; decide)
  rw [hy, ← hfwd z hz]
  exact hz

theorem isCoatom_M0 :
    IsCoatom (MulAction.stabilizer fi22P (ptSet 3510 fi22OmegaU0)) := by
  have horb := orbit_index.1
  have hsz : ∀ c : Fin 4, (blockSets c).ncard = ![1, 37800, 22400, 1575] c := by
    intro c
    rw [blockSets_ncard c.2]
    fin_cases c <;> rfl
  refine isCoatom_stabilizer_of_suborbits (G := fi22P) (ptSet 3510 fi22OmegaU0)
    (hGrp.subgroupOf fi22P) ?_ (k := 3) (fun c : Fin 4 => blockSets c) blockSets_zero ?_ ?_ ?_ ?_
    ?_ ?_
  · intro h hh
    rw [Subgroup.mem_subgroupOf] at hh
    rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def]
    exact hGrp_fix hh
  · intro c
    rw [horb]
    rintro _ ⟨i, ⟨hi, -⟩, rfl⟩
    exact ⟨i, hi, rfl⟩
  · intro y hy
    rw [horb] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    exact ⟨⟨_, nodes_blk hi⟩, i, ⟨hi, rfl⟩, rfl⟩
  · intro c d hcd
    rw [Set.disjoint_left]
    rintro _ ⟨i, ⟨hi, hc⟩, rfl⟩ ⟨j, ⟨hj, hd⟩, e⟩
    have := nodeSet_inj hj hi e
    subst this
    exact hcd (Fin.ext (hc.symm.trans hd))
  · intro c y hy z hz
    obtain ⟨i, ⟨hi, hc⟩, rfl⟩ := hy
    obtain ⟨j, ⟨hj, hd⟩, rfl⟩ := hz
    obtain ⟨a, ha, ea⟩ := nodeSet_eq_root hi
    obtain ⟨b, hb, eb⟩ := nodeSet_eq_root hj
    rw [hc] at ea
    rw [hd] at eb
    refine ⟨⟨b * a⁻¹, hGrp_le_P (hGrp.mul_mem hb (hGrp.inv_mem ha))⟩, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact hGrp.mul_mem hb (hGrp.inv_mem ha)
    · rw [Subgroup.smul_def]
      change (b * a⁻¹) • nodeSet i = nodeSet j
      rw [ea, eb, smul_smul, inv_mul_cancel_right]
  · intro T h0 hdvd
    simp only [hsz] at hdvd
    revert T
    decide
  · refine ⟨1, by decide, ?_⟩
    rw [← Set.ncard_pos (Set.toFinite _), hsz]
    decide

end CertificateChecks.KernelFi22Omega

end
