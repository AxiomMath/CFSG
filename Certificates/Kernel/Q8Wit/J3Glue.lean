module

public import Certificates.Kernel.Q8Wit.J3ChecksC
public import Certificates.Kernel.Q8Wit.J3SqsK
public import Certificates.Kernel.Q8Wit.J3Free3
public import CFSG.Certificates.Kernel.Q8WitSound
public import CFSG.Certificates.Kernel.Q8WitP2Sound
public import CFSG.Certificates.Kernel.OrbRow.WordChunk
public import Certificates.Kernel.Q16J3.Glue
public import Certificates.Kernel.J3Dc.Final

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelQ8W.J3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PGrp CFSG.KC.Misc.ArrEnum
open CFSG.KC.Q8Wit CFSG.KC.E81K Certificates.TwinPerpSmSp1
open CertificateChecks.KernelSpor (J3CentP)
open CertificateChecks.KernelCensus (J3S.F)
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native
open CFSG.KS.Prim (canonK)

theorem prepPG {l : ℕ} (hl : l < 8) :
    Orb.PRep 6156 13 (J3CentP (l + 1)) (tp 6156 (j3CentTbl (l + 1))) ∧
      tp 6156 (j3CentTbl (l + 1)) ∈ j3S := by
  have hp : CFSG.Sporadic.SmallOddCore.permOK 6156 (j3CentTbl (l + 1)) = true :=
    List.all_eq_true.1 CertificateChecks.KernelSpor.OddCore.j3_permOK_all (l + 1)
      (List.mem_range.2 (by omega))
  have hr := co2Rep_natArr_iff.2 (rep_tp hp)
  rw [CertificateChecks.KernelSpor.OddCore.j3CentTbl_eq (by omega)] at hr
  refine ⟨Orb.prep_of_rep hr, ?_⟩
  have hm : j3CentTbl (l + 1) ∈ j3SylowGenTbls := by
    rw [CertificateChecks.KernelQ16J3.q16J3_tbls]
    exact List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩
  rw [j3S]
  exact Subgroup.subset_closure ⟨j3CentTbl (l + 1), List.mem_toArray.2 hm, rfl⟩

@[expose] def InS (y : ℕ) : Prop :=
  canonK 6156 13 (mask 13) (6156 * 13) y = true ∧ ∃ g ∈ j3S, Orb.PRep 6156 13 y g

theorem genS {k : ℕ} (hk : k < J3Q.ng) : InS (J3Q.G k) := by
  obtain ⟨hs, he⟩ := CFSG.KC.E81K.map_get wordsQ
  have hk' : k < j3Wit.syl.qW.size := by rw [hs]; exact hk
  have hlet := CFSG.KC.E81K.letters_of_toList lettersQ k hk'
  refine ⟨allN_spec J3Q.g k hk, ?_⟩
  refine ⟨(j3Wit.syl.qW[k]!.map fun l => tp 6156 (j3CentTbl (l + 1))).prod, ?_, ?_⟩
  · apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
    exact (prepPG (hlet l hl)).2
  · rw [← he k hk]
    exact CFSG.KC.OrbRow.posWordK_rep (by norm_num) (by norm_num) fun l hl => (prepPG (hlet l hl)).1

theorem stepS {y : ℕ} (hy : InS y) {k : ℕ} (hk : k < J3Q.ng) :
    InS (pcomp 6156 13 (mask 13) (J3Q.G k) y) := by
  obtain ⟨hc, g, hg, hp⟩ := genS hk
  obtain ⟨hyc, h, hh, hyp⟩ := hy
  exact ⟨canonK_pcomp hc hyc, g * h, Subgroup.mul_mem _ hg hh, Orb.prep_pcomp (by norm_num) hp hyp⟩

theorem ptsS :
    ∀ i < J3Q.N, ∀ k < J3Q.ng, ∃ j < J3Q.N,
      J3Q.T j = pcomp 6156 13 (mask 13) (J3Q.G k) (J3Q.T i) := by
  have h0 : InS (J3Q.T 0) := by
    rw [Nat.eq_of_beq_eq_true J3Q.t0]
    exact ⟨(PP.id hw).1, 1, Subgroup.one_mem _, Orb.prep_pidn (by norm_num) (by norm_num)⟩
  have hT := keyed_points (L := 32) (K := 8) InS h0 (fun y hy k hk => stepS hy hk) (by decide)
    (by decide) (Nat.eq_of_beq_eq_true J3Q.c0) (Nat.eq_of_beq_eq_true J3Q.cK) J3Q.ryAll
  have hc : Nat.card ↥j3S ≤ J3Q.N := by
    rw [ctuc_j3_all_involution_fixed_subgroups_odd_core_trivial.2.1]
    decide
  intro i hi k hk
  obtain ⟨hyc, g, hg, hyp⟩ := stepS (hT i hi) hk
  exact pts_closed_of_card (w := 13) (T := J3Q.T) j3S hc (fun j hj => hT j hj)
    (distinctK_inj J3Q.dist) hyc hg hyp

theorem okQ :
    bfsK 6156 13 J3Q.ng J3Q.G J3Q.N J3Q.T J3Q.E J3Q.S = true :=
  bfsK_of_keyed (L := 32) (K := 8) (C := J3Q.C) (by decide) (by norm_num) hw J3Q.g J3Q.csAll
    J3Q.t0 J3Q.dist (Nat.eq_of_beq_eq_true J3Q.c0) (Nat.eq_of_beq_eq_true J3Q.cK) J3Q.ryAll
    J3Q.keys (by decide) ptsS

theorem keysQ : keysSK 6156 13 j3Wit.syl.qKeys J3Q.N J3Q.T J3Q.SK = true := by
  rw [← j3KeysArr_toList]
  exact J3Q.keys

@[expose] noncomputable def pinQ :
    Pin 6156 13 j3Wit.syl.qKeys :=
  ⟨J3Q.ng, J3Q.N, J3Q.G, J3Q.T, J3Q.E, J3Q.S, J3Q.SK, okQ, keysQ⟩

theorem pgE : j3Wit.syl.pg.size = 8 ∧
    ∀ j < 8, j3Wit.syl.pg[j]! = unpack 6156 13 (J3CentP (j + 1)) := by
  have e : j3Wit.syl.pg = ((List.range 8).map fun i =>
      CFSG.Sporadic.SmallOddCore.Native.natArr (CFSG.Sporadic.SmallOddCore.j3CentTbl (i + 1))).toArray := by
    simp only [j3Wit, CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.Check.j3Q16,
      CertificateChecks.KernelQ16J3.q16J3_tbls, List.map_map, Function.comp_def]
  refine ⟨by rw [e]; simp, fun j hj => ?_⟩
  rw [e, getElem!_pos _ j (by simpa using hj)]
  simp only [List.getElem_toArray, List.getElem_map, List.getElem_range]
  exact CertificateChecks.KernelSpor.OddCore.j3CentTbl_eq (by omega)

theorem xgE : j3Wit.xg.size = 2 ∧ ∀ l < 2, j3Wit.xg[l]! = unpack 6156 13 (J3S.F l) := by
  have e : j3Wit.xg = #[CFSG.Sporadic.Schreier.j3StrongArrs[0]!,
      CFSG.Sporadic.Schreier.j3StrongArrs[1]!] := rfl
  have key : ∀ a b : Array ℕ, (#[a, b] : Array (Array ℕ))[0]! = a ∧
      (#[a, b] : Array (Array ℕ))[1]! = b := fun _ _ => ⟨rfl, rfl⟩
  have ks : ∀ a b : Array ℕ, (#[a, b] : Array (Array ℕ)).size = 2 := fun _ _ => rfl
  refine ⟨by rw [e, ks], fun l hl => ?_⟩
  rw [e]
  have hl2 : l < 2 := hl
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · rw [(key _ _).1]
    exact CFSG.KD.J3Dc.strong_eq (by decide)
  · rw [(key _ _).2]
    exact CFSG.KD.J3Dc.strong_eq (by decide)

theorem wordsC : j3Wit.cW.toList.map (posWordK 6156 13 J3S.F) = (List.range nc).map C := by
  have hW : ∀ c ∈ JC.W, ∀ l ∈ c, l < 2 := by
    intro c hc l hl
    have h := List.all_eq_true.1 lettersW c hc
    simpa using List.all_eq_true.1 h l hl
  rw [← eq_of_beq flatC, ← eq_of_beq chunksC, List.map_map]
  exact List.map_congr_left fun ik _ =>
    (CFSG.KC.OrbRow.posWordK_chunks hw (allN_spec permXG) hW ik).symm

theorem q8Wit_true :
    q8WitCheck j3Wit = true := by
  have hq := words hw pgE.2 (allN_spec permPG) wordsQ lettersQ
  have hc := words hw xgE.2 (allN_spec permXG) wordsC lettersC
  have hT : ∀ i < J3Q.N, PP 6156 13 (J3Q.T i) :=
    PP_pts okQ fun k hk => (hq.2 k hk).2
  have tabs : tabsK 6156 13 J3Q.N J3Q.T SQ (fun i => pinvS 6156 13 (mask 13) (J3Q.T i)) = true :=
    tabsK_of_sqs sqsJ
  have hsq : ∀ i < J3Q.N, SQ i = pcomp 6156 13 (mask 13) (J3Q.T i) (J3Q.T i) := fun i hi => by
    have e := allNP_iff.1 sqsJ i hi
    exact Nat.eq_of_beq_eq_true e
  have hC : ∀ k < nc, PP 6156 13 (C k) := fun k hk => pp_of_permB hw (hc.2 k hk).2
  have hci : ∀ k < nc, CI k = pinvS 6156 13 (mask 13) (C k) := fun k hk =>
    Nat.eq_of_beq_eq_true (allNP_iff.1 invs k hk)
  have hfree := q8WitFreeK_of_P2 hw hT
    (fun i hi => by rw [hsq i hi]; exact canonK_pcomp (hT i hi).1 (hT i hi).1)
    (fun k hk => (hC k hk).1) (fun k hk => by rw [hci k hk]; exact (PP.inv (hC k hk)).1)
    (Nat.eq_of_beq_eq_true idJ) commJ freeJ
  exact q8WitCheck_of_pins j3Wit rfl hw (fun j => J3CentP (j + 1)) pgE.1 pgE.2
    (allN_spec permPG) (by decide) lettersQ pinQ wordsQ rfl
    (by change J3Q.N ≤ j3Wit.syl.qFuel; decide) J3S.F xgE.1 xgE.2
    (allN_spec permXG) lettersC C wordsC SQ (fun i => pinvS 6156 13 (mask 13) (J3Q.T i)) CI tabs
    invs hfree

end CertificateChecks.KernelQ8W.J3

end
