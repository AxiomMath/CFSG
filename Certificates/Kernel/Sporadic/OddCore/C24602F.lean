module

public import Certificates.Kernel.Sporadic.OddCore.C24602K
public import Certificates.Kernel.Sporadic.OddCore.J3BetaA5F
public import Certificates.Kernel.Sporadic.OddCore.MulHGlue
public import Certificates.Kernel.SporSch.J3K426.Sift
public import Certificates.Kernel.SporSch.PairJ3.Check2237
public import CFSG.Certificates.Kernel.Spor.ConjRunSound
public import CFSG.Certificates.Kernel.Spor.MulHFSound
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.Certificates.Kernel.ConjKeys
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ3
public import CFSG.Sporadic.SmallOddCore.J3
public import CFSG.Sporadic.SmallOddCore.J2CentralizerD
public import CFSG.Sporadic.SmallOddCore.LocalSpec
public import CFSG.Sporadic.Schreier.PairJ3Order
public import CFSG.Sporadic.Schreier.PairJ3Pairs
public import CFSG.Sporadic.Schreier.PairJ3Check
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Misc.RuInvHash
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.Monster.Code.Weights

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.C24602

open Subgroup
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.Schreier.PairNative CFSG.EvenSporadicStandard.Fin76b.Beta
open CFSG.Certificates CFSG.Certificates.Native CertificateChecks.KernelSpor
open CertificateChecks.KernelSporSch

local notation "⟪" x "⟫" => tabT (unpack 6156 13 x)

theorem hn : szOK 6156 13 = true := J3BetaA5.base.1

theorem bTbl : j3BetaTbl 7 = ⟪bK⟫ := J3BetaA5.beta_tab (by norm_num)

theorem c2462hsF_eq (cnt : Nat) (T HS HSI : Nat → Nat) :
    hsortPtKF 6156 13 (mask 13) cnt T HS HSI = hsortPtK 6156 13 (mask 13) cnt T HS HSI :=
  funext (hsortPtKF_eq 6156 13 cnt T HS HSI)

theorem s8H : slK C2462S8.cnt (hsortPtK 6156 13 (mask 13) C2462S8.cnt C2462S8.T C2462S8.HS
    C2462S8.HSI) 0 C2462S8.cnt = true := by
  rw [← c2462hsF_eq]
  exact s8HF

theorem s27H : slK C2462S27.cnt (hsortPtK 6156 13 (mask 13) C2462S27.cnt C2462S27.T C2462S27.HS
    C2462S27.HSI) 0 C2462S27.cnt = true := by
  rw [← c2462hsF_eq]
  exact s27HF

theorem s5H : slK C2462S5.cnt (hsortPtK 6156 13 (mask 13) C2462S5.cnt C2462S5.T C2462S5.HS
    C2462S5.HSI) 0 C2462S5.cnt = true := by
  rw [← c2462hsF_eq]
  exact s5HF

theorem gens_rep : CFSG.KS.ConjRun.GensRep 6156 13 (mask 13) 5 PJ3.S PJ3.SI PJ3Check.g := by
  unfold CFSG.KS.ConjRun.GensRep
  intro l hl p hp
  obtain ⟨h1, h2⟩ := PJ3Check.rep_g l hl
  refine ⟨?_, ?_⟩
  · rw [← CFSG.KS.Raw.Orb.unpack_get hp]
    exact h1 ⟨p, hp⟩
  · rw [← CFSG.KS.Raw.Orb.unpack_get hp]
    exact h2 ⟨p, hp⟩

theorem gens_mem :
    ∀ l < 5, PJ3Check.g l ∈ j3P := by
  intro l hl
  have h : PJ3Check.g l = j3StrongPerm l := by
    unfold PJ3Check.g j3StrongPerm
    rw [PJ3Check.arr_eq l hl]
  rw [h]
  exact CFSG.ComponentClassification.RankTwoSporadic.J3.j3StrongPerm_mem hl

theorem runs : ∀ s < 12, c24602run s = true := by
  intro s hs
  interval_cases s
  exacts [c24602run0, c24602run1, c24602run2, c24602run3, c24602run4, c24602run5, c24602run6,
    c24602run7, c24602run8, c24602run9, c24602run10, c24602run11]

theorem sub_facts {k cnt m : Nat}
    {G GI GJ T PL POS SRT SRI HS HSI CL : Nat → Nat} {ws : List (List Int)}
    {x : Equiv.Perm (Fin 6156)}
    (hx : Rep 6156 ⟪bK⟫ x) (hb : cK bK = true) (hgen : subGensK k G GI GJ ws = true)
    (hh : penumHdK (pidn 6156 13) cnt 40 T PL = true)
    (hE : penumSlK 6156 13 (mask 13) (6156 * 13) true G GI k cnt T PL POS SRT SRI 0 cnt = true)
    (hH : slK cnt (hsortPtK 6156 13 (mask 13) cnt T HS HSI) 0 cnt = true)
    (hCl : slK (Nat.mul cnt (k + k))
      (findPtK cnt T (prodQK 6156 13 (mask 13) (k + k) T (bothK k GI GJ)) CL) 0
      (Nat.mul cnt (k + k)) = true)
    (hm : Nat.beq cnt m = true) :
    Nat.card (genOf 6156 ((List.range k).map fun j => ⟪GI j⟫)) = m ∧
      genOf 6156 ((List.range k).map fun j => ⟪GI j⟫) ≤
        j3P ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 6156))) := by
  have hD := j3_groupData
  set gs := (List.range k).map fun j => ⟪GI j⟫
  have hg : ∀ j < k, G j = pidn 6156 13 ∧ cK (GI j) = true ∧ cK (GJ j) = true ∧
      invEqK 6156 13 (mask 13) (6156 * 13) (GI j) (GJ j) = true ∧
      wordEqK 6156 13 (mask 13) (pidn 6156 13) PJ3.S PJ3.SI 5 (ws.getD j []) (GI j) = true ∧
      Nat.beq (pc bK (GI j)) (pc (GI j) bK) = true := by
    intro j hj
    have h := allN_spec hgen j hj
    simp only [bAnd_iff] at h
    exact ⟨Nat.eq_of_beq_eq_true h.1, h.2⟩
  have htabs : TabsOK 6156 13 k GI gs.toArray := by
    refine ⟨by simp [gs], fun j hj => ⟨?_, (hg j hj).2.1⟩⟩
    rw [getElem!_pos _ j (by simpa [gs] using hj)]
    simp [gs]
  have hen : enumOK 6156 40 m gs = true :=
    enumOK_of hn (fun j hj => (hg j hj).1) htabs
      (fun j hj => ⟨(hg j hj).2.2.2.1, (hg j hj).2.2.1⟩) hh
      (fun i hi => penumSl_spec hE i (Nat.zero_le _) (by omega) hi)
      (fun i hi => slK_spec hH i (Nat.zero_le _) (by omega) hi)
      (fun c hc => slK_spec hCl c (Nat.zero_le _) (by rw [Nat.zero_add]; exact hc) hc)
      (Nat.eq_of_beq_eq_true hm)
  have hmem : ∀ g ∈ gs, ∃ j < k, g = ⟪GI j⟫ := by
    intro g hg'
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg'
    exact ⟨j, List.mem_range.mp hj, rfl⟩
  have hperm : ∀ g ∈ gs, permOK 6156 g = true := by
    intro g hg'
    obtain ⟨j, hj, rfl⟩ := hmem g hg'
    exact permOK_unpack (hg j hj).2.1 (hg j hj).2.2.2.1
  refine ⟨(enumOK_spec (by norm_num) hperm hen).1, ?_⟩
  rw [closure_le]
  rintro _ ⟨g, hg', rfl⟩
  have hg'' : g ∈ gs := by simpa using hg'
  obtain ⟨j, hj, rfl⟩ := hmem g hg''
  have hrep := rep_tp (hperm _ hg'')
  obtain ⟨-, hc, -, -, hs, hcm⟩ := hg j hj
  refine mem_inf.mpr ⟨(hD.sift _ _ hrep).1 ?_, ?_⟩
  · unfold CFSG.Sporadic.SmallOddCore.j3Sift
    rw [natArr_tabT hc]
    exact J3KT.sift_of hs
  · rw [mem_centralizer_singleton_iff]
    exact ((commTT_iff hx hrep).1 (by rw [commTT_unpack hb hc]; exact hcm)).symm

theorem countComm :
    j3CountComm = 1080 := by
  classical
  have h := k_base
  simp only [bAnd_iff] at h
  obtain ⟨cb, -, ib, hN, -, g8, n8, h8, g27, n27, h27, g5, n5, h5⟩ := h
  set x := tp 6156 ⟪bK⟫
  have hx : Rep 6156 ⟪bK⟫ x := rep_tp (permOK_unpack cb ib)
  have hxc : CFSG.Monster.B.Co2.Rep 6156 (unpack 6156 13 bK) x := by
    have h' := co2Rep_natArr_iff.2 hx
    rwa [natArr_tabT cb] at h'
  have hB : ∀ p (hp : p < 6156), pg 13 (mask 13) bK p = (x ⟨p, hp⟩ : Nat) := by
    intro p hp
    rw [← CFSG.KS.Raw.Orb.unpack_get hp]
    exact hxc ⟨p, hp⟩
  have hNv : C24602D.N = 46512 := Nat.eq_of_beq_eq_true hN
  have hnext := CFSG.KS.ConjRun.nextK_of_runs (C := 12) (L := 4096) runs
    (by rw [hNv]; norm_num)
  have hk := CFSG.KS.ConjRun.conj_keys_of_next gens_rep hB (r := 4) (by norm_num) hnext
  rw [hNv] at hk
  obtain ⟨c8, l8⟩ := sub_facts hx cb g8 h8 s8E s8H s8Cl n8
  obtain ⟨c27, l27⟩ := sub_facts hx cb g27 h27 s27E s27H s27Cl n27
  obtain ⟨c5, l5⟩ := sub_facts hx cb g5 h5 s5E s5H s5Cl n5
  have hgs : List.Forall₂ (CFSG.Monster.B.Co2.Rep 6156) [natArr (j3BetaTbl 7)] [x] :=
    List.Forall₂.cons (by rw [bTbl]; exact co2Rep_natArr_iff.2 hx) List.Forall₂.nil
  unfold j3CountComm
  rw [PairJ3.parCount_eq, show PairJ3.blocks = blocksOf 6156
    (rawLevels 6156 j3StrongArrs PairJ3.baseArr) PairJ3.groups from rfl]
  refine CFSG.KC.ConjKeys.countW_eq_of_conj_keys j3ChainArrays (by norm_num)
    PairJ3.chain_check.1 j3_groups (x := x) (fun w g hw _ => ?_) (N := 46512) (m := 1080)
    (by rw [← j3P_eq_original, card_j3P])
    (CFSG.KS.ConjRun.cW 5 C24602D.root C2462PL PJ3Check.g 8)
    (fun j _ => by
      rw [← j3P_eq_original]
      exact CFSG.KS.ConjRun.cW_mem gens_mem 8 j)
    (CFSG.KS.ConjRun.keyP 13 4) hk
    [genOf 6156 ((List.range 2).map fun j => ⟪C2462S8.GI j⟫),
      genOf 6156 ((List.range 3).map fun j => ⟪C2462S27.GI j⟫),
      genOf 6156 ((List.range 1).map fun j => ⟪C2462S5.GI j⟫)] ?_ ?_
  · rw [commW_iff hgs hw]
    simp
  · intro L hL
    rw [← j3P_eq_original]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
    rcases hL with rfl | rfl | rfl
    · exact l8
    · exact l27
    · exact l5
  · simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, c8, c27, c5]
    norm_num

end CertificateChecks.KernelSpor.C24602

end
