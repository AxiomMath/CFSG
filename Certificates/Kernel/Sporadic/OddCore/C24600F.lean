module

public import Certificates.Kernel.Sporadic.OddCore.C24600K
public import Certificates.Kernel.Sporadic.OddCore.J2CnF
public import CFSG.Certificates.Kernel.ConjKeys
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Sporadic.SmallOddCore.J2
public import CFSG.Sporadic.SmallOddCore.LocalSpec
public import CFSG.Sporadic.SmallOddCore.J2CentralizerD
public import CFSG.Sporadic.Schreier.ClassSpec
public import CFSG.Sporadic.Schreier.PairJ2Order
public import CFSG.Sporadic.Schreier.PairJ2Pairs
public import CFSG.Sporadic.Schreier.PairJ2Check
public import Certificates.Certificate2280
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.C24600

open Subgroup
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.Schreier.PairNative CFSG.EvenSporadicStandard.Fin76b.Beta
open CFSG.Certificates CFSG.Certificates.Native CertificateChecks.KernelSpor

local notation "⟪" x "⟫" => tabT (unpack 315 9 x)

theorem bTbl : j2BetaTbl 7 = ⟪bK⟫ := by
  have h : natArr (j2BetaTbl 7) = unpack 315 9 (C246BT.F 7) := by
    have h := CFSG.KC.Misc.HexFlat.hexT_sound C246BT.all (by norm_num) 7 (by norm_num)
    rw [← C246BT.eq] at h
    exact h
  rw [← tabT_natArr (j2BetaTbl 7), h]
  rfl

theorem gens_rep :
    ∀ l < j2PGTbls.size, Rep 315 j2PGTbls[l]! (j2Gen l) ∧ Rep 315 j2PGInvTbls[l]! (j2Gen l)⁻¹ ∧
      j2Gen l ∈ j2P := by
  intro l hl
  have hD := j2_groupData
  have hl2 : l < 2 := hl
  have hinv : j2PGInvTbls[l]! = invT 315 j2PGTbls[l]! := by
    rw [getElem!_pos _ l (by simpa [j2PGInvTbls] using hl), getElem!_pos _ l hl]
    simp [j2PGInvTbls]
  refine ⟨hD.rep l hl, ?_, hD.mem hl⟩
  rw [hinv]
  refine rep_invT (hD.rep l hl) ?_
  rw [← hinv, (J2Cn.pgi_tabs.2 l hl2).1, (J2Cn.pg_tabs.2 l hl2).1]
  exact invOK_unpack (J2Cn.Sc hl2) (J2Cn.SIc hl2) (allN_spec J2PC.permP l (by omega))

theorem sub_facts {k cnt m : Nat}
    {G GI GJ T PL POS SRT SRI HS HSI CL : Nat → Nat} {x : Equiv.Perm (Fin 315)}
    (hx : Rep 315 ⟪bK⟫ x) (hb : cK bK = true) (hgen : subGensK k G GI GJ = true)
    (hh : penumHdK J2Cn.idK cnt 40 T PL = true)
    (hE : penumSlK 315 9 (mask 9) (315 * 9) true G GI k cnt T PL POS SRT SRI 0 cnt = true)
    (hH : slK cnt (hsortPtK 315 9 (mask 9) cnt T HS HSI) 0 cnt = true)
    (hCl : slK (Nat.mul cnt (k + k))
      (findPtK cnt T (prodQK 315 9 (mask 9) (k + k) T (bothK k GI GJ)) CL) 0
      (Nat.mul cnt (k + k)) = true)
    (hm : Nat.beq cnt m = true) :
    Nat.card (genOf 315 ((List.range k).map fun j => ⟪GI j⟫)) = m ∧
      genOf 315 ((List.range k).map fun j => ⟪GI j⟫) ≤
        j2P ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 315))) := by
  have hD := j2_groupData
  set gs := (List.range k).map fun j => ⟪GI j⟫
  have hg : ∀ j < k, G j = pidn 315 9 ∧ cK (GI j) = true ∧ cK (GJ j) = true ∧
      invEqK 315 9 (mask 9) (315 * 9) (GI j) (GJ j) = true ∧ J2Cn.sK (GI j) = true ∧
      J2Cn.commK bK (GI j) = true := by
    intro j hj
    have h := allN_spec hgen j hj
    simp only [bAnd_iff] at h
    exact ⟨Nat.eq_of_beq_eq_true h.1, h.2⟩
  have htabs : TabsOK 315 9 k GI gs.toArray := by
    refine ⟨by simp [gs], fun j hj => ⟨?_, (hg j hj).2.1⟩⟩
    rw [getElem!_pos _ j (by simpa [gs] using hj)]
    simp [gs]
  have hen : enumOK 315 40 m gs = true :=
    enumOK_of J2Cn.hn (fun j hj => (hg j hj).1) htabs
      (fun j hj => ⟨(hg j hj).2.2.2.1, (hg j hj).2.2.1⟩) hh
      (fun i hi => penumSl_spec hE i (Nat.zero_le _) (by omega) hi)
      (fun i hi => slK_spec hH i (Nat.zero_le _) (by omega) hi)
      (fun c hc => slK_spec hCl c (Nat.zero_le _) (by rw [Nat.zero_add]; exact hc) hc)
      (Nat.eq_of_beq_eq_true hm)
  have hmem : ∀ g ∈ gs, ∃ j < k, g = ⟪GI j⟫ := by
    intro g hg'
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg'
    exact ⟨j, List.mem_range.mp hj, rfl⟩
  have hperm : ∀ g ∈ gs, permOK 315 g = true := by
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
  refine mem_inf.mpr ⟨(hD.sift _ _ hrep).1 (by rw [J2Cn.sift_eq hc]; exact hs), ?_⟩
  rw [mem_centralizer_singleton_iff]
  exact ((commTT_iff hx hrep).1 (by rw [J2Cn.commF hb hc]; exact hcm)).symm

theorem countComm :
    j2CountComm = 1080 := by
  classical
  have h := k_base
  simp only [bAnd_iff] at h
  obtain ⟨cb, -, ib, bR, bG, bcnt, bhd, g8, n8, h8, g27, n27, h27, g5, n5, h5⟩ := h
  set x := tp 315 ⟪bK⟫
  have hx : Rep 315 ⟪bK⟫ x := rep_tp (permOK_unpack cb ib)
  have hpair := J2Cn.pair_of bG
  obtain ⟨-, htree, hdist⟩ := conjH_sound J2Cn.hn (TabsOK_congr hpair.1 J2Cn.pg_tabs)
    (TabsOK_congr hpair.2 J2Cn.pgi_tabs) (x := ⟪bK⟫) (by rw [Nat.eq_of_beq_eq_true bR]) bhd
    (J2Cn.pe_all' bE) (J2Cn.sl_all' bH)
  set E := (hRec 315 9 C246B.cnt C246B.T C246B.PL).1
  have hsz : E.size = 560 := by
    rw [hRec_size]
    exact Nat.eq_of_beq_eq_true bcnt
  have horb := conjTreeOK_spec j2P gens_rep hx htree
  choose! c hcP hcR using horb
  have hnd := nodup_of_hkeysDistinct (forall₂_tablePerm hcR) hdist
  have hk : ∀ i < 560, ∀ j < 560, id (c i * x * (c i)⁻¹) = id (c j * x * (c j)⁻¹) → i = j := by
    intro i hi j hj e
    have hi' : i < E.size := by omega
    have hj' : j < E.size := by omega
    have hget : ∀ l (hl : l < E.size),
        (E.toList.map (tablePerm 315))[l]'(by simpa using hl) = c l * x * (c l)⁻¹ := by
      intro l hl
      rw [List.getElem_map, Array.getElem_toList, ← getElem!_pos E l hl]
      exact tablePerm_eq (hcR l hl)
    exact (hnd.getElem_inj_iff (hi := by simpa using hi') (hj := by simpa using hj')).1
      ((hget i hi').trans (e.trans (hget j hj').symm))
  obtain ⟨c8, l8⟩ := sub_facts hx cb g8 h8 s8E s8H s8Cl n8
  obtain ⟨c27, l27⟩ := sub_facts hx cb g27 h27 s27E s27H s27Cl n27
  obtain ⟨c5, l5⟩ := sub_facts hx cb g5 h5 s5E s5H s5Cl n5
  have hgs : List.Forall₂ (CFSG.Monster.B.Co2.Rep 315) [natArr (j2BetaTbl 7)] [x] :=
    List.Forall₂.cons (by rw [bTbl]; exact co2Rep_natArr_iff.2 hx) List.Forall₂.nil
  unfold j2CountComm
  rw [show PairJ2.blocks = blocksOf 315 (rawLevels 315 j2StrongArrs PairJ2.baseArr)
    PairJ2.groups from rfl]
  refine CFSG.KC.ConjKeys.countW_eq_of_conj_keys j2ChainArrays (by norm_num)
    PairJ2.chain_check.1 j2_groups (x := x) (fun w g hw _ => ?_) (N := 560) (m := 1080)
    (by rw [← j2P_eq_original, card_j2P]) c
    (fun j hj => by rw [← j2P_eq_original]; exact hcP j (by omega)) id hk
    [genOf 315 ((List.range 2).map fun j => ⟪C246S8.GI j⟫),
      genOf 315 ((List.range 3).map fun j => ⟪C246S27.GI j⟫),
      genOf 315 ((List.range 1).map fun j => ⟪C246S5.GI j⟫)] ?_ ?_
  · rw [commW_iff hgs hw]
    simp
  · intro L hL
    rw [← j2P_eq_original]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
    rcases hL with rfl | rfl | rfl
    · exact l8
    · exact l27
    · exact l5
  · simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, c8, c27, c5]
    norm_num

theorem sqW_iff' {n : ℕ} {b : Array ℕ} {β : Equiv.Perm (Fin n)}
    (hb : CFSG.Monster.B.Co2.Rep n b β) {w : List (Array ℕ)} {g : Equiv.Perm (Fin n)}
    (hw : RepW n w g) : sqW n b w = true ↔ g * g = β := by
  rw [sqW, CFSG.Monster.B.Co2.allLt_iff]
  constructor
  · intro h
    ext x
    have h1 := h x.val x.isLt
    rw [beq_iff_eq, hw x, hb x] at h1
    have h2 := hw (g x)
    exact h2.symm.trans h1
  · intro h i hi
    rw [beq_iff_eq]
    have h2 := hw ⟨i, hi⟩
    have h3 := hw (g ⟨i, hi⟩)
    have h4 := hb ⟨i, hi⟩
    have h5 : g (g ⟨i, hi⟩) = β ⟨i, hi⟩ := by rw [← h]; rfl
    rw [show evR w i = ((g ⟨i, hi⟩ : Fin n) : ℕ) from h2, h3, h5]
    exact h4.symm

theorem countSq :
    j2CountSq = 0 := by
  classical
  have hrep17 : Rep 315 (j2CentTbl 17) (tp 315 (j2CentTbl 17)) :=
    rep_tp (J2Cn.permF (by norm_num))
  have hcount := card_eq_countW (f := sqW 315 (natArr (j2CentTbl 17)))
    (Pr := fun g => g * g = tp 315 (j2CentTbl 17)) j2ChainArrays (by norm_num)
    PairJ2.chain_check.1 j2_groups (fun w g hw _ => sqW_iff' (co2Rep_natArr_iff.2 hrep17) hw)
  unfold j2CountSq
  rw [show PairJ2.blocks = blocksOf 315 (rawLevels 315 j2StrongArrs PairJ2.baseArr)
    PairJ2.groups from rfl, ← hcount, Nat.card_eq_zero]
  left
  refine ⟨fun ⟨⟨s, hsP⟩, hs⟩ => ?_⟩
  have hs' : s * s = tp 315 (j2CentTbl 17) := hs
  obtain ⟨-, -, -, hrows, -⟩ := ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  have hC1 : genOf 315 j2C1Gens = j2P ⊓ centralizer ({tp 315 (j2CentTbl 17)} : Set _) := by
    have h := (hrows _ (List.mem_cons_of_mem _ List.mem_cons_self)).2.2.2.1
    dsimp only [CFSG.Sporadic.SmallOddCore.j2C] at h
    rw [genOf, j2C1Gens]
    exact h
  have hsC : s ∈ genOf 315 j2C1Gens := by
    rw [hC1]
    refine mem_inf.mpr ⟨by rwa [j2P_eq_original], mem_centralizer_singleton_iff.mpr ?_⟩
    rw [← hs']
    group
  obtain ⟨-, -, hcov, -⟩ := enumOK_spec (by norm_num) j2_C1Gens_perm J2Loc.c1_enum
  obtain ⟨k, hk, hkrep⟩ := hcov s hsC
  have hrec : mulClosureH 315 j2C1Gens.toArray 300 = hRec 315 9 J2C1.cnt J2C1.T J2C1.PL :=
    (mulH_sound J2Loc.hn (J2Loc.ids_of J2Loc.idv.1.2.1) J2Loc.c1_tabs J2Loc.hd.1.2.1
      (J2Loc.pe_all J2Loc.c1E) (J2Loc.sl_all J2Loc.c1H)).1
  rw [hrec, hRec_size] at hk
  rw [hrec, hRec_get hk] at hkrep
  have hcT := penumPt_canon (J2Loc.pe_all J2Loc.c1E k hk)
  have hsq : Rep 315 ⟪pcomp 315 9 (mask 9) (J2C1.T k) (J2C1.T k)⟫ (s * s) := by
    rw [← compT_unpack hcT hcT]
    exact Rep.compT hkrep hkrep
  have heq := (tblEq_iff_eq hsq hrep17).2 hs'
  rw [J2Cn.tabF (by norm_num), tblEq_unpack (CFSG.KC.BfsPin.canonK_pcomp hcT hcT) (J2Cn.Fc (by norm_num))] at heq
  have hq := k_sq
  simp only [bAnd_iff] at hq
  have hk' := allN_spec hq.2 k hk
  unfold J2Cn.pc J2Cn.F at hk'
  unfold J2Cn.F at heq
  rw [heq] at hk'
  exact Bool.false_ne_true hk'

end CertificateChecks.KernelSpor.C24600

end
