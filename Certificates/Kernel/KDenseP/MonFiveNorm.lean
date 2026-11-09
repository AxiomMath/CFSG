module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveRel
public import CFSG.Certificates.Kernel.Common.PcCollect
public import CFSG.Certificates.Kernel.KDenseP.MonFive.Pairs
public import Certificates.Kernel.KDenseP.AgreeOf
import CFSG.Certificates.Kernel.Common.Harness

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.KernelKDenseP.MonFive

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive CFSG.KC.PcCollect CFSG.KC.KDenseP.MonFive

set_option maxRecDepth 100000

@[expose] noncomputable def x5 (k : ℕ) : Gmat := gw fiveGens[k]!

@[expose] noncomputable def n5 (j : ℕ) : Gmat := gw fiveNW[j]!

@[expose] def cF (k m : ℕ) : List ℕ := nfFrom 0 (fiveCw[k * 9 + m]!).toList

@[expose] def pF (k : ℕ) : List ℕ := nfFrom 0 (fivePw[k]!).toList

@[expose] def rF (j k : ℕ) : List ℕ := nfFrom 0 ((fiveNImg[j]!)[k]!).toList

@[expose] def T5 : ℕ :=
  1355165710006884966607884924572290649238449192755248285952306222756834275245554526241996645261473448498176226471941707028801238269452501444932090414883616828750020458179056684339816284171232282787311666082902230809882194866756773579580863461824579143058503124105064889824728342588897166585357671204239012046655562160549058789517598363092846339921839575314849294740317281465933556062528345990602954521236002555337871808917628011367205663355962461050640496006004073858534741219900261767022784119410173420400993367928197091626931567080208558544832363531486543034371803910715401508943477166442438374026744576087199412682163313181556712581761979179050570120897662724363746461962640550206663982116846977311308068080642504056688109080404720627728445259097597608186092907678555832313361884081503272082544751226637041030588095581850971965021664248623832165173971137906993397919994227260215481076883847187417246706231001414441265062301602061671290742624678686453762648850716589776241701912275091782283226544905267240472601695060903812051811896003214232973132143086772562545143869848153881144111817013956697350998860239181185832304024555570737528744447128950271403840305612536397621174223802293501367202529172669578619086721541835568886802897853112328079380122120800770482358132221385167221385773964208496611312332036523545519223258442057863459772967100348171561860206492887710658658115048857806319132937253258360401158659766811947268091957190032336192436907183663037496028634591367871711780217367806284223377696993851468472588248848818358469364096487639001664353072648397782909385076395493660842130968016430958124673401513173996397569771902635739552964261069031035929421638099018040165427776751460617117237159774677436148083246642524878536316905097184163219265940524392917306282729765804507137463575877164892180910882969260222508190324889979926166980701079426556257957973704521710009965285928639371565658665045459374421171503753873352551262914109028697727272603542244253718023326194164567574368584464839917551977795228360912933298275343322996525161502405750304014336

@[expose] def P5 : ℕ :=
  2758566162421655706332013262798848

theorem getElem!_toList (v : Array ℕ) (k : ℕ) : v[k]! = v.toList.getD k 0 := by
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList]
  by_cases h : k < v.size
  · rw [getElem!_pos v k h, Array.getElem?_eq_getElem h, Option.getD_some]
  · rw [getElem!_neg v k h, Array.getElem?_eq_none (by omega), Option.getD_none]
    rfl

theorem prod_range_nfFrom (x : ℕ → Gmat) :
    ∀ (u : List ℕ) (i : ℕ), ((List.range u.length).map fun k => x (i + k) ^ u.getD k 0).prod =
      evW x (nfFrom i u)
  | [], _ => rfl
  | a :: u, i => by
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.prod_cons,
      nfFrom_cons, evW_append, evW_replicate, ← prod_range_nfFrom x u (i + 1)]
    congr 2
    simp only [List.map_inj_left, List.mem_range, Function.comp_apply, List.getD_cons_succ]
    intro k _
    rw [Nat.add_assoc, Nat.add_comm 1 k]

theorem gw_rhsW_ev (hp : agreeAll powEqs = true) (v : Array ℕ) (hv : v.size = 9) :
    gw (rhsW v) = evW x5 (nfFrom 0 v.toList) := by
  rw [gw_rhsW hp, ← prod_range_nfFrom x5 v.toList 0, Array.length_toList, hv]
  congr 1
  apply List.map_congr_left
  intro k _
  rw [getElem!_toList, Nat.zero_add]
  rfl

theorem powEqs_ok (hrel : agreeAll relEqs = true) : agreeAll powEqs = true := by
  unfold relEqs at hrel
  simp only [agreeAll, List.all_append, Bool.and_eq_true] at hrel ⊢
  exact hrel.1.1

theorem cw_size : ∀ i < 81, (fiveCw[i]!).size = 9 := by decide +kernel

theorem pw_size : ∀ i < 9, (fivePw[i]!).size = 9 := by decide +kernel

theorem nimg_size : ∀ j < 3, ∀ i < 9, ((fiveNImg[j]!)[i]!).size = 9 := by decide +kernel

theorem hC5 (hrel : agreeAll relEqs = true) :
    ∀ k m, k < m → m < 9 → x5 k * x5 m = evW x5 (cF k m) * x5 k := by
  intro k m hkm hm
  have hmem : (fiveGens[m]! ++ fiveGens[k]!, fiveGens[k]! ++ rhsW fiveCw[k * 9 + m]!) ∈ relEqs := by
    unfold relEqs cwEqs
    refine List.mem_append_right _ (List.mem_flatMap.2 ⟨k, List.mem_range.2 (by omega),
      List.mem_map.2 ⟨m, List.mem_filter.2 ⟨List.mem_range.2 hm, by simpa using hkm⟩, rfl⟩⟩)
  have e := agreeAll_sound hrel _ hmem
  simp only [gw_append] at e
  have hc : cF k m = nfFrom 0 (fiveCw[k * 9 + m]!).toList := rfl
  rw [hc, ← gw_rhsW_ev (powEqs_ok hrel) _ (cw_size _ (by omega))]
  exact e

theorem pwEqs_ok (hrel : agreeAll relEqs = true) : agreeAll pwEqs = true := by
  unfold relEqs at hrel
  simp only [agreeAll, List.all_append, Bool.and_eq_true] at hrel ⊢
  exact hrel.1.2

theorem hPw (hpow : agreeAll powEqs = true) (hpw : agreeAll pwEqs = true) :
    ∀ k < 9, x5 k ^ 5 = evW x5 (pF k) := by
  intro k hk
  have hmem : (repW 5 fiveGens[k]!, rhsW fivePw[k]!) ∈ pwEqs :=
    List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩
  have e := agreeAll_sound hpw _ hmem
  rw [gw_repW] at e
  have hc : pF k = nfFrom 0 (fivePw[k]!).toList := rfl
  rw [hc, ← gw_rhsW_ev hpow _ (pw_size k hk)]
  exact e

theorem hP5 (hrel : agreeAll relEqs = true) : ∀ k < 9, x5 k ^ 5 = evW x5 (pF k) :=
  hPw (powEqs_ok hrel) (pwEqs_ok hrel)

theorem cF_lt : ∀ k < 9, ∀ m < 9, k < m → ∀ l ∈ cF k m, k < l ∧ l < 9 := by decide +kernel

theorem dT_lt : ∀ k < 9, ∀ j < 9, k < j → ∀ l ∈ dT T5 9 k j, k < l ∧ l < 9 := by decide +kernel

theorem pT_eq : ∀ k < 9, pT P5 k = pF k := by decide +kernel

theorem pF_lt : ∀ k < 9, ∀ l ∈ pF k, k < l ∧ l < 9 := by decide +kernel

theorem rF_lt : ∀ j < 3, ∀ k < 9, ∀ l ∈ rF j k, l < 9 := by decide +kernel

theorem dchk : ∀ k < 9, ∀ j < 9, k < j →
    colE 9 T5 P5 ((dT T5 9 k j).flatMap (cF k)) [j] = true := by decide +kernel

theorem hD5 (hrel : agreeAll relEqs = true) :
    ∀ k j, k < j → j < 9 → x5 j * x5 k = x5 k * evW x5 (dT T5 9 k j) :=
  fun k j hkj hj => conjD_of_checks x5 9 T5 P5 0 cF (fun k m _ h1 h2 => hC5 hrel k m h1 h2)
    (fun k m _ h1 h2 => cF_lt k (by omega) m h2 h1) (fun k j _ h1 h2 => dT_lt k (by omega) j h2 h1)
    (fun k _ hk => by rw [pT_eq k hk]; exact hP5 hrel k hk)
    (fun k _ hk => by rw [pT_eq k hk]; exact pF_lt k hk)
    (fun k j _ h1 h2 => dchk k (by omega) j h2 h1) k j (Nat.zero_le _) hkj hj

theorem col5 (hrel : agreeAll relEqs = true) {l l' : List ℕ} (hl : ∀ j ∈ l, j < 9)
    (hl' : ∀ j ∈ l', j < 9) (h : colE 9 T5 P5 l l' = true) : evW x5 l = evW x5 l' :=
  colE_sound x5 9 T5 P5 0 (fun k j _ h1 h2 => hD5 hrel k j h1 h2)
    (fun k j _ h1 h2 => dT_lt k (by omega) j h2 h1)
    (fun k _ hk => by rw [pT_eq k hk]; exact hP5 hrel k hk)
    (fun k _ hk => by rw [pT_eq k hk]; exact pF_lt k hk) (fun j hj => ⟨Nat.zero_le _, hl j hj⟩)
    (fun j hj => ⟨Nat.zero_le _, hl' j hj⟩) h

theorem flat_lt {j : ℕ} (hj : j < 3) :
    ∀ l : List ℕ, (∀ m ∈ l, m < 9) → ∀ a ∈ l.flatMap (rF j), a < 9 := by
  intro l hl a ha
  obtain ⟨m, hm, ha'⟩ := List.mem_flatMap.1 ha
  exact rF_lt j hj m (hl m hm) a ha'

theorem norm_of_pick (hrel : agreeAll relEqs = true) {j : ℕ} {l : List ℕ} (hj : j < 3)
    (hl : ∀ i ∈ l, i < 9) (hN : agreeAll (normPick j l) = true) :
    ∀ i ∈ l, n5 j * x5 i = evW x5 (rF j i) * n5 j := by
  intro i hi
  have e := agreeAll_sound hN _ (List.mem_map.2 ⟨i, hi, rfl⟩)
  simp only [gw_append] at e
  have hc : rF j i = nfFrom 0 ((fiveNImg[j]!)[i]!).toList := rfl
  rw [hc, ← gw_rhsW_ev (powEqs_ok hrel) _ (nimg_size j hj i (hl i hi))]
  exact e

theorem rel_cw (hrel : agreeAll relEqs = true) (a b : ℕ) (hab : a < b) (hb : b < 9) :
    evW x5 [a, b] = evW x5 (cF a b ++ [a]) := by
  rw [evW_append, evW_cons, evW_cons, evW_cons, evW_nil, mul_one, mul_one, hC5 hrel a b hab hb]

theorem step5 (hrel : agreeAll relEqs = true) (j k e e' : ℕ) (lw L1 L2 : List ℕ) (hj : j < 3)
    (hk : k < 9) (hrelw : evW x5 lw = evW x5 (L1 ++ List.replicate e k ++ L2))
    (hK : ∀ m ∈ lw ++ L1 ++ L2, n5 j * x5 m = evW x5 (rF j m) * n5 j)
    (hlet : ∀ m ∈ lw ++ L1 ++ L2, m < 9)
    (hc : colE 9 T5 P5 (lw.flatMap (rF j))
      (L1.flatMap (rF j) ++ (List.replicate e k).flatMap (rF j) ++ L2.flatMap (rF j)) = true)
    (hc5 : colE 9 T5 P5 ((List.replicate 5 k).flatMap (rF j)) [] = true)
    (hpk : pF k = []) (hee : (e * e') % 5 = 1) :
    n5 j * x5 k = evW x5 (rF j k) * n5 j := by
  have hl1 : ∀ m ∈ lw, m < 9 := fun m hm => hlet m (by simp [hm])
  have hl2 : ∀ m ∈ L1, m < 9 := fun m hm => hlet m (by simp [hm])
  have hl3 : ∀ m ∈ L2, m < 9 := fun m hm => hlet m (by simp [hm])
  have hl4 : ∀ m ∈ List.replicate e k, m < 9 := fun m hm => by
    rw [(List.mem_replicate.1 hm).2]
    exact hk
  refine image_of_rel x5 k e e' lw L1 L2 hrelw hK (col5 hrel (flat_lt hj lw hl1) ?_ hc)
    (by rw [hP5 hrel k hk, hpk]; rfl) ?_ hee
  · intro a ha
    simp only [List.mem_append] at ha
    rcases ha with (ha | ha) | ha
    · exact flat_lt hj L1 hl2 a ha
    · exact flat_lt hj _ hl4 a ha
    · exact flat_lt hj L2 hl3 a ha
  · rw [← evW_flatMap_replicate x5 5 k]
    exact col5 hrel (flat_lt hj _ fun m hm => by rw [(List.mem_replicate.1 hm).2]; exact hk)
      (by simp) hc5

theorem forall_mem_cons' {P : ℕ → Prop} {a : ℕ} {l : List ℕ} (ha : P a) (hl : ∀ m ∈ l, P m) :
    ∀ m ∈ a :: l, P m :=
  List.forall_mem_cons.2 ⟨ha, hl⟩

theorem norm_all_0 (hrel : agreeAll relEqs = true)
    (hN : agreeAll (normPick 0 [0, 1, 4, 6]) = true) :
    ∀ m < 9, n5 0 * x5 m = evW x5 (rF 0 m) * n5 0 := by
  have K0 := norm_of_pick hrel (j := 0) (l := [0, 1, 4, 6]) (by norm_num) (by decide) hN
  have h8 := step5 hrel 0 8 1 1 [4, 6] [6] [4] (by norm_num) (by norm_num)
    ((rel_cw hrel 4 6 (by norm_num) (by norm_num)).trans
      (congrArg (evW x5) (by decide +kernel : cF 4 6 ++ [4] = [6] ++ List.replicate 1 8 ++ [4])))
    (fun m hm => K0 m (by revert m hm; decide))
    (by decide)
    (by quickRfl) (by quickRfl) (by decide +kernel) (by norm_num)
  have K1 := forall_mem_cons' (P := fun m => n5 0 * x5 m = evW x5 (rF 0 m) * n5 0) h8 K0
  have h5 := step5 hrel 0 5 4 4 [0, 4] [4, 4] [6, 6, 6, 6, 8, 8, 0] (by norm_num) (by norm_num)
    ((rel_cw hrel 0 4 (by norm_num) (by norm_num)).trans
      (congrArg (evW x5) (by decide +kernel : cF 0 4 ++ [0] = [4, 4] ++ List.replicate 4 5 ++ [6, 6, 6, 6, 8, 8, 0])))
    (fun m hm => K1 m (by revert m hm; decide))
    (by decide)
    (by quickRfl) (by quickRfl) (by decide +kernel) (by norm_num)
  have K2 := forall_mem_cons' (P := fun m => n5 0 * x5 m = evW x5 (rF 0 m) * n5 0) h5 K1
  have h2 := step5 hrel 0 2 2 3 [1, 5] [] [6, 6, 8, 1] (by norm_num) (by norm_num)
    ((rel_cw hrel 1 5 (by norm_num) (by norm_num)).trans
      (congrArg (evW x5) (by decide +kernel : cF 1 5 ++ [1] = [] ++ List.replicate 2 2 ++ [6, 6, 8, 1])))
    (fun m hm => K2 m (by revert m hm; decide))
    (by decide)
    (by quickRfl) (by quickRfl) (by decide +kernel) (by norm_num)
  have K3 := forall_mem_cons' (P := fun m => n5 0 * x5 m = evW x5 (rF 0 m) * n5 0) h2 K2
  have h3 := step5 hrel 0 3 4 4 [1, 6] [] [4, 4, 4, 4, 5, 6, 6, 6, 1] (by norm_num) (by norm_num)
    ((rel_cw hrel 1 6 (by norm_num) (by norm_num)).trans
      (congrArg (evW x5) (by decide +kernel : cF 1 6 ++ [1] = [] ++ List.replicate 4 3 ++ [4, 4, 4, 4, 5, 6, 6, 6, 1])))
    (fun m hm => K3 m (by revert m hm; decide))
    (by decide)
    (by quickRfl) (by quickRfl) (by decide +kernel) (by norm_num)
  have K4 := forall_mem_cons' (P := fun m => n5 0 * x5 m = evW x5 (rF 0 m) * n5 0) h3 K3
  have h7 := step5 hrel 0 7 1 1 [1, 2] [3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 6] [8, 8, 8, 8, 1] (by norm_num) (by norm_num)
    ((rel_cw hrel 1 2 (by norm_num) (by norm_num)).trans
      (congrArg (evW x5) (by decide +kernel : cF 1 2 ++ [1] = [3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 6] ++ List.replicate 1 7 ++ [8, 8, 8, 8, 1])))
    (fun m hm => K4 m (by revert m hm; decide))
    (by decide)
    (by quickRfl) (by quickRfl) (by decide +kernel) (by norm_num)
  have K5 := forall_mem_cons' (P := fun m => n5 0 * x5 m = evW x5 (rF 0 m) * n5 0) h7 K4
  intro m hm
  exact K5 m (by revert m hm; decide)

theorem norm_all_1 (hrel : agreeAll relEqs = true)
    (hN : agreeAll (normPick 1 [0, 1, 4, 6]) = true) :
    ∀ m < 9, n5 1 * x5 m = evW x5 (rF 1 m) * n5 1 := by
  have K0 := norm_of_pick hrel (j := 1) (l := [0, 1, 4, 6]) (by norm_num) (by decide) hN
  have h8 := step5 hrel 1 8 1 1 [4, 6] [6] [4] (by norm_num) (by norm_num)
    ((rel_cw hrel 4 6 (by norm_num) (by norm_num)).trans
      (congrArg (evW x5) (by decide +kernel : cF 4 6 ++ [4] = [6] ++ List.replicate 1 8 ++ [4])))
    (fun m hm => K0 m (by revert m hm; decide))
    (by decide)
    (by quickRfl) (by quickRfl) (by decide +kernel) (by norm_num)
  have K1 := forall_mem_cons' (P := fun m => n5 1 * x5 m = evW x5 (rF 1 m) * n5 1) h8 K0
  have h5 := step5 hrel 1 5 4 4 [0, 4] [4, 4] [6, 6, 6, 6, 8, 8, 0] (by norm_num) (by norm_num)
    ((rel_cw hrel 0 4 (by norm_num) (by norm_num)).trans
      (congrArg (evW x5) (by decide +kernel : cF 0 4 ++ [0] = [4, 4] ++ List.replicate 4 5 ++ [6, 6, 6, 6, 8, 8, 0])))
    (fun m hm => K1 m (by revert m hm; decide))
    (by decide)
    (by quickRfl) (by quickRfl) (by decide +kernel) (by norm_num)
  have K2 := forall_mem_cons' (P := fun m => n5 1 * x5 m = evW x5 (rF 1 m) * n5 1) h5 K1
  have h2 := step5 hrel 1 2 2 3 [1, 5] [] [6, 6, 8, 1] (by norm_num) (by norm_num)
    ((rel_cw hrel 1 5 (by norm_num) (by norm_num)).trans
      (congrArg (evW x5) (by decide +kernel : cF 1 5 ++ [1] = [] ++ List.replicate 2 2 ++ [6, 6, 8, 1])))
    (fun m hm => K2 m (by revert m hm; decide))
    (by decide)
    (by quickRfl) (by quickRfl) (by decide +kernel) (by norm_num)
  have K3 := forall_mem_cons' (P := fun m => n5 1 * x5 m = evW x5 (rF 1 m) * n5 1) h2 K2
  have h3 := step5 hrel 1 3 4 4 [1, 6] [] [4, 4, 4, 4, 5, 6, 6, 6, 1] (by norm_num) (by norm_num)
    ((rel_cw hrel 1 6 (by norm_num) (by norm_num)).trans
      (congrArg (evW x5) (by decide +kernel : cF 1 6 ++ [1] = [] ++ List.replicate 4 3 ++ [4, 4, 4, 4, 5, 6, 6, 6, 1])))
    (fun m hm => K3 m (by revert m hm; decide))
    (by decide)
    (by quickRfl) (by quickRfl) (by decide +kernel) (by norm_num)
  have K4 := forall_mem_cons' (P := fun m => n5 1 * x5 m = evW x5 (rF 1 m) * n5 1) h3 K3
  have h7 := step5 hrel 1 7 4 4 [1, 3] [2, 2, 2, 3, 3, 3, 4, 4, 4, 5] [8, 8, 8, 8, 1] (by norm_num) (by norm_num)
    ((rel_cw hrel 1 3 (by norm_num) (by norm_num)).trans
      (congrArg (evW x5) (by decide +kernel : cF 1 3 ++ [1] = [2, 2, 2, 3, 3, 3, 4, 4, 4, 5] ++ List.replicate 4 7 ++ [8, 8, 8, 8, 1])))
    (fun m hm => K4 m (by revert m hm; decide))
    (by decide)
    (by quickRfl) (by quickRfl) (by decide +kernel) (by norm_num)
  have K5 := forall_mem_cons' (P := fun m => n5 1 * x5 m = evW x5 (rF 1 m) * n5 1) h7 K4
  intro m hm
  exact K5 m (by revert m hm; decide)

theorem norm_all_2 (hrel : agreeAll relEqs = true)
    (hN : agreeAll (normPick 2 [0, 1, 4, 6]) = true) :
    ∀ m < 9, n5 2 * x5 m = evW x5 (rF 2 m) * n5 2 := by
  have K0 := norm_of_pick hrel (j := 2) (l := [0, 1, 4, 6]) (by norm_num) (by decide) hN
  have h8 := step5 hrel 2 8 1 1 [4, 6] [6] [4] (by norm_num) (by norm_num)
    ((rel_cw hrel 4 6 (by norm_num) (by norm_num)).trans
      (congrArg (evW x5) (by decide +kernel : cF 4 6 ++ [4] = [6] ++ List.replicate 1 8 ++ [4])))
    (fun m hm => K0 m (by revert m hm; decide))
    (by decide)
    (by quickRfl) (by quickRfl) (by decide +kernel) (by norm_num)
  have K1 := forall_mem_cons' (P := fun m => n5 2 * x5 m = evW x5 (rF 2 m) * n5 2) h8 K0
  have h5 := step5 hrel 2 5 4 4 [0, 4] [4, 4] [6, 6, 6, 6, 8, 8, 0] (by norm_num) (by norm_num)
    ((rel_cw hrel 0 4 (by norm_num) (by norm_num)).trans
      (congrArg (evW x5) (by decide +kernel : cF 0 4 ++ [0] = [4, 4] ++ List.replicate 4 5 ++ [6, 6, 6, 6, 8, 8, 0])))
    (fun m hm => K1 m (by revert m hm; decide))
    (by decide)
    (by quickRfl) (by quickRfl) (by decide +kernel) (by norm_num)
  have K2 := forall_mem_cons' (P := fun m => n5 2 * x5 m = evW x5 (rF 2 m) * n5 2) h5 K1
  have h2 := step5 hrel 2 2 2 3 [1, 5] [] [6, 6, 8, 1] (by norm_num) (by norm_num)
    ((rel_cw hrel 1 5 (by norm_num) (by norm_num)).trans
      (congrArg (evW x5) (by decide +kernel : cF 1 5 ++ [1] = [] ++ List.replicate 2 2 ++ [6, 6, 8, 1])))
    (fun m hm => K2 m (by revert m hm; decide))
    (by decide)
    (by quickRfl) (by quickRfl) (by decide +kernel) (by norm_num)
  have K3 := forall_mem_cons' (P := fun m => n5 2 * x5 m = evW x5 (rF 2 m) * n5 2) h2 K2
  have h3 := step5 hrel 2 3 4 4 [0, 6] [2, 2, 2] [4, 4, 4, 4, 5, 5, 5, 6, 6, 6, 8, 0] (by norm_num) (by norm_num)
    ((rel_cw hrel 0 6 (by norm_num) (by norm_num)).trans
      (congrArg (evW x5) (by decide +kernel : cF 0 6 ++ [0] = [2, 2, 2] ++ List.replicate 4 3 ++ [4, 4, 4, 4, 5, 5, 5, 6, 6, 6, 8, 0])))
    (fun m hm => K3 m (by revert m hm; decide))
    (by decide)
    (by quickRfl) (by quickRfl) (by decide +kernel) (by norm_num)
  have K4 := forall_mem_cons' (P := fun m => n5 2 * x5 m = evW x5 (rF 2 m) * n5 2) h3 K3
  have h7 := step5 hrel 2 7 1 1 [0, 5] [3, 3, 3, 4, 5, 5, 5, 5, 6, 6, 6] [8, 8, 8, 8, 0] (by norm_num) (by norm_num)
    ((rel_cw hrel 0 5 (by norm_num) (by norm_num)).trans
      (congrArg (evW x5) (by decide +kernel : cF 0 5 ++ [0] = [3, 3, 3, 4, 5, 5, 5, 5, 6, 6, 6] ++ List.replicate 1 7 ++ [8, 8, 8, 8, 0])))
    (fun m hm => K4 m (by revert m hm; decide))
    (by decide)
    (by quickRfl) (by quickRfl) (by decide +kernel) (by norm_num)
  have K5 := forall_mem_cons' (P := fun m => n5 2 * x5 m = evW x5 (rF 2 m) * n5 2) h7 K4
  intro m hm
  exact K5 m (by revert m hm; decide)

theorem norm_all (hrel : agreeAll relEqs = true) (h0 : agreeAll (normPick 0 [0, 1, 4, 6]) = true)
    (h1 : agreeAll (normPick 1 [0, 1, 4, 6]) = true) (h2 : agreeAll (normPick 2 [0, 1, 4, 6]) = true) :
    ∀ j < 3, ∀ m < 9, n5 j * x5 m = evW x5 (rF j m) * n5 j := by
  intro j hj
  interval_cases j
  · exact norm_all_0 hrel h0
  · exact norm_all_1 hrel h1
  · exact norm_all_2 hrel h2

theorem valid_of_agree {w₁ w₂ : List Native.Gen} (h : agree w₁ w₂ = true) :
    (∀ g ∈ w₁, g.validB = true) ∧ ∀ g ∈ w₂, g.validB = true := by
  unfold agree at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2⟩

theorem agree_of_mem {ps : List (List Native.Gen × List Native.Gen)} (h : agreeAll ps = true)
    {p : List Native.Gen × List Native.Gen} (hp : p ∈ ps) : agree p.1 p.2 = true :=
  List.all_eq_true.1 h p hp

theorem gens_valid (hpw : agreeAll pwEqs = true) : ∀ k < 9, ∀ g ∈ fiveGens[k]!, g.validB = true := by
  intro k hk g hg
  have hmem : (repW 5 fiveGens[k]!, rhsW fivePw[k]!) ∈ pwEqs :=
    List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩
  refine (valid_of_agree (agree_of_mem hpw hmem)).1 g ?_
  unfold repW
  rw [List.mem_flatten]
  exact ⟨_, List.mem_replicate.2 ⟨by norm_num, rfl⟩, hg⟩

theorem powW_valid (hpow : agreeAll powEqs = true) (hpw : agreeAll pwEqs = true) :
    ∀ k < 9, ∀ e, ∀ g ∈ powW k e, g.validB = true := by
  intro k hk e g hg
  unfold powW at hg
  split_ifs at hg with hs
  · obtain ⟨h2, h4, hne⟩ := hs
    have hmem : ((fivePowW[k]!)[e]!, repW e fiveGens[k]!) ∈ powEqs := by
      unfold powEqs
      refine List.mem_flatMap.2
        ⟨k, List.mem_range.2 hk, List.mem_filterMap.2 ⟨e, List.mem_range'_1.2 ⟨h2, by omega⟩, ?_⟩⟩
      simp [hne]
    exact (valid_of_agree (agree_of_mem hpow hmem)).1 g hg
  · unfold repW at hg
    obtain ⟨w, hw, hgw⟩ := List.mem_flatten.1 hg
    rw [(List.mem_replicate.1 hw).2] at hgw
    exact gens_valid hpw k hk g hgw

theorem rhsW_valid (hpow : agreeAll powEqs = true) (hpw : agreeAll pwEqs = true) (v : Array ℕ) :
    ∀ g ∈ rhsW v, g.validB = true := by
  intro g hg
  unfold rhsW at hg
  obtain ⟨k, hk, hg'⟩ := List.mem_flatMap.1 hg
  exact powW_valid hpow hpw k (List.mem_range.1 (List.mem_reverse.1 hk)) _ g hg'

theorem nw_valid {j : ℕ} (h : agreeAll (normPick j [0, 1, 4, 6]) = true) :
    ∀ g ∈ fiveNW[j]!, g.validB = true := fun g hg =>
  (valid_of_agree (agree_of_mem h (List.mem_cons_self ..))).1 g (List.mem_append_right _ hg)

theorem normEqs_ok (hrel : agreeAll relEqs = true) (h0 : agreeAll (normPick 0 [0, 1, 4, 6]) = true)
    (h1 : agreeAll (normPick 1 [0, 1, 4, 6]) = true) (h2 : agreeAll (normPick 2 [0, 1, 4, 6]) = true) :
    ∀ p ∈ normEqs, ((∀ g ∈ p.1, g.validB = true) ∧ ∀ g ∈ p.2, g.validB = true) ∧ gw p.1 = gw p.2 := by
  intro p hp
  unfold normEqs at hp
  obtain ⟨j, hj, hp⟩ := List.mem_flatMap.1 hp
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hp
  rw [List.mem_range] at hj hi
  have hnw : ∀ g ∈ fiveNW[j]!, g.validB = true := by
    interval_cases j
    · exact nw_valid h0
    · exact nw_valid h1
    · exact nw_valid h2
  refine ⟨⟨fun g hg => ?_, fun g hg => ?_⟩, ?_⟩
  · rcases List.mem_append.1 hg with hg | hg
    · exact gens_valid (pwEqs_ok hrel) i hi g hg
    · exact hnw g hg
  · rcases List.mem_append.1 hg with hg | hg
    · exact hnw g hg
    · exact rhsW_valid (powEqs_ok hrel) (pwEqs_ok hrel) _ g hg
  · simp only [gw_append]
    rw [gw_rhsW_ev (powEqs_ok hrel) _ (nimg_size j hj i hi)]
    exact norm_all hrel h0 h1 h2 j hj i hi

theorem normSub_ok (hrel : agreeAll relEqs = true) (h0 : agreeAll (normPick 0 [0, 1, 4, 6]) = true)
    (h1 : agreeAll (normPick 1 [0, 1, 4, 6]) = true) (h2 : agreeAll (normPick 2 [0, 1, 4, 6]) = true)
    {ps : List (List Native.Gen × List Native.Gen)} (hps : ∀ p ∈ ps, p ∈ normEqs) : agreeAll ps = true :=
  CertificateChecks.KernelKDenseP.agreeAll_of_wordLin
    (fun p hp => (normEqs_ok hrel h0 h1 h2 p (hps p hp)).1)
    (fun p hp => congrArg Subtype.val (normEqs_ok hrel h0 h1 h2 p (hps p hp)).2)

end CertificateChecks.KernelKDenseP.MonFive

end
