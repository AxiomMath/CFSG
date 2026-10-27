module

public import Certificates.Kernel.HN25550.Elems
public import Certificates.Kernel.HN25550.E0
public import Certificates.Kernel.HN25550.E1
public import Certificates.Kernel.HN25550.Neg
public import Certificates.Kernel.Sporadic.OddCore.HN2092
public import Certificates.Certificate2092
public import CFSG.Certificates.Kernel.Spor.PNodeSound
public import CFSG.Certificates.Kernel.Spor.PEnumSound
public import CFSG.Certificates.Kernel.Spor.BaseMaskGlue
public import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourEnumSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.SylowReduce
public import CFSG.Sporadic.HNOddCore.SixD
public import CFSG.Sporadic.HNOddCore.SylA
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Spor.BaseMaskSound

set_option maxRecDepth 400000

#kqb_all CFSG.KD.HN25550.EP CFSG.KD.HN25550.ckE 32

public section

namespace CertificateChecks.KernelHN25550

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.PNode CFSG.KS.WordRegs
open CFSG.KD.HN25550 CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNSchreier CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CertificateChecks.KernelSpor CFSG.KC.HNMult

theorem hd_parts : EP.cnt = 1024 ∧ EP.k = 4 ∧ penumHdK (pidn 1100 11) EP.cnt 1024 EP.T EP.PL = true ∧
    genK 0 [11] = true ∧ genK 1 [3] = true ∧ genK 2 [6, 2] = true ∧
    genK 3 [2, 11, 2, 11, 6] = true := by
  obtain ⟨h1, h2, -, h4, h5, h6, h7, h8⟩ := (by simpa only [bAnd_iff] using hd_ok :
    Nat.beq EP.cnt 1024 = true ∧ Nat.beq EP.k 4 = true ∧ Nat.beq CNT 1024 = true ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, h4, h5, h6, h7, h8⟩

theorem cnt_eq : EP.cnt = 1024 := hd_parts.1

theorem pWI_get {j : ℕ} (hj : j < 4) : genK j (pWI.getD j []) = true ∧
    plettersOK 12 (pWI.getD j []) = true := by
  obtain ⟨-, -, -, h0, h1, h2, h3⟩ := hd_parts
  interval_cases j
  · exact ⟨h0, by decide⟩
  · exact ⟨h1, by decide⟩
  · exact ⟨h2, by decide⟩
  · exact ⟨h3, by decide⟩

theorem pWI_eq (j : ℕ) : pWI.getD j [] = (PW.getD j []).map fun s => ((s + 1 : ℕ) : ℤ) := by
  rw [pw_ok.1]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases PW[j]? <;> rfl

@[expose] noncomputable def gensP : Array Tab := Array.ofFn (n := 4) fun j => unpack 1100 11 (EP.G j.val)

theorem gensP_get {j : ℕ} (hj : j < 4) : gensP[j]! = unpack 1100 11 (EP.G j) := by
  unfold gensP
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem gensOK : GensOK 1100 11 4 EP.G gensP :=
  ⟨by simp [gensP], fun j hj => ⟨gensP_get hj, allN_spec gcan j hj⟩⟩

theorem ptP : ∀ i < EP.cnt, penumPtK 1100 11 (mask 11) (1100 * 11) false EP.G EP.G 4 EP.cnt EP.T
    EP.PL EP.POS EP.SRT EP.SRI i = true := by
  intro i hi
  have hi' : i < 1024 := cnt_eq ▸ hi
  have hs : i / 32 < 32 := by omega
  exact CFSG.KS.BaseMask.penumSl_spec (EP.all (i / 32) hs) (by change i / 32 * 32 ≤ i; omega)
    (by change i < i / 32 * 32 + 32; omega) hi

theorem encP : enumBFS 1100 gensP 1024 = penumRec 1100 11 EP.cnt EP.T EP.PL ∧
    enumOK 1100 gensP (penumRec 1100 11 EP.cnt EP.T EP.PL) = true :=
  penumK_left_sound (by decide) gensOK hd_parts.2.2.1 ptP

noncomputable abbrev EPr : Enum := penumRec 1100 11 EP.cnt EP.T EP.PL

theorem EPr_size : EPr.tabs.size = 1024 := by simp [EPr, penumRec, cnt_eq]

theorem EPr_tab {i : ℕ} (hi : i < 1024) : EPr.tabs[i]! = unpack 1100 11 (EP.T i) := by
  have hi' : i < EP.cnt := by rw [cnt_eq]; exact hi
  simp only [EPr, penumRec]
  rw [getElem!_pos _ i (by simpa using hi'), Array.getElem_ofFn]

theorem EPr_par {i : ℕ} (hi : i < 1024) : EPr.par[i]! = parOf EP.PL i := by
  have hi' : i < EP.cnt := by rw [cnt_eq]; exact hi
  simp only [EPr, penumRec]
  rw [getElem!_pos _ i (by simpa using hi'), Array.getElem_ofFn]

theorem EPr_lab {i : ℕ} (hi : i < 1024) : EPr.lab[i]! = labOf EP.PL i := by
  have hi' : i < EP.cnt := by rw [cnt_eq]; exact hi
  simp only [EPr, penumRec]
  rw [getElem!_pos _ i (by simpa using hi'), Array.getElem_ofFn]

theorem tree_parts : unpack 1100 11 (EP.T 0) = idTab 1100 ∧ ∀ i < 1024, 0 < i →
    parOf EP.PL i < i ∧ labOf EP.PL i < 4 ∧
    unpack 1100 11 (EP.T i) = comp 1100 (unpack 1100 11 (EP.G (labOf EP.PL i)))
      (unpack 1100 11 (EP.T (parOf EP.PL i))) := by
  have h := encP.2
  unfold enumOK at h
  obtain ⟨-, h0, -, -, htree⟩ := treeOK_spec h
  have hs : gensP.size = 4 := by simp [gensP]
  refine ⟨by rw [← EPr_tab (by norm_num)]; exact h0, fun i hi hi0 => ?_⟩
  obtain ⟨h1, h2, h3⟩ := htree i (by rw [EPr_size]; exact hi) hi0
  rw [EPr_par hi] at h1
  rw [EPr_lab hi, hs] at h2
  refine ⟨h1, h2, ?_⟩
  rw [← EPr_tab hi, h3, EPr_lab hi, EPr_par hi, EPr_tab (i := parOf EP.PL i) (by omega), leftStep,
    gensP_get h2]

theorem pathK_fuel : ∀ i < 1024, ∀ f, i ≤ f → pathK EP.PL f i = pathK EP.PL i i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi f hf
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · cases f <;> rfl
    · obtain ⟨hp, -, -⟩ := tree_parts.2 i hi hi0
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      rw [pathK_succ, pathK_succ, ih _ hp (by omega) f' (by omega), ih _ hp (by omega) i' (by omega)]

theorem pathK_cons {i : ℕ} (hi : i < 1024) (hi0 : 0 < i) :
    pathK EP.PL i i = labOf EP.PL i :: pathK EP.PL (parOf EP.PL i) (parOf EP.PL i) := by
  obtain ⟨hp, -, -⟩ := tree_parts.2 i hi hi0
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  rw [pathK_succ, if_neg (by omega), pathK_fuel _ (by omega) i' (by omega)]

theorem pathK_lt : ∀ i < 1024, ∀ j ∈ pathK EP.PL i i, j < 4 := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi j hj
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact absurd hj (by simp [pathK_zero])
    · obtain ⟨hp, hl, -⟩ := tree_parts.2 i hi hi0
      rw [pathK_cons hi hi0] at hj
      rcases List.mem_cons.1 hj with rfl | hj
      · exact hl
      · exact ih _ hp (by omega) j hj


@[expose] noncomputable def nodeEl (i : ℕ) : C6 := ((pathK EP.PL i i).map pgen).prod

theorem nodeEl_zero : nodeEl 0 = 1 := rfl

theorem nodeEl_cons {i : ℕ} (hi : i < 1024) (hi0 : 0 < i) :
    nodeEl i = pgen (labOf EP.PL i) * nodeEl (parOf EP.PL i) := by
  rw [nodeEl, pathK_cons hi hi0, List.map_cons, List.prod_cons]
  rfl

theorem node_coe {i : ℕ} (hi : i < 1024) :
    ((nodeEl i : C6) : JH) = wordEl rEl (pathCodes EP.PL PR i) := by
  rw [pathCodes_eq, nodeEl]
  change C6.subtype ((pathK EP.PL i i).map pgen).prod = _
  rw [map_list_prod, List.map_map, wordEl, List.map_map]
  congr 1
  refine List.map_congr_left fun j hj => ?_
  simp only [Function.comp_apply, Subgroup.coe_subtype]
  rw [pgen_eq (pathK_lt i hi j hj), codeEl_odd]

theorem node_codes {i : ℕ} (hi : i < 1024) : ∀ c ∈ pathCodes EP.PL PR i, c / 2 < 46 := by
  intro c hc
  rw [pathCodes_eq] at hc
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hc
  obtain ⟨-, -, h⟩ := pr_parts
  have := (h j (pathK_lt i hi j hj)).2
  omega

theorem phi6_g6F (s : ℕ) : phi6 (g6F s) = om0Perm s := by
  unfold g6F om0Perm
  split_ifs
  · rfl
  · exact map_one _

theorem wordVal_succ {G : Type*} [Group G] (g : ℕ → G) (l : List ℕ) :
    wordVal g (l.map fun s => ((s + 1 : ℕ) : ℤ)) = (l.map g).prod := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    rw [List.map_cons, wordVal_cons, ih, List.map_cons, List.prod_cons, if_pos (by omega)]
    congr 2

theorem tab_gen {j : ℕ} (hj : j < 4) : TabRep gensP[j]! (phi6 (pgen j)) := by
  obtain ⟨hg, hp⟩ := pWI_get hj
  have hx := HN2092.x_get hg
  have hw := prep_pword_wordVal (fun h hh => prep_om0 hh) (fun h hh => prep_om0_inv hh) _ hp
  rw [hx, pWI_eq, wordVal_succ] at hw
  have e : phi6 (pgen j) = ((PW.getD j []).map om0Perm).prod := by
    rw [pgen, map_list_prod, List.map_map]
    congr 1
    exact List.map_congr_left fun s _ => phi6_g6F s
  rw [gensP_get hj, e]
  exact ⟨by simp [unpack], fun i => hw i⟩

theorem tab_node : ∀ i < 1024, TabRep (unpack 1100 11 (EP.T i)) (phi6 (nodeEl i)) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [tree_parts.1, nodeEl_zero, map_one]
      exact TabRep.idTab
    · obtain ⟨hp, hl, he⟩ := tree_parts.2 i hi hi0
      rw [he, nodeEl_cons hi hi0, map_mul]
      have hg := tab_gen hl
      rw [gensP_get hl] at hg
      exact hg.comp (ih _ hp (by omega))

noncomputable abbrev Hs : Subgroup (Equiv.Perm (Fin 1100)) :=
  Subgroup.closure (Set.range fun j : Fin 4 => phi6 (pgen j))

theorem enum_H : Enumerates Hs EPr.tabs.toList := by
  have hs : gensP.size = 4 := by simp [gensP]
  refine enumerates_closure (gens := gensP) ?_ ?_ encP.2
  · rintro _ ⟨j, rfl⟩
    exact ⟨j, by rw [hs]; exact j.2, tab_gen j.2⟩
  · intro j hj
    rw [hs] at hj
    exact ⟨_, ⟨⟨j, hj⟩, rfl⟩, tab_gen hj⟩

theorem card_H : Nat.card Hs = 1024 := by
  rw [enum_H.card, Array.length_toList, EPr_size]

theorem H_le : Hs ≤ phi6.range := by
  rw [Subgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  exact ⟨_, rfl⟩

theorem mem_mul_iff (x y : C6) : phi6 (x * y) ∈ Dsub ↔ (phi6 x ∈ Dsub ↔ phi6 y ∈ Dsub) := by
  have h := Subgroup.mul_mem_iff_of_index_two index_Dr (a := ⟨phi6 x, x, rfl⟩)
    (b := ⟨phi6 y, y, rfl⟩)
  simpa [Subgroup.mem_subgroupOf, map_mul] using h

theorem prod_mem_iff {α : Type*} (x : α → C6) (b : α → ℕ) :
    ∀ l : List α, (∀ a ∈ l, (phi6 (x a) ∈ Dsub ↔ b a % 2 = 0)) →
      (phi6 (l.map x).prod ∈ Dsub ↔ (l.map b).sum % 2 = 0)
  | [], _ => by simp [Subgroup.one_mem]
  | a :: l, h => by
    rw [List.map_cons, List.prod_cons, mem_mul_iff, h a List.mem_cons_self,
      prod_mem_iff x b l fun a' ha' => h a' (List.mem_cons_of_mem _ ha'), List.map_cons,
      List.sum_cons]
    omega

theorem sift_mem {G : ℕ} (hG : canonK 1100 11 (mask 11) (1100 * 11) G = true) (h : inD G = true)
    {g : Equiv.Perm (Fin 1100)} (hp : PRep 1100 (unpack 1100 11 G) g) : g ∈ Dsub := by
  refine (mem_Dsub_iff hp).1 ?_
  rw [lvArr_eq, aArr_eq, bArr_eq, HN2092.a_eq, HN2092.b_eq, HN2092.sift_eq hG]
  exact h

theorem sifts : inD (HSG 1) = true ∧ inD (HSG 2) = true ∧
    inD (CFSG.KC.Enum.pcomp 1100 11 (mask 11) (HSG 10) (sGI 5)) = true := by
  simpa only [bAnd_iff] using sift_ok

theorem om0_mem {s : ℕ} (hs : s < 12) (h : inD (HSG s) = true) : om0Perm s ∈ Dsub := by
  have hp := prep_om0 hs
  rw [HN2092.g_get.2 s hs] at hp
  exact sift_mem (allN_spec HN2092.gC s hs) h hp

theorem om0_ten : om0Perm 10 * (om0Perm 5)⁻¹ ∈ Dsub := by
  have hp := prep_pcomp (prep_om0 (s := 10) (by norm_num))
    (prep_inv_of_pisInv (prep_om0 (s := 5) (by norm_num)) (six_parts.2.1 5 (by norm_num)))
  rw [HN2092.g_inv 5 (by norm_num), HN2092.g_get.2 10 (by norm_num),
    HN2092.pcomp_k (allN_spec HN2092.gC 10 (by norm_num)) (allN_spec HN2092.gCI 5 (by norm_num))]
    at hp
  exact sift_mem (CFSG.KC.BfsPin.canonK_pcomp (allN_spec HN2092.gC 10 (by norm_num))
    (allN_spec HN2092.gCI 5 (by norm_num))) sifts.2.2 hp

theorem letter_mem_iff {s : ℕ} (hs : s ∈ G6S) : phi6 (g6F s) ∈ Dsub ↔ SG.getD s 0 % 2 = 0 := by
  have hSG := pw_ok.2.2.2.2.1
  rw [pw_ok.2.2.1] at hSG hs
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hSG
  obtain ⟨e1, e2, e5, e10, -⟩ := hSG
  rw [phi6_g6F]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · rw [e1]
    exact iff_of_true (om0_mem (by norm_num) sifts.1) rfl
  · rw [e2]
    exact iff_of_true (om0_mem (by norm_num) sifts.2.1) rfl
  · rw [e5]
    exact iff_of_false om0Perm_five_not_mem (by norm_num)
  · rw [e10]
    refine iff_of_false (fun h => om0Perm_five_not_mem ?_) (by norm_num)
    have h2 := Dsub.mul_mem (Dsub.inv_mem om0_ten) h
    rwa [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one] at h2

theorem pgen_mem_iff {j : ℕ} : phi6 (pgen j) ∈ Dsub ↔ PP.getD j 0 % 2 = 0 := by
  rw [pgen, prod_mem_iff g6F (fun s => SG.getD s 0) _ fun s hs => letter_mem_iff (pw_letters s hs),
    pw_ok.2.2.2.2.2]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases PW[j]? with
  | none => simp
  | some w => simp [Nat.mod_mod]

theorem node_mem_iff (i : ℕ) : phi6 (nodeEl i) ∈ Dsub ↔ parK PP (pathK EP.PL i i) = 0 := by
  rw [nodeEl, prod_mem_iff pgen (fun j => PP.getD j 0) _ fun j _ => pgen_mem_iff, parK_eq]

theorem coe_t6C : ((t6C : C6) : JH) = aJ := rfl

theorem sq_of {t : C6} (htJ : (t : JH) = aJ) : t ^ 2 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, htJ, Subgroup.coe_one]
  exact aJ_sq

theorem comm_of {t : C6} (htJ : (t : JH) = aJ) (x : C6) : x * t = t * x := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, htJ]
  exact ((Subgroup.mem_centralizer_iff.1 x.2) aJ (Set.mem_singleton aJ)).symm

theorem ne_one_of {t : C6} (htJ : (t : JH) = aJ) : t ≠ 1 := fun h => by
  have h' := congrArg Subtype.val h
  rw [htJ, Subgroup.coe_one] at h'
  exact aJ_ne_one h'

theorem ker_eq {k : C6} (hk : k ∈ phi6.ker) : k = 1 ∨ k = t6C := by
  have hz : Nat.card (Subgroup.zpowers t6C) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_mk_two _ aJ_sq aJ_ne_one
  have hle : Subgroup.zpowers t6C ≤ phi6.ker := by
    rw [Subgroup.zpowers_le]
    exact t6C_mem_ker
  have he := Subgroup.eq_of_le_of_card_ge hle (by rw [card_ker_phi6, hz])
  rw [← he, Subgroup.mem_zpowers_iff] at hk
  obtain ⟨n, rfl⟩ := hk
  have h2 : orderOf t6C = 2 := orderOf_mk_two _ aJ_sq aJ_ne_one
  rw [← zpow_mod_orderOf, h2]
  have : n % (2 : ℕ) = 0 ∨ n % (2 : ℕ) = 1 := by omega
  rcases this with h | h
  · left
    rw [h, zpow_zero]
  · right
    rw [h, zpow_one]

theorem iff_aux {a b : Prop} : ((a ↔ b) ↔ a) ↔ b := by tauto

theorem lenL_eq {α : Type} (l : List α) : CFSG.KC.Ord.lenL l = l.length := by
  induction l with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem sq_of_relW {i : ℕ} (hi : i < 1024)
    (h : relW RB mul 46 CFSG.KD.OrdHN.ONE (pathCodes EP.PL PR i ++ pathCodes EP.PL PR i) = true) :
    nodeEl i ^ 2 = 1 := by
  have h1 := wordEl_eq_one (fun c hc => by
    rcases List.mem_append.1 hc with hc | hc <;> exact node_codes hi c hc) h
  rw [wordEl_append, ← node_coe hi, ← Subgroup.coe_mul, ← pow_two] at h1
  exact Subtype.ext h1

theorem fac_range : (88704000 : ℕ).factorization 2 = 10 := by
  have h : (88704000 : ℕ) = 2 ^ 10 * 86625 := by norm_num
  have h2 : ¬ 2 ∣ 86625 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow,
    Nat.Prime.factorization Nat.prime_two]
  simp [Nat.factorization_eq_zero_of_not_dvd h2]

theorem dvd_H : 2 ^ (Nat.card phi6.range).factorization 2 ∣ Nat.card (Hs.subgroupOf phi6.range) := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe H_le).toEquiv, card_H, card_phi6_range, fac_range]
  norm_num

theorem pow_four {t g : C6} (ht : t ^ 2 = 1) (hg2 : g ^ 2 = t) : phi6 g ^ 4 = 1 := by
  rw [← map_pow, show g ^ 4 = (g ^ 2) ^ 2 by rw [← pow_mul], hg2, ht, map_one]

theorem conj_into {t g : C6} (ht : t ^ 2 = 1) (hg2 : g ^ 2 = t) :
    ∃ c : C6, phi6 (c * g * c⁻¹) ∈ Hs := by
  let σ : phi6.range := ⟨phi6 g, MonoidHom.mem_range.2 ⟨g, rfl⟩⟩
  have hσ : σ ^ 4 = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact pow_four ht hg2)
  obtain ⟨y, hy⟩ := CFSG.EvenSporadicStandard.TwoHS.exists_conj_mem_of_dvd_card _ dvd_H
    (CFSG.EvenSporadicStandard.TwoHS.isPGroup_zpowers_of_pow_four_eq_one hσ)
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 y.2
  refine ⟨c, ?_⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at hy
  rw [map_mul, map_mul, map_inv, hc]
  exact hy

theorem conj_mem_iff (c g : C6) : phi6 (c * g * c⁻¹) ∈ Dsub ↔ phi6 g ∈ Dsub := by
  rw [mem_mul_iff, mem_mul_iff, map_inv, inv_mem_iff]
  exact iff_aux

theorem conj_sq {t c g : C6} (htc : ∀ x : C6, x * t = t * x) (hg2 : g ^ 2 = t) :
    (c * g * c⁻¹) ^ 2 = t := by
  rw [conj_pow, hg2, htc c, mul_inv_cancel_right]

theorem sq_of_ker_gen {G : Type*} [Group G] {n z t : G} (ht : t ^ 2 = 1) (hc : n * t = t * n)
    (hk : n⁻¹ * z = 1 ∨ n⁻¹ * z = t) (hz : z ^ 2 = t) : n ^ 2 = t := by
  rcases hk with h | h
  · rw [inv_mul_eq_one] at h
    rw [h]
    exact hz
  · obtain rfl : z = n * t := by rw [← h, mul_inv_cancel_left]
    have hcomm : Commute n t := hc
    rw [hcomm.mul_pow, ht, mul_one] at hz
    exact hz

theorem tab_sq_fix {P : ℕ} {σ : Equiv.Perm (Fin 1100)} (hrep : TabRep (unpack 1100 11 P) σ)
    (hsq : σ * σ = 1) {x : ℕ} (hx : x < 1100) : pg 11 (mask 11) P (pg 11 (mask 11) P x) = x := by
  have h1 := hrep.apply ⟨x, hx⟩
  rw [HN2092.unpack_get' hx] at h1
  have h2 := hrep.apply (σ ⟨x, hx⟩)
  have hlt : pg 11 (mask 11) P x < 1100 := by rw [h1]; exact Fin.isLt _
  rw [← h1, HN2092.unpack_get' hlt] at h2
  rw [h2, ← Equiv.Perm.mul_apply, hsq]
  rfl

theorem node_ok {i : ℕ} (hi : i < 1024) :
    nodeK 1100 11 (mask 11) EP.T EP.PL PP INV i (NW.getD i 0) = true := by
  have hnodes := (by simpa only [bAnd_iff] using nodes_ok :
    Nat.beq (CFSG.KC.Ord.lenL NW) 1024 = true ∧ nodesK 1100 11 (mask 11) EP.T EP.PL PP INV NW 0 = true)
  have hlen : NW.length = 1024 := by
    have := Nat.eq_of_beq_eq_true hnodes.1
    rwa [lenL_eq] at this
  have hnode := nodesK_spec NW 0 hnodes.2 i (by rw [hlen]; exact hi)
  rwa [Nat.zero_add] at hnode

theorem odd_of_not_mem {i : ℕ} (h : phi6 (nodeEl i) ∉ Dsub) : parK PP (pathK EP.PL i i) = 1 := by
  have h1 : parK PP (pathK EP.PL i i) ≠ 0 := fun h0 => h ((node_mem_iff i).2 h0)
  have h2 : parK PP (pathK EP.PL i i) < 2 := by rw [parK_eq]; exact Nat.mod_lt _ (by norm_num)
  omega

theorem node_sq_ne (t : C6) (htJ : (t : JH) = aJ) (ht1 : phi6 t = 1) {i : ℕ} (hi : i < 1024)
    (hodd : parK PP (pathK EP.PL i i) = 1) (hn2 : nodeEl i ^ 2 = t) : False := by
  rcases nodeK_odd (node_ok hi) hodd with hinv | ⟨x, hx, hmove⟩
  · have h1 := sq_of_relW hi (List.all_eq_true.1 irels _ (sqPathsK_spec INV IREL inv_ok i hinv))
    rw [hn2] at h1
    exact ne_one_of htJ h1
  · refine hmove (tab_sq_fix (tab_node i hi) ?_ hx)
    rw [← map_mul, ← pow_two, hn2]
    exact ht1

theorem exists_node {z : C6} (hzH : phi6 z ∈ Hs) : ∃ i < 1024, phi6 z = phi6 (nodeEl i) := by
  obtain ⟨i, hi, hrep⟩ := enum_H.exists_pos hzH
  rw [EPr_size] at hi
  rw [EPr_tab hi] at hrep
  exact ⟨i, hi, hrep.perm_eq (tab_node i hi)⟩

theorem s1 (t : C6) (htJ : (t : JH) = aJ) (ht1 : phi6 t = 1)
    (hker : ∀ k ∈ phi6.ker, k = 1 ∨ k = t) (g : C6) (hgN : g ∉ Dsub.comap phi6)
    (hg2 : g ^ 2 = t) : False := by
  obtain ⟨c, hzH⟩ := conj_into (sq_of htJ) hg2
  obtain ⟨i, hi, hphi⟩ := exists_node hzH
  have hzN : phi6 (nodeEl i) ∉ Dsub := fun h =>
    hgN (Subgroup.mem_comap.2 ((conj_mem_iff c g).1 (by rw [hphi]; exact h)))
  have hk : (nodeEl i)⁻¹ * (c * g * c⁻¹) ∈ phi6.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hphi, inv_mul_cancel]
  exact node_sq_ne t htJ ht1 hi (odd_of_not_mem hzN)
    (sq_of_ker_gen (sq_of htJ) (comm_of htJ _) (hker _ hk) (conj_sq (comm_of htJ) hg2))

theorem codeEl_zero_gen {G : Type*} [Group G] (ρ : ℕ → G) : codeEl ρ 0 = (ρ 0)⁻¹ := by
  rw [codeEl, if_neg (by norm_num), Nat.zero_div]

theorem sq_of_word_gen {G : Type*} [Group G] (ρ : ℕ → G) (u : List ℕ)
    (h : wordEl ρ (List.append u (List.append u [0])) = 1) : wordEl ρ u * wordEl ρ u = ρ 0 := by
  rw [List.append_eq, List.append_eq, wordEl_append, wordEl_append, wordEl_single,
    codeEl_zero_gen, ← mul_assoc, mul_inv_eq_one] at h
  exact h

theorem sq_of_word {i : ℕ} {W : List ℕ} (hi : i < 1024)
    (he : W = List.append (pathCodes EP.PL PR i) (List.append (pathCodes EP.PL PR i) [0]))
    (hrel : relW RB mul 46 CFSG.KD.OrdHN.ONE W = true) :
    ((nodeEl i : C6) : JH) * ((nodeEl i : C6) : JH) = aJ := by
  subst he
  have hw := wordEl_eq_one (fun c hc => by
    rcases List.mem_append.1 hc with hc | hc
    · exact node_codes hi c hc
    · rcases List.mem_append.1 hc with hc | hc
      · exact node_codes hi c hc
      · rw [List.mem_singleton] at hc
        omega) hrel
  have h := sq_of_word_gen rEl _ hw
  rw [← node_coe hi, rEl_zero] at h
  exact h

theorem s2_of (t : C6) (htJ : (t : JH) = aJ) {i : ℕ} {W : List ℕ} (hi : i < 1024)
    (hpar : parK PP (pathK EP.PL i i) = 0)
    (he : W = List.append (pathCodes EP.PL PR i) (List.append (pathCodes EP.PL PR i) [0]))
    (hrel : relW RB mul 46 CFSG.KD.OrdHN.ONE W = true) :
    ∃ x : C6, x ∈ Dsub.comap phi6 ∧ x ^ 2 = t := by
  refine ⟨nodeEl i, Subgroup.mem_comap.2 ((node_mem_iff i).2 hpar), ?_⟩
  apply Subtype.ext
  rw [Subgroup.coe_pow, pow_two, htJ]
  exact sq_of_word hi he hrel

theorem s2 (t : C6) (htJ : (t : JH) = aJ) : ∃ x : C6, x ∈ Dsub.comap phi6 ∧ x ^ 2 = t := by
  obtain ⟨h1, h2, h3⟩ := (by simpa only [bAnd_iff] using s2_ok :
    Nat.blt S2N 1024 = true ∧ Nat.beq (parK PP (pathK EP.PL S2N S2N)) 0 = true ∧
      eqLK S2W (List.append (pathCodes EP.PL PR S2N)
        (List.append (pathCodes EP.PL PR S2N) [0])) = true)
  exact s2_of t htJ (Nat.le_of_ble_eq_true h1) (Nat.eq_of_beq_eq_true h2) (eqLK_spec h3) s2rel

end CertificateChecks.KernelHN25550

namespace CertificateChecks.KernelHN25550

theorem sign_facts :
    (∀ g : CFSG.Sporadic.HNOddCore.C6,
        g ∉ CFSG.Sporadic.HNOddCore.Dsub.comap CFSG.Sporadic.HNOddCore.phi6 →
        g ^ 2 = CFSG.Sporadic.HNOddCore.t6C → False) ∧
      ∃ x : CFSG.Sporadic.HNOddCore.C6,
        x ∈ CFSG.Sporadic.HNOddCore.Dsub.comap CFSG.Sporadic.HNOddCore.phi6 ∧
        x ^ 2 = CFSG.Sporadic.HNOddCore.t6C := by
  exact ⟨s1 _ coe_t6C (MonoidHom.mem_ker.1 CFSG.Sporadic.HNOddCore.t6C_mem_ker)
    fun _ hk => ker_eq hk, s2 _ coe_t6C⟩

end CertificateChecks.KernelHN25550

end
