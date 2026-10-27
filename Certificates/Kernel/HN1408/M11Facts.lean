
module

public import Certificates.Kernel.HN1408.M11Glue
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.M11Spec2
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableISpec

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

abbrev RepC (X : Nat) (g : Equiv.Perm (Fin 1408)) : Prop :=
  Cn X ∧ Rep 1408 (tabT (unpack 1408 11 X)) g

theorem repC_pc {X Y : Nat} {g h : Equiv.Perm (Fin 1408)} (hX : RepC X g) (hY : RepC Y h) :
    RepC (pc X Y) (g * h) := by
  refine ⟨canonK_pcomp hX.1 hY.1, ?_⟩
  have e : pc X Y = pcomp 1408 11 (mask 11) X Y := rfl
  rw [e, ← compT_unpack hX.1 hY.1]
  exact Rep.compT hX.2 hY.2

theorem repWM {w : List Nat} (hw : lettersOK w = true) : Rep 1408 (tabW w) (elemW w) :=
  rep_elemW_of_gensOK gensOK_true (wordOK_of hw)

theorem repC_word {w : List Nat} (hw : lettersOK w = true) : RepC (WK w) (elemW w) := by
  refine ⟨(tabW_eq hw).2, ?_⟩
  rw [← (tabW_eq hw).1]
  exact repWM hw

theorem repC_pt {X x : Nat} {g : Equiv.Perm (Fin 1408)} (hX : RepC X g) (hx : x < 1408) :
    pt X x = (g ⟨x, hx⟩).val := by
  rw [← ap_eq hX.1 hx, hX.2 x hx, idx_of_lt g hx, Equiv.Perm.smul_def]

theorem eq_of_repC {X : Nat} {g h : Equiv.Perm (Fin 1408)} (hg : RepC X g) (hh : RepC X h) :
    g = h := CFSG.Sporadic.Schreier.rep_unique hg.2 hh.2

theorem hry : RepC (WK y0Word) (elemW y0Word) := repC_word (by decide)

theorem orderOf_y : orderOf (elemW y0Word) = 11 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact orderOf_eq_of_primeOrderOK (repWM (by decide)) mkY

theorem repC_yp {k : Nat} (hk : k ≤ 11) : RepC (MYP k) (elemW y0Word ^ k) := by
  have e : MYP k = ppK (WK y0Word) k := Nat.eq_of_beq_eq_true (allN_spec kYP k (by omega))
  rw [e]
  refine ⟨cn_ppK hry.1 k, ?_⟩
  rw [← powT_eq hry.1 k]
  exact Rep.powT (by norm_num) hry.2 k

theorem y_inv {k : Nat} (hk : k ≤ 11) : elemW y0Word ^ (11 - k) = (elemW y0Word ^ k)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← pow_add, Nat.sub_add_cancel hk, ← orderOf_y, pow_orderOf_eq_one]

theorem lettersOK_gen {j : Nat} (hj : j < 7) : lettersOK [j + 1] = true := by
  simp only [lettersOK, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq]
  omega

theorem gen_inv {j : Nat} (hj : j < 7) : (elemW [j + 1])⁻¹ = elemW [j + 1] := by
  have hG := repC_word (lettersOK_gen hj)
  have e : pc (WK [j + 1]) (WK [j + 1]) = idK := Nat.eq_of_beq_eq_true (allN_spec kG j hj)
  have h2 : RepC idK 1 := ⟨cId, by rw [← idT_eq]; exact Rep.idT (by norm_num)⟩
  have h1 := repC_pc hG hG
  rw [e] at h1
  exact inv_eq_of_mul_eq_one_right (eq_of_repC h1 h2)

theorem mem_closure_flatMap :
    ∀ l : List Nat, elemW (l.flatMap fun l => if l = 0 then y0Word else i0Word) ∈
      closure ({elemW y0Word, elemW i0Word} : Set (Equiv.Perm (Fin 1408)))
  | [] => by
    have e : elemW [] = 1 := by simp [elemW, CFSG.EvenSporadicStandard.TwoHS.wordVal]
    rw [List.flatMap_nil, e]
    exact one_mem _
  | a :: l => by
    rw [List.flatMap_cons, elemW_append]
    refine mul_mem ?_ (mem_closure_flatMap l)
    by_cases h : a = 0
    · rw [if_pos h]
      exact subset_closure (Set.mem_insert _ _)
    · rw [if_neg h]
      exact subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem v_eq : elemW vWord = elemW vWordYI := by
  have e : WK vWordYI = WK vWord := Nat.eq_of_beq_eq_true kVW
  have h1 := repC_word (w := vWordYI) (by decide)
  rw [e] at h1
  exact eq_of_repC (repC_word (by decide)) h1

theorem enumA : enumW invCap 7920 [y0Word, vWord] = true := recA.1

theorem y0_mem : elemW y0Word ∈ m11K := subset_closure ⟨y0Word, by simp, rfl⟩

theorem m11_group :
    Nat.card ↥m11K = 7920 ∧ orderOf (elemW y0Word) = 11 ∧ orderOf (elemW vWord) = 11 ∧
      elemW y0Word * elemW vWord ≠ elemW vWord * elemW y0Word ∧
      (∀ w ∈ m11Relators, CFSG.Sporadic.Bridge.wordProd (fun i => if i = 0 then elemW y0Word else
        if i = 1 then elemW vWord else 1) w = 1) ∧
      (∀ g ∈ m11K, TwoHSData.M11Order (orderOf g)) ∧
      orderOf (elemW i0Word) = 2 ∧ elemW i0Word ∈ m11K ∧
      closure ({elemW y0Word, elemW i0Word} : Set (Equiv.Perm (Fin 1408))) = m11K := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := enumA
  obtain ⟨hg, -⟩ := enumW_gens_words h1
  obtain ⟨hcard, hL0⟩ := enumW_spec h1
  have hry' : Rep 1408 (tabW y0Word) (elemW y0Word) := rep_elemW_of_gensOK hg (by decide)
  have hrv : Rep 1408 (tabW vWord) (elemW vWord) := rep_elemW_of_gensOK hg (by decide)
  have hri : Rep 1408 (tabW i0Word) (elemW i0Word) := rep_elemW_of_gensOK hg (by decide)
  have hid : Rep 1408 (idT 1408) (1 : Equiv.Perm (Fin 1408)) := Rep.idT (by norm_num)
  have hiy' := Rep.inv_of_invOK hry' mkIY
  have hiv' := Rep.inv_of_invOK hrv mkIV
  have hi0K : elemW i0Word ∈ m11K := by
    have h := mkWin
    unfold wordsInOK at h
    simp only [List.all_cons, List.all_nil, Bool.and_true] at h
    exact (hL0.memT_iff hri).1 h
  refine ⟨hcard, orderOf_eq_of_primeOrderOK hry' mkY, orderOf_eq_of_primeOrderOK hrv mkV,
    fun hcon => ?_, fun w hw => ?_, (ordAllOK_iff hid hL0).1 mkOrd,
    orderOf_eq_of_primeOrderOK hri mkI, hi0K, ?_⟩
  · have h2 := mkYV
    rw [(commTT_iff hry' hrv).2 hcon] at h2
    exact absurd h2 (by decide)
  · exact (tblEq_iff_eq (rep_relTab hry' hrv hiy' hiv' w) hid).1
      (List.all_eq_true.1 mkRel w hw)
  · apply le_antisymm
    · rw [closure_le]
      rintro _ (rfl | rfl)
      · exact y0_mem
      · exact hi0K
    · rw [m11K_eq_closure, closure_le]
      rintro _ (rfl | rfl)
      · exact subset_closure (Set.mem_insert _ _)
      · rw [v_eq]
        exact mem_closure_flatMap vYI

theorem m11Prop_of_jK {J W : Nat} {g : Equiv.Perm (Fin 1408)} (hJ : RepC J g)
    (h : jK (WK n1Word) (MInv 2) (WK y0Word) J W = true) : m11Prop g := by
  have h1 := enumA
  obtain ⟨hg, -⟩ := enumW_gens_words h1
  obtain ⟨-, hL0⟩ := enumW_spec h1
  obtain ⟨hwn, hinv⟩ := conjEqOK_parts mkN1
  have hrn : Rep 1408 (tabW n1Word) (elemW n1Word) := rep_elemW_of_gensOK hg hwn
  have hrni := Rep.inv_of_invOK hrn hinv
  have hry' : Rep 1408 (tabW y0Word) (elemW y0Word) := rep_elemW_of_gensOK hg (by decide)
  have hid : Rep 1408 (idT 1408) (1 : Equiv.Perm (Fin 1408)) := Rep.idT (by norm_num)
  obtain ⟨hsz, hys⟩ := rep_powsT hry'
  have hL : IsEnumSet 1408 #[tabT (unpack 1408 11 J)] {g} := by
    refine ⟨fun k hk => ⟨g, rfl, ?_⟩, fun x hx => ⟨0, by simp, ?_⟩⟩
    · have hk0 : k = 0 := by simpa using hk
      subst hk0
      simpa using hJ.2
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      simpa using hJ.2
  have hc : m11ClassOK (idT 1408) (tabW n1Word) (invT 1408 (tabW n1Word)) (powsT (tabW y0Word))
      (subgroupList invCap [y0Word, vWord]) #[tabT (unpack 1408 11 J)] = true := by
    unfold m11ClassOK
    simpa using mkJ_spec hJ.1 h
  exact (m11ClassOK_iff hid hrn hrni hys hsz hL0 hL).1 hc g rfl

theorem probeG_conj {c y g : Equiv.Perm (Fin 1408)} (hc : Commute c y) :
    ∀ p : List Nat, probeG y (c * g * c⁻¹) p = c * probeG y g p * c⁻¹
  | [] => by simp [probeG]
  | e :: p => by
    have hce : y ^ e * c = c * y ^ e := ((hc.pow_right e).eq).symm
    have ih := probeG_conj (g := g) hc p
    simp only [probeG, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih]
    calc y ^ e * (c * g * c⁻¹) * (c * (List.map (fun e => y ^ e * g) p).prod * c⁻¹)
        = (y ^ e * c) * g * (List.map (fun e => y ^ e * g) p).prod * c⁻¹ := by group
      _ = c * (y ^ e * g * (List.map (fun e => y ^ e * g) p).prod) * c⁻¹ := by
        rw [hce]
        group

theorem m11Prop_conj {g : Equiv.Perm (Fin 1408)} (h : m11Prop g) (k : Nat) :
    m11Prop (elemW y0Word ^ k * g * (elemW y0Word ^ k)⁻¹) := by
  have hcK : elemW y0Word ^ k ∈ m11K := pow_mem y0_mem k
  have hcy : Commute (elemW y0Word ^ k) (elemW y0Word) := (Commute.self_pow _ k).symm
  have hn : elemW n1Word * elemW y0Word * (elemW n1Word)⁻¹ = elemW y0Word ^ 7 :=
    conjEqOK_spec (enumW_gens_words enumA).1 (repWM (by decide))
      (Rep.powT (by norm_num) (repWM (w := y0Word) (by decide)) 7) mkN1
  have hnc : elemW n1Word * elemW y0Word ^ k * (elemW n1Word)⁻¹ = (elemW y0Word ^ 7) ^ k := by
    rw [← hn, conj_pow]
  have hnK : elemW n1Word * elemW y0Word ^ k * (elemW n1Word)⁻¹ ∈ m11K := by
    rw [hnc]
    exact pow_mem (pow_mem y0_mem 7) k
  rcases h with ⟨p, hp, ho⟩ | hm | hm
  · left
    refine ⟨p, hp, ?_⟩
    rw [probeG_conj hcy p]
    have e : orderOf (elemW y0Word ^ k * probeG (elemW y0Word) g p * (elemW y0Word ^ k)⁻¹) =
        orderOf (probeG (elemW y0Word) g p) := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    rw [e]
    exact ho
  · right
    left
    exact mul_mem (mul_mem hcK hm) (inv_mem hcK)
  · right
    right
    have e : elemW n1Word * (elemW y0Word ^ k * g * (elemW y0Word ^ k)⁻¹) * (elemW n1Word)⁻¹ =
        (elemW n1Word * elemW y0Word ^ k * (elemW n1Word)⁻¹) * (elemW n1Word * g * (elemW n1Word)⁻¹) *
          (elemW n1Word * elemW y0Word ^ k * (elemW n1Word)⁻¹)⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hnK hm) (inv_mem hnK)

theorem clsK_parts {w : List Nat} {R P S W : Nat → Nat} {n cnt : Nat}
    (h : clsK w R P S W n cnt = true) :
    R 0 = WK w ∧ (∀ i < n, 0 < i → repK R P i = true) ∧ sortK R S n cnt = true ∧
      jAll n R W = true := by
  unfold clsK at h
  obtain ⟨h1, h2⟩ := mkA h
  obtain ⟨h3, h4⟩ := mkA h2
  obtain ⟨h5, h6⟩ := mkA h4
  refine ⟨Nat.eq_of_beq_eq_true h1, fun i hi hi0 => ?_, h5, h6⟩
  have h7 := allN_spec h3 i hi
  have e : Nat.beq i 0 = false :=
    Bool.eq_false_iff.2 fun h' => by have := Nat.eq_of_beq_eq_true h'; omega
  rw [e] at h7
  exact h7

theorem repK_parts {R P : Nat → Nat} {i : Nat} (h : repK R P i = true) :
    ∃ p k j, p < i ∧ k < 11 ∧ j < 7 ∧
      R i = pc (pc (WK [j + 1]) (pc (pc (MYP k) (R p)) (MYP (11 - k)))) (WK [j + 1]) := by
  unfold repK at h
  simp only [strictB_app] at h
  obtain ⟨a, h⟩ := mkA h
  obtain ⟨b, h⟩ := mkA h
  obtain ⟨c, d⟩ := mkA h
  exact ⟨_, _, _, Nat.blt_eq.mp a, Nat.blt_eq.mp b, Nat.blt_eq.mp c, Nat.eq_of_beq_eq_true d⟩

theorem reps_mem {w : List Nat} (hw : lettersOK w = true) {R P S W : Nat → Nat} {n cnt : Nat}
    (h : clsK w R P S W n cnt = true) :
    ∀ i < n, ∃ c ∈ P1408, RepC (R i) (c * elemW w * c⁻¹) := by
  obtain ⟨h0, hr, -, -⟩ := clsK_parts h
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · refine ⟨1, one_mem _, ?_⟩
      rw [h0]
      simpa using repC_word hw
    · obtain ⟨p, k, j, hp, hk, hj, e⟩ := repK_parts (hr i hi hpos)
      obtain ⟨c, hcP, hc⟩ := ih p hp (by omega)
      have hG := repC_word (lettersOK_gen hj)
      have hR := repC_pc (repC_pc hG (repC_pc (repC_pc (repC_yp (k := k) (by omega)) hc)
        (repC_yp (k := 11 - k) (by omega)))) hG
      rw [← e] at hR
      refine ⟨elemW [j + 1] * elemW y0Word ^ k * c,
        mul_mem (mul_mem (elemW_mem _) (pow_mem (elemW_mem _) k)) hcP, ?_⟩
      convert hR using 1
      calc (elemW [j + 1] * elemW y0Word ^ k * c) * elemW w * (elemW [j + 1] * elemW y0Word ^ k * c)⁻¹
          = elemW [j + 1] * (elemW y0Word ^ k * (c * elemW w * c⁻¹) * (elemW y0Word ^ k)⁻¹) *
              (elemW [j + 1])⁻¹ := by group
        _ = _ := by rw [gen_inv hj, y_inv (by omega)]

@[expose] def keyP (g : Equiv.Perm (Fin 1408)) : Nat :=
  (g ⟨0, by norm_num⟩).val + 2048 * (g ⟨1, by norm_num⟩).val +
    4194304 * (g ⟨2, by norm_num⟩).val + 8589934592 * (g ⟨3, by norm_num⟩).val

theorem keyK_eq {X k : Nat} {g : Equiv.Perm (Fin 1408)} (hX : RepC X g) (hk : k ≤ 11) :
    keyK X k = keyP (elemW y0Word ^ k * g * (elemW y0Word ^ k)⁻¹) := by
  have hA := repC_yp (k := k) hk
  have hB := repC_yp (k := 11 - k) (by omega)
  rw [y_inv hk] at hB
  have hC := repC_pc (repC_pc hA hX) hB
  have hp : ∀ x (hx : x < 1408), pt (MYP k) (pt X (pt (MYP (11 - k)) x)) =
      ((elemW y0Word ^ k * g * (elemW y0Word ^ k)⁻¹) ⟨x, hx⟩).val := by
    intro x hx
    rw [← repC_pt hC hx, pt_pc (X := pc (MYP k) X) (canonK_pcomp hA.1 hX.1) hx,
      pt_pc hA.1 (pt_lt hB.1 hx)]
  unfold keyK keyP
  rw [hp 0 (by norm_num), hp 1 (by norm_num), hp 2 (by norm_num), hp 3 (by norm_num)]
  simp only [Nat.add_eq, Nat.mul_eq]
  omega

theorem class_prop {w : List Nat} (hw : lettersOK w = true) {R P S W : Nat → Nat} {n cnt : Nat}
    (h : clsK w R P S W n cnt = true)
    (hc : (conjClass P1408 (elemW w)).ncard = cnt) :
    ∀ g ∈ conjClass P1408 (elemW w), m11Prop g := by
  obtain ⟨-, -, hs, hj⟩ := clsK_parts h
  have hreps := reps_mem hw h
  have H : ∀ i, ∃ r : Equiv.Perm (Fin 1408), i < n → r ∈ conjClass P1408 (elemW w) ∧
      RepC (R i) r := by
    intro i
    by_cases hi : i < n
    · obtain ⟨c, hcP, hcR⟩ := hreps i hi
      exact ⟨_, fun _ => ⟨⟨c, hcP, rfl⟩, hcR⟩⟩
    · exact ⟨1, fun h => absurd h hi⟩
  choose r hr using H
  have hS : ∀ m < cnt, f16 (S m) 0 < n ∧ f16 (S m) 1 < 11 := by
    intro m hm
    have h1 := allN_spec hs m hm
    simp only [strictB_app] at h1
    obtain ⟨a, h1⟩ := mkA h1
    obtain ⟨b, -⟩ := mkA h1
    exact ⟨Nat.blt_eq.mp a, Nat.blt_eq.mp b⟩
  obtain ⟨e, he⟩ : ∃ e : Nat → Equiv.Perm (Fin 1408), ∀ m, e m =
      elemW y0Word ^ f16 (S m) 1 * r (f16 (S m) 0) * (elemW y0Word ^ f16 (S m) 1)⁻¹ :=
    ⟨_, fun _ => rfl⟩
  have hkey : ∀ m < cnt, keyK (R (f16 (S m) 0)) (f16 (S m) 1) = keyP (e m) := by
    intro m hm
    rw [he m]
    exact keyK_eq (hr _ (hS m hm).1).2 (by have := (hS m hm).2; omega)
  have hsucc : ∀ m, m + 1 < cnt → keyP (e m) < keyP (e (m + 1)) := by
    intro m hm
    have h1 := allN_spec hs m (by omega)
    simp only [strictB_app] at h1
    obtain ⟨-, h1⟩ := mkA h1
    obtain ⟨-, h1⟩ := mkA h1
    have e1 : Nat.blt (m + 1) cnt = true := Nat.blt_eq.mpr hm
    rw [e1] at h1
    rw [← hkey m (by omega), ← hkey (m + 1) hm]
    exact Nat.blt_eq.mp h1
  have hmono : ∀ m m', m < m' → m' < cnt → keyP (e m) < keyP (e m') := by
    intro m m' hlt hm'
    induction m' with
    | zero => omega
    | succ m' ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with h' | h'
      · exact (ih h' (by omega)).trans (hsucc m' hm')
      · rw [h']
        exact hsucc m' hm'
  have hinj : Set.InjOn e ↑(Finset.range cnt) := by
    intro m hm m' hm' hee
    have hm1 : m < cnt := Finset.mem_range.1 hm
    have hm2 : m' < cnt := Finset.mem_range.1 hm'
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have h1 := hmono m m' hlt hm2
      rw [hee] at h1
      exact lt_irrefl _ h1
    · have h1 := hmono m' m hlt hm1
      rw [hee] at h1
      exact lt_irrefl _ h1
  have hsub : (↑((Finset.range cnt).image e) : Set (Equiv.Perm (Fin 1408))) ⊆
      conjClass P1408 (elemW w) := by
    intro x hx
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hx
    have hm1 : m < cnt := Finset.mem_range.1 hm
    obtain ⟨⟨c, hcP, hcr⟩, -⟩ := hr _ (hS m hm1).1
    refine ⟨elemW y0Word ^ f16 (S m) 1 * c, mul_mem (pow_mem (elemW_mem _) _) hcP, ?_⟩
    rw [he m, hcr]
    group
  have hfin : (conjClass P1408 (elemW w)).Finite := Set.toFinite _
  have heq : (↑((Finset.range cnt).image e) : Set (Equiv.Perm (Fin 1408))) =
      conjClass P1408 (elemW w) := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ hfin
    rw [hc, Set.ncard_coe_finset, Finset.card_image_of_injOn hinj, Finset.card_range]
  intro g hg
  rw [← heq] at hg
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hg
  have hm1 : m < cnt := Finset.mem_range.1 hm
  rw [he m]
  refine m11Prop_conj ?_ _
  have hj' := hj
  unfold jAll at hj'
  simp only [strictB_app] at hj'
  have hi := (hS m hm1).1
  exact m11Prop_of_jK (hr _ hi).2 (allN_spec hj' _ hi)

theorem elemW_az : elemW classaz.rep = elemA * elemZ := by
  have e : classaz.rep = wordA ++ wordZ := by decide
  rw [e, elemW_append]
  rfl

theorem m11_facts :
    Nat.card ↥m11K = 7920 ∧ orderOf (elemW y0Word) = 11 ∧ orderOf (elemW vWord) = 11 ∧
      elemW y0Word * elemW vWord ≠ elemW vWord * elemW y0Word ∧
      (∀ w ∈ m11Relators, CFSG.Sporadic.Bridge.wordProd (fun i => if i = 0 then elemW y0Word else
        if i = 1 then elemW vWord else 1) w = 1) ∧
      (∀ g ∈ m11K, TwoHSData.M11Order (orderOf g)) ∧
      orderOf (elemW i0Word) = 2 ∧ elemW i0Word ∈ m11K ∧
      closure ({elemW y0Word, elemW i0Word} : Set (Equiv.Perm (Fin 1408))) = m11K ∧
      elemW n1Word * elemW y0Word * (elemW n1Word)⁻¹ = elemW y0Word ^ 7 ∧
      ((conjClass P1408 elemZ).ncard = 5775 → ∀ g ∈ conjClass P1408 elemZ, m11Prop g) ∧
      ((conjClass P1408 (elemA * elemZ)).ncard = 5775 →
        ∀ g ∈ conjClass P1408 (elemA * elemZ), m11Prop g) ∧
      orderOf (elemW rho0Word) = 5 ∧ elemW rho0Word ∈ m11K ∧
      (∀ k : ℕ, 0 < k → k < 5 → ∃ c ∈ m11K, c * elemW rho0Word * c⁻¹ = elemW rho0Word ^ k) ∧
      elemW cBWord * elemW rho0Word * (elemW cBWord)⁻¹ = elemW fix5B.rep := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := m11_group
  have hg := (enumW_gens_words enumA).1
  obtain ⟨-, hL0⟩ := enumW_spec enumA
  have hn : elemW n1Word * elemW y0Word * (elemW n1Word)⁻¹ = elemW y0Word ^ 7 :=
    conjEqOK_spec hg (repWM (by decide))
      (Rep.powT (by norm_num) (repWM (w := y0Word) (by decide)) 7) mkN1
  have hz : elemW classz.rep = elemZ := by
    have e : classz.rep = wordZ := by decide
    rw [e]
    rfl
  refine ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, hn, fun h => ?_, fun h => ?_,
    m11FiveOK_spec hg hL0 mkFive⟩
  · rw [← hz] at h ⊢
    exact class_prop (by decide) kCZ h
  · rw [← elemW_az] at h ⊢
    exact class_prop (by decide) kCAZ h

end CFSG.KD.HN1408

end
