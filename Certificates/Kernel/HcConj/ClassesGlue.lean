module

public import Certificates.Kernel.HcConj.Extra
public import CFSG.Certificates.Kernel.HcConjSound
public import Certificates.Kernel.HcReplay.FactsGlue
import all Certificates.Data.Kernel.HcPack
import all Certificates.Data.Kernel.HcConj
import all Certificates.Data.G23RecogGlueInputs
import all Certificates.Data.G23RecogHFactsInputs
public import Certificates.Data.G23RecogHCharInputs
import all Certificates.Data.G23RecogHCharInputs

public section

namespace CFSG.KC.HcPack

open CFSG.GH74.QTGen4.Recog.G23 CFSG.GH74.QTGen4.Recog.G23.HFactsData
  CFSG.GH74.QTGen4.Recog.G23.HCharData

theorem hcRepL_eq (j : Fin 20) : hcRepL j = Lx (hcRep j) := by
  simp [hcRepL, hcRepTab]

theorem KC_eq (j : Fin 20) : KC j = cjClass (hcRepL j) := by
  simp [KC, KTab]

theorem KFst_eq (j : Fin 20) : KFst j = (KC j).map Prod.fst := by
  have hs : j.val < KTab.size := by simp [KTab]
  unfold KFst KFstTab KC
  rw [getElem!_pos (KTab.map fun l => l.map Prod.fst) j.val (by simpa using hs),
    getElem!_pos KTab j.val hs, Array.getElem_map]

theorem pk_evalW : ∀ w : List (Fin 5 × Bool), pk (Lx (HCharData.evalW w)) = evalP w
  | [] => by
    have e : HCharData.evalW [] = 1 := by simp [HCharData.evalW]
    have e2 : Lx (1 : ↥Hc) = idL := by rw [glue_idL_eq]; rfl
    rw [e, e2, pk_idL]
    rfl
  | p :: w => by
    have e0 : HCharData.evalW (p :: w) = cond p.2 (gA p.1) (gA p.1)⁻¹ * HCharData.evalW w := by
      simp only [HCharData.evalW, List.map_cons, List.prod_cons]
    have e3 : evalP (p :: w) = mulP (wP p) (evalP w) := by
      simp only [evalP, List.foldr_cons]
    have e : Lx (HCharData.evalW (p :: w)) =
        mulL (Lx (cond p.2 (gA p.1) (gA p.1)⁻¹)) (Lx (HCharData.evalW w)) := by
      rw [e0]
      unfold Lx
      rw [Subgroup.coe_mul, Lst_mul]
    rw [e, pk_mulL (VL_Lx _) (VL_Lx _), ch320017_letters, pk_evalW w, e3]

theorem VL_rep (j : Fin 20) : VL (hcRepL j) := by
  rw [hcRepL_eq]
  exact VL_Lx _

theorem pk_rep (j : Fin 20) : pk (hcRepL j) = hcRP.getD j 0 := by
  rw [hcRepL_eq, hcRep, pk_evalW, ch320017_words]

theorem VL_KC (j : Fin 20) : ∀ q ∈ KC j, VL q.1 ∧ VL q.2 := by
  rw [KC_eq]
  exact VL_cjClass _ (VL_rep j)

theorem KC_map_pk (j : Fin 20) : (KC j).map (F2 pk) = (hcF j).zip (hcS j) := by
  rw [KC_eq, cjClass_map_pk _ (VL_rep j), pk_rep, ch320017_class]

theorem hcF_len (j : Fin 20) : (hcF j).length = (hcS j).length := by
  rw [(ch320017_nodup.2.2.2.2 j).1, (ch320017_nodup.2.2.2.2 j).2]

theorem KFst_map_pk (j : Fin 20) : (KFst j).map pk = hcF j := by
  have e : (KFst j).map pk = ((KC j).map (F2 pk)).map Prod.fst := by
    rw [KFst_eq, List.map_map, List.map_map]
    rfl
  rw [e, KC_map_pk, List.map_fst_zip (Nat.le_of_eq (hcF_len j))]

theorem VL_KFst (j : Fin 20) : ∀ x ∈ KFst j, VL x := by
  intro x hx
  rw [KFst_eq] at hx
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
  exact (VL_KC j q hq).1

theorem mem_KFst {j : Fin 20} {x : List ℕ} (hx : VL x) : x ∈ KFst j ↔ pk x ∈ hcF j := by
  rw [mem_iff_pk (VL_KFst j) hx, KFst_map_pk]

theorem pk_mem_KC {j : Fin 20} {q : List ℕ × List ℕ} (hq : q ∈ KC j) :
    (pk q.1, pk q.2) ∈ (hcF j).zip (hcS j) := by
  rw [← KC_map_pk]
  exact List.mem_map_of_mem (f := F2 pk) hq

theorem mem_E_iff {x : List ℕ} (hx : VL x) : x ∈ elts ↔ pk x ∈ hcElts.E := by
  rw [mem_iff_pk VL_elts hx, elts_map_pk_eq]

theorem hcElts_len : hcElts.E.length = 576 := ch320017_inv.1

theorem mem_E_of_posB {xs ds : List ℕ}
    (h : posB (fun e x _ => Nat.beq e x) (getT (ofT 576 hcElts.E)) 576 [0] xs ds = true) :
    ∀ x ∈ xs, x ∈ hcElts.E := by
  intro x hx
  have h' := h
  rw [← hcElts_len] at h'
  obtain ⟨e, he, hq⟩ := posB_sound _ _ hcElts.E (getT_ofT _ _ (Nat.le_refl _)) [0] xs ds h' x hx 0
    List.mem_cons_self
  rwa [← Nat.eq_of_beq_eq_true hq]

theorem KC_mem_elts {j : Fin 20} {q : List ℕ × List ℕ} (hq : q ∈ KC j) :
    q.1 ∈ elts ∧ q.2 ∈ elts := by
  have hz := pk_mem_KC hq
  have h1 := List.of_mem_zip hz
  exact ⟨(mem_E_iff (VL_KC j q hq).1).2 (mem_E_of_posB (ch320017_memF j) _ h1.1),
    (mem_E_iff (VL_KC j q hq).2).2 (mem_E_of_posB (ch320017_memS j) _ h1.2)⟩

theorem hcL_nodup : hcL.Nodup := by
  obtain ⟨_, h1, h2, h3, _⟩ := ch320017_nodup
  rw [← h1] at h2 h3
  exact nodup_of_incT h2 h3

theorem KF_get (j : Fin 20) : hcCj.KF[j.val]'(by rw [ch320017_nodup.1]; exact j.2) = hcF j := by
  rw [hcF, List.getD_eq_getElem]

theorem hcF_nodup (j : Fin 20) : (hcF j).Nodup := by
  have h := (List.nodup_flatten.1 hcL_nodup).1
  rw [← KF_get]
  exact h _ (List.getElem_mem _)

theorem hcF_disj {i j : Fin 20} (hij : i ≠ j) {c : ℕ} (hi : c ∈ hcF i) (hj : c ∈ hcF j) : False := by
  have hp := (List.nodup_flatten.1 hcL_nodup).2
  rw [List.pairwise_iff_getElem] at hp
  have hl : hcCj.KF.length = 20 := ch320017_nodup.1
  rw [← KF_get] at hi hj
  rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
  · exact List.disjoint_left.1 (hp i j (by rw [hl]; exact i.2) (by rw [hl]; exact j.2) h) hi hj
  · exact List.disjoint_left.1 (hp j i (by rw [hl]; exact j.2) (by rw [hl]; exact i.2) h) hj hi

theorem cover (c : ℕ) (hc : c ∈ hcElts.E) : ∃ j : Fin 20, c ∈ hcF j := by
  have h := ch320017_cover
  have hl : hcL.length = 576 := ch320017_nodup.2.1
  rw [← hl] at h
  obtain ⟨e, he, hq⟩ := posB_sound _ _ hcL (getT_ofT _ _ (Nat.le_refl _)) [0] hcElts.E _ h c hc 0
    List.mem_cons_self
  rw [Nat.eq_of_beq_eq_true hq] at he
  obtain ⟨l, hl', hcl⟩ := List.mem_flatten.1 he
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hl'
  have hi' : i < 20 := by rw [← ch320017_nodup.1]; exact hi
  refine ⟨⟨i, hi'⟩, ?_⟩
  rw [← KF_get]
  exact hcl

theorem pk_invL_mem {l : List ℕ} (hl : l ∈ elts) : invL l ∈ elts := by
  obtain ⟨σ, -, rfl⟩ := elts_sound l hl
  have hv := VL_invL_Lst σ
  rw [mem_E_iff hv, pk_invL (VL_Lst σ)]
  have h := ch320017_inv.2
  rw [← hcElts_len] at h
  obtain ⟨e, he, hq⟩ := posB_sound _ _ hcElts.E (getT_ofT _ _ (Nat.le_refl _)) [0] hcElts.E _ h
    _ ((mem_E_iff (VL_Lst σ)).1 hl) 0 List.mem_cons_self
  rwa [← Nat.eq_of_beq_eq_true hq]

theorem invOK : InvOK := by
  intro l hl
  refine ⟨pk_invL_mem hl, ?_⟩
  obtain ⟨σ, -, rfl⟩ := elts_sound l hl
  rw [invL_Lst, ← Lst_mul, inv_mul_cancel, ← glue_idL_eq]

theorem powL_eq_iff {l m : List ℕ} (hl : VL l) (hm : VL m) (n : ℕ) :
    powL l n = m ↔ powP (pk l) n = pk m := by
  obtain ⟨e, hv⟩ := pk_powL hl n
  rw [← e]
  exact ⟨congrArg pk, VL_inj hv hm⟩

theorem ordOK : OrdOK := by
  intro j
  obtain ⟨h1, h2⟩ := ch320017_ord j
  have hr := VL_rep j
  refine ⟨(powL_eq_iff hr VL_idL _).2 ?_, fun m hm hm0 he => h2 m hm hm0 ?_⟩
  · rw [pk_rep, pk_idL]
    exact h1
  · rw [← pk_rep, ← pk_idL]
    exact (powL_eq_iff hr VL_idL _).1 he

theorem pk_z : pk (Lx zA) = hcRP.getD 1 0 := pk_Lx_z

theorem dOK : DOK := by
  intro j
  rw [ch320017_d j, powL_eq_iff (VL_rep j) (VL_Lx _), pk_rep, pk_z]

theorem repOK : RepOK := by
  refine ⟨VL_inj (VL_rep 0) VL_idL ?_, VL_inj (VL_rep 1) (VL_Lx _) ?_⟩
  · rw [pk_rep, pk_idL, idP_eq]
    rfl
  · rw [pk_rep, pk_z]
    rfl

theorem pk_conj_gen (k : Fin 5) (x : List ℕ) (hx : VL x) :
    pk (mulL (mulL (Lx (gA k)) x) (Lx (gA k)⁻¹)) = conjP (cjGP.getD (2 * k) (0, 0)) (pk x) := by
  rw [(ch320017_gp k).1, pk_mulL (VL_mulL (VL_Lx _) hx) (VL_Lx _), pk_mulL (VL_Lx _) hx]
  rfl

theorem pk_conj_gen' (k : Fin 5) (x : List ℕ) (hx : VL x) :
    pk (mulL (mulL (Lx (gA k)⁻¹) x) (Lx (gA k))) =
      conjP (cjGP.getD (2 * k + 1) (0, 0)) (pk x) := by
  rw [(ch320017_gp k).2, pk_mulL (VL_mulL (VL_Lx _) hx) (VL_Lx _), pk_mulL (VL_Lx _) hx]
  rfl

theorem clos_of (j : Fin 20) {x : ℕ} (hx : x ∈ hcF j) (i : ℕ) (hi : i < 10) :
    conjP (cjGP.getD i (0, 0)) x ∈ hcF j := by
  obtain ⟨e, he, hq⟩ := posB_sound _ _ (hcF j) (getT_ofT _ _ (Nat.le_refl _)) _ (hcF j) _
    (ch320017_clos j) x hx i (by simp; omega)
  rwa [← Nat.eq_of_beq_eq_true hq]

theorem classOK : ClassOK := by
  refine ⟨fun j => ?_, fun j p hp => ?_, fun j p hp k => ?_, fun x hx => ?_,
    fun i j hij x hi hj => ?_, fun j => ?_⟩
  · have h := ch320017_head j
    rw [← KC_map_pk] at h
    obtain ⟨q, hq, he⟩ := List.mem_map.1 h
    have hv := VL_KC j q hq
    have e1 : q.1 = hcRepL j := VL_inj hv.1 (VL_rep j) (by
      rw [pk_rep]
      exact congrArg Prod.fst he)
    have e2 : q.2 = idL := VL_inj hv.2 VL_idL (by
      rw [pk_idL]
      exact congrArg Prod.snd he)
    rw [← e1, ← e2]
    exact hq
  · obtain ⟨h1, h2⟩ := KC_mem_elts hp
    refine ⟨h1, h2, ?_⟩
    have hv := VL_KC j p hp
    rw [mulL_eq_iff hv.2 (VL_rep j) hv.1 hv.2, pk_rep]
    exact ch320017_conj j (pk p.1, pk p.2) (pk_mem_KC hp)
  · have hv := (VL_KC j p hp).1
    have hx : pk p.1 ∈ hcF j := (List.of_mem_zip (pk_mem_KC hp)).1
    refine ⟨(mem_KFst (VL_mulL (VL_mulL (VL_Lx _) hv) (VL_Lx _))).2 ?_,
      (mem_KFst (VL_mulL (VL_mulL (VL_Lx _) hv) (VL_Lx _))).2 ?_⟩
    · rw [pk_conj_gen k _ hv]
      exact clos_of j hx _ (by omega)
    · rw [pk_conj_gen' k _ hv]
      exact clos_of j hx _ (by omega)
  · obtain ⟨j, hj⟩ := cover _ ((mem_E_iff (VL_elts x hx)).1 hx)
    exact ⟨j, (mem_KFst (VL_elts x hx)).2 hj⟩
  · have hv := VL_KFst i x hi
    exact hcF_disj hij ((mem_KFst hv).1 hi) ((mem_KFst hv).1 hj)
  · refine ⟨List.Nodup.of_map pk ?_, ?_⟩
    · rw [KFst_map_pk]
      exact hcF_nodup j
    · rw [← List.length_map (f := pk), KFst_map_pk]
      exact (ch320017_nodup.2.2.2.2 j).1

theorem mulL_eq_iff' {a b m : List ℕ} (ha : VL a) (hb : VL b) (hm : VL m) :
    mulL a b = m ↔ mulP (pk a) (pk b) = pk m := by
  rw [← pk_mulL ha hb]
  exact ⟨congrArg pk, VL_inj (VL_mulL ha hb) hm⟩

theorem ne_iff_pk {a m : List ℕ} (ha : VL a) (hm : VL m) : a ≠ m ↔ pk a ≠ pk m :=
  ⟨fun h e => h (VL_inj ha hm e), fun h e => h (congrArg pk e)⟩

theorem filter_len_of {P : List ℕ → Bool} {Q : ℕ → Bool} (h : ∀ u ∈ elts, P u = Q (pk u)) :
    (elts.filter P).length = (hcElts.E.filter Q).length := by
  rw [← elts_map_pk_eq, List.filter_map, List.length_map]
  exact congrArg List.length (List.filter_congr h)

theorem VL_invL_rep (j : Fin 20) : VL (invL (hcRepL j)) := by
  rw [hcRepL_eq]
  exact VL_invL_Lst _

theorem ctOK : CtOK := by
  obtain ⟨h1, h2⟩ := ch320017_ct
  refine ⟨Eq.trans (filter_len_of fun u hu => ?_) h1, fun j hj => Eq.trans
    (filter_len_of fun u hu => ?_) (h2 j hj)⟩
  · have hv := VL_elts u hu
    refine decide_eq_decide.2 ?_
    rw [mulL_eq_iff' hv hv VL_idL, ne_iff_pk hv VL_idL, ne_iff_pk hv (VL_Lx _), pk_idL, pk_z]
  · have hv := VL_elts u hu
    refine decide_eq_decide.2 ?_
    rw [mulL_eq_iff' hv hv VL_idL, ne_iff_pk hv VL_idL, pk_idL,
      mulL_eq_iff hv (VL_rep j) (VL_invL_rep j) hv, pk_invL (VL_rep j), pk_rep]

theorem len_filter_zip (p : ℕ → Bool) : ∀ (a b : List ℕ), a.length = b.length →
    ((a.zip b).filter fun q => p q.1).length = (a.filter p).length
  | [], _, _ => by simp
  | _ :: _, [], h => absurd h (by simp)
  | x :: a, y :: b, h => by
    have ih := len_filter_zip p a b (by simpa using h)
    rw [List.zip_cons_cons, List.filter_cons, List.filter_cons]
    split <;> simp [ih]

theorem len_filter_pt (p q : ℕ → Bool) : ∀ (l1 l2 : List ℕ), l1.length = l2.length →
    (∀ t (h1 : t < l1.length) (h2 : t < l2.length), p l1[t] = q l2[t]) →
    (l1.filter p).length = (l2.filter q).length
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => absurd h (by simp)
  | _ :: _, [], h, _ => absurd h (by simp)
  | x :: l1, y :: l2, h, hp => by
    have ih := len_filter_pt p q l1 l2 (by simpa using h)
      (fun t h1 h2 => hp (t + 1) (by simpa using h1) (by simpa using h2))
    have h0 : p x = q y := hp 0 (by simp) (by simp)
    rw [List.filter_cons, List.filter_cons, h0]
    split <;> simp [ih]

theorem aOK : AOK := by
  intro r k j
  obtain ⟨hI, hlen, hpt⟩ := ch320017_a r k
  rw [hI] at hlen hpt
  have hr := VL_rep k
  have e1 : ((KC (hcI r)).filter fun p => decide (mulL (invL p.1) (hcRepL k) ∈ KFst j)).length =
      (((KC (hcI r)).map (F2 pk)).filter fun q =>
        decide (mulP (invP q.1) (hcRP.getD k 0) ∈ hcF j)).length := by
    rw [List.filter_map, List.length_map]
    refine congrArg List.length (List.filter_congr fun p hp => ?_)
    have hv := (VL_KC _ p hp).1
    obtain ⟨σ, -, hσ⟩ := elts_sound p.1 (KC_mem_elts hp).1
    have hvi : VL (invL p.1) := by
      rw [← hσ]
      exact VL_invL_Lst σ
    simp only [Function.comp_apply, F2]
    refine decide_eq_decide.2 ?_
    rw [mem_KFst (VL_mulL hvi hr), pk_mulL hvi hr, pk_invL hv, pk_rep]
  rw [e1, KC_map_pk,
    len_filter_zip (fun c => decide (mulP (invP c) (hcRP.getD k 0) ∈ hcF j)) _ _ (hcF_len _),
    ← ch320017_count r k j, List.count, List.countP_eq_length_filter]
  refine len_filter_pt _ _ _ _ hlen.symm (fun t h1 h2 => ?_)
  obtain ⟨hc, hd, he⟩ := hpt t h1
  rw [List.getD_eq_getElem _ _ h2] at hc hd he
  rw [List.getD_eq_getElem _ _ h1] at he
  have hy := he ▸ List.getD_eq_getElem _ (0 : ℕ) hd ▸ List.getElem_mem hd
  by_cases hcj : ((hcCj.aC.getD r []).getD k [])[t] = (j : ℕ)
  · rw [hcj] at hy
    rw [hcj, beq_self_eq_true, decide_eq_true_eq]
    exact hy
  · have hn : ¬ mulP (invP (hcF (hcI r))[t]) (hcRP.getD k 0) ∈ hcF j := fun hj =>
      hcF_disj (i := ⟨_, hc⟩) (j := j) (fun e => hcj (congrArg Fin.val e)) hy hj
    rw [beq_eq_false_iff_ne.2 hcj, decide_eq_false_iff_not]
    exact hn

theorem certificate320017_facts :
    F5Eq ∧ RepLOK ∧ KFstOK ∧ RepOK ∧ InvOK ∧ OrdOK ∧ DOK ∧ ClassOK ∧ CtOK ∧ AOK :=
  ⟨f5Eq, hcRepL_eq, KFst_eq, repOK, invOK, ordOK, dOK, classOK, ctOK, aOK⟩

end CFSG.KC.HcPack

end
