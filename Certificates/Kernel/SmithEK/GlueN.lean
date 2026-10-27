
module

public import Certificates.Kernel.SmithEK.ChecksN
public import CFSG.Certificates.Kernel.SmithEK.NSound
public import CFSG.LargeExtraspecial.SMod20CollCertBase

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE CFSG.SmithE.K CFSG.KC.Misc.O73 CFSG.KS.PK CFSG.LargeExtraspecial.SMod20
  CFSG.Sporadic.Th

theorem pnCL_eq : pn.CL = uaCo.toList := by decide +kernel

theorem uaCo_get (k : Nat) : uaCo[k]! = uaCo.toList.getD k 0 := by
  simp only [List.getD_eq_getElem?_getD, getElem!_def, Array.getElem?_toList]
  cases uaCo[k]? <;> rfl

theorem pnCP_get (k : Nat) : at' 9 pn.CP k = uaCo[k]! := by
  have h : Nat.beq pn.CP (pn.CL.foldr (fun x acc => x + 2 ^ 9 * acc) 0) = true := c21275cp_0
  have hlt : uaCo.toList.all (fun x => decide (x < 2 ^ 9)) = true := by decide +kernel
  rw [Nat.eq_of_beq_eq_true h, pnCL_eq, uaCo_get]
  exact at'_foldr 9 _ (fun x hx => of_decide_eq_true (List.all_eq_true.1 hlt x hx)) k

theorem collS2_testBit {v : Nat} (hv : v < 512) : collS2[v]! = (s2K pn.CL).testBit v := by
  apply Bool.eq_iff_iff.2
  rw [collS2_get hv, s2K_testBit, pnCL_eq]
  simp only [← uaCo_get]
  rfl

theorem beq_eq' (x y : Nat) : Nat.beq x y = (x == y) := by
  by_cases h : x = y
  · subst h
    rw [Nat.beq_refl, beq_self_eq_true]
  · rw [Bool.eq_false_iff.2 fun e => h (Nat.eq_of_beq_eq_true e), (beq_eq_false_iff_ne).2 h]

theorem ivOn_eq {x y z : Nat} (hx : x < 21) (hy : y < 21) (hz : z < 21) :
    ivOn pn.CP (s2K pn.CL) x y z = collOn collS2 x y z := by
  have e : bitK (s2K pn.CL) (Nat.xor (Nat.xor (at' 9 pn.CP x) (at' 9 pn.CP y)) (at' 9 pn.CP z)) =
      collS2[uaCo[x]! ^^^ uaCo[y]! ^^^ uaCo[z]!]! := by
    rw [collS2_testBit (uaCo_xor_lt hx hy hz), bitK_eq, pnCP_get, pnCP_get, pnCP_get]
    rfl
  unfold ivOn collOn
  rw [e]
  simp only [beq_eq']
  rfl

theorem ivP_eq {z a b : Nat} (hz : z < 21) (ha : a < 21) (hb : b < 21) :
    ivP pn.CP (s2K pn.CL) z a b = collP collS2 z a b := by
  unfold ivP collP
  rw [ivOn_eq hz ha hb]
  simp only [beq_eq']

theorem hlm : ivLm pn.CP (s2K pn.CL) pn.LI pn.LM = true := c21275lm_0

theorem hmp : ivMp pn.LM pn.MP = true := c21275mp_0

theorem ivLn_get {a b z : Nat} (ha : a < 21) (hb : b < 21) (hz : z < 21) :
    (ivLn pn.LI pn.LM a b).testBit z = collP collS2 z a b := by
  rw [(ivLm_sound hlm ha hb).2 z hz, ivP_eq hz ha hb]

theorem collSearch_lt (a b c d : Nat) : collSearch collS2 a b c d < 21 := by
  unfold collSearch
  cases h : (List.range 21).find? fun z => collQ collS2 z a b c d with
  | none => decide
  | some z => exact List.mem_range.1 (List.mem_of_find?_eq_some h)

theorem ivMeet_coll {a b c d : Nat} (ha : a < 21) (hb : b < 21) (hc : c < 21) (hd : d < 21) :
    ivMeet pn.LI pn.MP a b c d = collSearch collS2 a b c d := by
  rw [ivMeet_eq hlm hmp ha hb hc hd]
  unfold collSearch collQ
  refine congrArg (fun o => Option.getD o 0) (ivFind_congr fun z hz => ?_)
  have hz' := List.mem_range.1 hz
  rw [ivP_eq hz' ha hb, ivP_eq hz' hc hd]

@[expose] def nList (f : Nat → Nat → Nat → Nat → Nat) (y0 y1 y2 y3 y4 : Nat) : List Nat :=
  let x2 := f y0 y1 y2 y3
  let x5 := f y0 y2 y1 y3
  let x6 := f y0 y3 y1 y2
  let x7 := f y1 y3 y2 y4
  let x8 := f y0 y2 y4 x6
  let x9 := f y0 y1 y3 x8
  let x11 := f y1 y3 y2 x9
  let x16 := f y0 y2 y3 y4
  [y0, y1, x2, y4, y2, x5, x6, x7, x8, x9, y3, x11, f y0 x11 y1 y2,
    f y0 x11 y1 x8, f y0 y3 y1 x8, f y0 x7 y1 x8, x16,
    f y0 x7 y1 y2, f y0 x7 y1 x16, f y0 x11 y1 x16,
    f y0 y3 y1 x16]

theorem nList_congr {f g : Nat → Nat → Nat → Nat → Nat}
    (hfg : ∀ a b c d, a < 21 → b < 21 → c < 21 → d < 21 → f a b c d = g a b c d)
    (hg : ∀ a b c d, g a b c d < 21) {y0 y1 y2 y3 y4 : Nat} (h0 : y0 < 21) (h1 : y1 < 21)
    (h2 : y2 < 21) (h3 : y3 < 21) (h4 : y4 < 21) :
    nList f y0 y1 y2 y3 y4 = nList g y0 y1 y2 y3 y4 := by
  simp only [nList, hfg, hg, h0, h1, h2, h3, h4]

theorem nList_lt {y0 y1 y2 y3 y4 : Nat} (h0 : y0 < 21) (h1 : y1 < 21) (h2 : y2 < 21)
    (h3 : y3 < 21) (h4 : y4 < 21) : ∀ x ∈ nList (collSearch collS2) y0 y1 y2 y3 y4, x < 21 := by
  simp only [nList, List.forall_mem_cons, List.not_mem_nil, collSearch_lt, h0, h1, h2, h3, h4,
    IsEmpty.forall_iff, implies_true, and_self]

theorem ivList_eq {y0 y1 y2 y3 y4 : Nat} (h0 : y0 < 21) (h1 : y1 < 21) (h2 : y2 < 21)
    (h3 : y3 < 21) (h4 : y4 < 21) :
    ivList pn.LI pn.MP y0 y1 y2 y3 y4 = nList (collSearch collS2) y0 y1 y2 y3 y4 :=
  nList_congr (fun _ _ _ _ ha hb hc hd => ivMeet_coll ha hb hc hd) collSearch_lt h0 h1 h2 h3 h4

theorem toArray_get (l : List Nat) (k : Nat) : l.toArray[k]! = l.getD k 0 := by
  simp [List.getElem!_toArray, List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]

theorem collInit_eq (y0 y1 y2 y3 y4 : Nat) : collInit #[y0, y1, y2, y3, y4] =
    #[y0, y1, 0, y4, y2, 0, 0, 0, 0, 0, y3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  unfold collInit
  apply Array.ext'
  simp [List.ofFn_succ]

theorem collStep_toArray (M : Array Nat) (l : List Nat) (st : Nat × Nat × Nat × Nat × Nat) :
    collStep M l.toArray st = (l.set st.1 (M[l.getD st.2.1 0 * 9261 + l.getD st.2.2.1 0 * 441 +
      l.getD st.2.2.2.1 0 * 21 + l.getD st.2.2.2.2 0]!)).toArray := by
  unfold collStep
  rw [toArray_get l, toArray_get l, toArray_get l, toArray_get l]
  apply Array.ext'
  simp [Array.set!_eq_setIfInBounds]

theorem collCon_nList (M : Array Nat) (y0 y1 y2 y3 y4 : Nat) :
    collCon M #[y0, y1, y2, y3, y4] =
      (nList (fun a b c d => M[a * 9261 + b * 441 + c * 21 + d]!) y0 y1 y2 y3 y4).toArray := by
  unfold collCon
  rw [collInit_eq]
  simp only [collSteps, List.foldl_cons, List.foldl_nil, collStep_toArray, List.getD_cons_succ,
    List.getD_cons_zero, List.set_cons_succ, List.set_cons_zero]
  rfl

theorem collCon_eq_ivList {y0 y1 y2 y3 y4 : Nat} (h0 : y0 < 21) (h1 : y1 < 21) (h2 : y2 < 21)
    (h3 : y3 < 21) (h4 : y4 < 21) :
    collCon (collMeet collS2) #[y0, y1, y2, y3, y4] =
      (ivList pn.LI pn.MP y0 y1 y2 y3 y4).toArray := by
  rw [collCon_nList, ivList_eq h0 h1 h2 h3 h4,
    nList_congr (fun _ _ _ _ ha hb hc hd => collMeet_get ha hb hc hd) collSearch_lt h0 h1 h2 h3 h4]

theorem tbXor (a b i : Nat) : (Nat.xor a b).testBit i = (a.testBit i ^^ b.testBit i) :=
  Nat.testBit_xor a b i

theorem tbOr (a b i : Nat) : (Nat.lor a b).testBit i = (a.testBit i || b.testBit i) :=
  Nat.testBit_or a b i

theorem tbAnd (a b i : Nat) : (Nat.land a b).testBit i = (a.testBit i && b.testBit i) :=
  Nat.testBit_and a b i

theorem tbShl (a i : Nat) : (Nat.shiftLeft 1 a).testBit i = decide (a = i) := by
  change (1 <<< a).testBit i = _
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem tbAll {i : Nat} (hi : i < 21) : ivAll.testBit i = true := by
  have e : ivAll = 2 ^ 21 - 1 := by decide
  rw [e, Nat.testBit_two_pow_sub_one, decide_eq_true hi]

theorem frame_iff {y0 y1 y2 y3 y4 : Nat} (h0 : y0 < 21) (h1 : y1 < 21) (h2 : y2 < 21)
    (h3 : y3 < 21) (h4 : y4 < 21) :
    ((Nat.xor ivAll (Nat.shiftLeft 1 y0)).testBit y1 = true ∧
      (Nat.xor ivAll (ivLn pn.LI pn.LM y0 y1)).testBit y2 = true ∧
      (Nat.xor ivAll (Nat.lor (ivLn pn.LI pn.LM y0 y1)
        (Nat.lor (ivLn pn.LI pn.LM y0 y2) (ivLn pn.LI pn.LM y1 y2)))).testBit y3 = true ∧
      (Nat.land (Nat.xor (ivLn pn.LI pn.LM y0 y1) (Nat.lor (Nat.shiftLeft 1 y0)
        (Nat.shiftLeft 1 y1))) (Nat.xor ivAll (ivLn pn.LI pn.LM y2 y3))).testBit y4 = true) ↔
      collFrame collS2 y0 y1 y2 y3 y4 = true := by
  simp only [tbXor, tbOr, tbAnd, tbShl, tbAll h1, tbAll h2, tbAll h3, tbAll h4,
    ivLn_get h0 h1 h2, ivLn_get h0 h1 h3, ivLn_get h0 h2 h3, ivLn_get h1 h2 h3,
    ivLn_get h0 h1 h4, ivLn_get h2 h3 h4]
  unfold collFrame
  have hP : collP collS2 y4 y0 y1 = (y4 == y0 || y4 == y1 || collOn collS2 y4 y0 y1) := rfl
  have bd : ∀ a b : Nat, (a == b) = decide (a = b) := fun a b => by
    by_cases h : a = b <;> simp [h]
  have dc : ∀ a b : Nat, decide (a = b) = decide (b = a) := fun a b => by
    by_cases h : a = b <;> simp [h, eq_comm]
  rw [hP]
  simp only [bne, bd]
  rw [dc y0 y4, dc y1 y4]
  generalize decide (y0 = y1) = d01
  generalize decide (y4 = y0) = d40
  generalize decide (y4 = y1) = d41
  generalize collP collS2 y2 y0 y1 = p2
  generalize collP collS2 y3 y0 y1 = p3a
  generalize collP collS2 y3 y0 y2 = p3b
  generalize collP collS2 y3 y1 y2 = p3c
  generalize collOn collS2 y4 y0 y1 = o4
  generalize collP collS2 y4 y2 y3 = q4
  revert d01 d40 d41 p2 p3a p3b p3c o4 q4
  decide

theorem ivAmat_eq {l : List Nat} (hlt : ∀ x ∈ l, x < 21) (a : Nat) :
    ivAmat pn.CP (ivPack l) a = collAmat l.toArray a := by
  have hp : ∀ k, at' 5 (ivPack l) k = l.getD k 0 :=
    at'_ivPack fun x hx => by have := hlt x hx; omega
  have key : ∀ n, Nat.rec (motive := fun _ => Nat) 0 (fun j acc => Nat.xor acc
      (bif bitK a j then at' 9 pn.CP (at' 5 (ivPack l) j) else 0)) n = collAmatN l.toArray a n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      change Nat.xor (Nat.rec (motive := fun _ => Nat) 0 (fun j acc => Nat.xor acc
        (bif bitK a j then at' 9 pn.CP (at' 5 (ivPack l) j) else 0)) n)
        (bif bitK a n then at' 9 pn.CP (at' 5 (ivPack l) n) else 0) = _
      rw [ih, collAmatN, bitK_eq, hp, pnCP_get, toArray_get l n]
      cases a.testBit n <;> rfl
  exact key 9

theorem test_eq {l : List Nat} (hlen : l.length = 21) (hlt : ∀ x ∈ l, x < 21) :
    (ivBack l && ivInv pn.CP (ivPack l)) =
      (collComp l.toArray l.toArray == collId && l.toArray != collId && collAdm l.toArray) := by
  have hlt' : ∀ k < 21, l.getD k 0 < 21 := fun k hk => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact hlt _ (List.getElem_mem _)
  have hsz : l.toArray.size = 21 := by simp [hlen]
  have hinv : collComp l.toArray l.toArray = collId ↔ ∀ k < 21, l.getD (l.getD k 0) 0 = k := by
    rw [collComp_eq_collId]
    simp only [toArray_get l]
  have hid : l.toArray ≠ collId ↔ ∃ k < 21, l.getD k 0 ≠ k := by
    constructor
    · intro hne
      refine Classical.byContradiction fun h => hne ?_
      refine array_ext_getElem! hsz (by simp [collId]) fun k hk => ?_
      rw [toArray_get, collId_get hk]
      exact Classical.byContradiction fun h' => h ⟨k, hk, h'⟩
    · rintro ⟨k, hk, hne⟩ e
      apply hne
      rw [← toArray_get, e, collId_get hk]
  have hA : ∀ k < 21, (ivAmat pn.CP (ivPack l) (at' 9 pn.CP k) = at' 9 pn.CP (l.getD k 0) ↔
      collAmat l.toArray uaCo[k]! = uaCo[l.getD k 0]!) := fun k _ => by
    rw [ivAmat_eq hlt, pnCP_get, pnCP_get]
  apply Bool.eq_iff_iff.2
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne]
  constructor
  · rintro ⟨-, hi⟩
    obtain ⟨h1, h2, h3⟩ := (ivInv_iff hlt).1 hi
    refine ⟨⟨hinv.2 h1, hid.2 h2⟩, ?_⟩
    unfold collAdm
    simp only [Bool.and_eq_true, beq_iff_eq, allIn_eq_true, decide_eq_true_eq, Bool.or_eq_true,
      bne_iff_ne, toArray_get l]
    refine ⟨⟨⟨hsz, fun k _ hk => hlt' k hk⟩, fun k _ hk m _ hm => ?_⟩,
      fun k _ hk => (hA k hk).1 (h3 k hk)⟩
    by_cases e : k = m
    · exact Or.inl e
    · exact Or.inr fun he => e (by rw [← h1 k hk, he, h1 m hm])
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have h1' := hinv.1 h1
    obtain ⟨-, -, -, hA'⟩ := collAdm_parts h3
    refine ⟨ivBack_of_inv h1', (ivInv_iff hlt).2 ⟨h1', hid.1 h2, fun k hk => (hA k hk).2 ?_⟩⟩
    rw [← toArray_get l k]
    exact hA' k hk

theorem grp_eq : ∀ y0 < 21, ivGrp pn.CP pn.LI pn.LM pn.MP y0 [] = pn.R.getD y0 [] := by
  intro y0 hy
  suffices h : CFSG.KC.Misc.eqLN (ivGrp pn.CP pn.LI pn.LM pn.MP y0 []) (pn.R.getD y0 []) = true by
    rw [eqLN_eq] at h
    exact of_decide_eq_true h
  match y0, hy with
  | 0, _ => exact c21275grp_0
  | 1, _ => exact c21275grp_1
  | 2, _ => exact c21275grp_2
  | 3, _ => exact c21275grp_3
  | 4, _ => exact c21275grp_4
  | 5, _ => exact c21275grp_5
  | 6, _ => exact c21275grp_6
  | 7, _ => exact c21275grp_7
  | 8, _ => exact c21275grp_8
  | 9, _ => exact c21275grp_9
  | 10, _ => exact c21275grp_10
  | 11, _ => exact c21275grp_11
  | 12, _ => exact c21275grp_12
  | 13, _ => exact c21275grp_13
  | 14, _ => exact c21275grp_14
  | 15, _ => exact c21275grp_15
  | 16, _ => exact c21275grp_16
  | 17, _ => exact c21275grp_17
  | 18, _ => exact c21275grp_18
  | 19, _ => exact c21275grp_19
  | 20, _ => exact c21275grp_20
  | n + 21, h => omega

theorem flatMap_congr' {α β : Type} {f g : α → List β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h x List.mem_cons_self,
      flatMap_congr' fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem ite_flatMap {α β : Type} (c : Prop) [Decidable c] (l : List α) (f : α → List β) :
    (if c then l.flatMap f else []) = l.flatMap fun x => if c then f x else [] := by
  split <;> simp

theorem filterMap_eq_flatMap' {α β : Type} (f : α → Option β) :
    ∀ l : List α, l.filterMap f = l.flatMap fun x => (f x).toList
  | [] => rfl
  | x :: l => by
    rw [List.filterMap_cons, List.flatMap_cons, filterMap_eq_flatMap' f l]
    cases f x <;> rfl

theorem collInvs_eq : collInvs collS2 (collMeet collS2) =
    ((List.range 21).flatMap fun y0 => (pn.R.getD y0 []).map ivUnpack).toArray := by
  unfold collInvs collDom
  refine congrArg List.toArray ?_
  simp only [List.filterMap_flatMap]
  simp only [List.filterMap_filterMap]
  simp only [filterMap_eq_flatMap']
  apply flatMap_congr'
  intro y0 hy0
  have h0 := List.mem_range.1 hy0
  rw [← grp_eq y0 h0, ivGrp_eq]
  simp only [ite_flatMap, List.map_flatMap]
  refine flatMap_congr' fun y1 hy1 => flatMap_congr' fun y2 hy2 => flatMap_congr' fun y3 hy3 =>
    flatMap_congr' fun y4 hy4 => ?_
  have h1 := List.mem_range.1 hy1
  have h2 := List.mem_range.1 hy2
  have h3 := List.mem_range.1 hy3
  have h4 := List.mem_range.1 hy4
  have hf := frame_iff h0 h1 h2 h3 h4
  by_cases hfr : collFrame collS2 y0 y1 y2 y3 y4 = true
  · obtain ⟨c1, c2, c3, c4⟩ := hf.2 hfr
    have hl := ivList_eq h0 h1 h2 h3 h4
    have hlt := nList_lt h0 h1 h2 h3 h4
    rw [← hl] at hlt
    have hlen : (ivList pn.LI pn.MP y0 y1 y2 y3 y4).length = 21 := rfl
    rw [if_pos c1, if_pos c2, if_pos c3, if_pos c4, if_pos hfr, Option.bind_some]
    simp only [collCon_eq_ivList h0 h1 h2 h3 h4]
    rw [← test_eq hlen hlt]
    by_cases hb : (ivBack (ivList pn.LI pn.MP y0 y1 y2 y3 y4) &&
        ivInv pn.CP (ivPack (ivList pn.LI pn.MP y0 y1 y2 y3 y4))) = true
    · rw [if_pos hb, if_pos hb, List.map_cons, List.map_nil,
        ivUnpack_ivPack hlen fun x hx => by have := hlt x hx; omega]
      rfl
    · rw [if_neg hb, if_neg hb]
      rfl
  · have hn := fun h => hfr (hf.1 h)
    rw [if_neg hfr]
    change [] = _
    split_ifs with c1 c2 c3 c4 <;> first | rfl | exact absurd ⟨c1, c2, c3, c4⟩ hn

end CertificateChecks.KernelSmithEK
