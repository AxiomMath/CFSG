module

public import Certificates.Kernel.EvenSporSuz.SylowBind25002
public import Certificates.Kernel.EvenSporSuz.Sylow25002
public import Certificates.Kernel.EvenSporSuz.Bridge
public import CFSG.Certificates.Kernel.EvenSporSuz.LaneSound
public import CFSG.Certificates.Kernel.EvenSporSuz.SylowSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.Lhat
import all CFSG.Certificates.Kernel.EvenSporSuz.SylowSound
import all Init.Data.List.SplitOn.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.InnerAbs

public section

namespace CertificateChecks.KernelSyl25002

open CFSG.KC.EvenSporSuz CFSG.KC.EvenSporSuz.Syl CFSG.KC.Misc.G24 CFSG.KC.Misc.Spec
  CertificateChecks.KernelSuz CFSG.EvenSporadicStandard.TwoSuz

theorem lanesL_eq : ∀ l : List ℕ, lanesL l = lanes l.length (fun t => l.getD t 0)
  | [] => by simp [lanesL, lanes]
  | a :: l => by
    have h : ∀ t, l.getD t 0 * 2 ^ (8 * (t + 1)) = 256 * (l.getD t 0 * 2 ^ (8 * t)) := fun t => by
      rw [Nat.mul_succ, pow_add]
      ring
    rw [lanesL, lanesL_eq l, lanes, lanes, List.length_cons, Finset.sum_range_succ',
      Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, h, Nat.mul_zero, pow_zero, Nat.mul_one]
    omega

theorem lanesMt_toArray {l : List ℕ} (hl : l.length = 144) : lanesMt l.toArray = lanesL l := by
  rw [lanesL_eq, hl, lanesMt]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem aL_eq : aL = lanesMt matA := by
  have h := inputs.2.2.2.2.2.2.2.2.1
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rw [aL, matA_eq, lanesMt_toArray h.1]

theorem bL_eq : bL = lanesMt matB := by
  have h := inputs.2.2.2.2.2.2.2.2.2
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rw [bL, matB_eq, lanesMt_toArray h.1]

theorem lanes_getD (a : Array Mt) (i : ℕ) :
    (a.toList.map lanesMt).getD i one3 = lanesMt (a.getD i oneM) := by
  rw [← lanesMt_oneM, List.getD_map, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD,
    Array.getElem?_toList]

theorem lanes_letter (G : GenSys) (c : ℕ) :
    (bif Nat.beq (c % 2) 0 then (G.mats.toList.map lanesMt).getD (c / 2) one3
      else (G.invs.toList.map lanesMt).getD (c / 2) one3) = lanesMt (G.letter c) := by
  rcases Nat.mod_two_eq_zero_or_one c with h | h
  · have hb : Nat.beq (c % 2) 0 = true := by rw [h]; rfl
    rw [hb, cond_true, lanes_getD, GenSys.letter, if_pos h]
  · have hb : Nat.beq (c % 2) 0 = false := by rw [h]; rfl
    rw [hb, cond_false, lanes_getD, GenSys.letter, if_neg (by omega)]

theorem foldl_hom {α β γ : Type} (F : β → γ → β) (G : α → γ → α) (φ : α → β) (P : α → Prop)
    (hP : ∀ a c, P a → P (G a c)) (h : ∀ a c, P a → F (φ a) c = φ (G a c)) :
    ∀ (w : List γ) (a : α), P a → w.foldl F (φ a) = φ (w.foldl G a)
  | [], _, _ => rfl
  | c :: w, a, ha => by
    rw [List.foldl_cons, List.foldl_cons, h a c ha]
    exact foldl_hom F G φ P hP h w _ (hP a c ha)

theorem evalL_eq {G : GenSys} (hG : CanonGS G) (w : List ℕ) :
    evalL (G.mats.toList.map lanesMt) (G.invs.toList.map lanesMt) w = lanesMt (G.eval w) := by
  unfold evalL GenSys.eval
  have h := foldl_hom (fun a c => mulF3 a (bif Nat.beq (c % 2) 0 then
      (G.mats.toList.map lanesMt).getD (c / 2) one3
      else (G.invs.toList.map lanesMt).getD (c / 2) one3))
    (fun a c => mulM a (G.letter c)) lanesMt (fun a => canonB a = true)
    (fun a c _ => canonB_mulM a (G.letter c))
    (fun a c ha => by
      beta_reduce
      rw [lanes_letter, mulF3_lanesMt ha (CFSG.KC.EvenSporSuz.canonB_letter hG c)])
    w oneM canonB_oneM
  rw [lanesMt_oneM] at h
  exact h

theorem abL_eq : abL = abGS.mats.toList.map lanesMt := by
  have hA := KernelSuz.hA
  have hB := KernelSuz.hB
  simp only [abL, abGS, matA2, matA3, matB2, List.toList_toArray, List.map_cons, List.map_nil,
    aL_eq, bL_eq, mulF3_lanesMt hA hA, mulF3_lanesMt (canonB_mulM _ _) hA, mulF3_lanesMt hB hB]

theorem abiL_eq : abiL = abGS.invs.toList.map lanesMt := by
  have hA := KernelSuz.hA
  have hB := KernelSuz.hB
  simp only [abiL, abGS, matA2, matA3, matB2, List.toList_toArray, List.map_cons, List.map_nil,
    aL_eq, bL_eq, mulF3_lanesMt hA hA, mulF3_lanesMt (canonB_mulM _ _) hA, mulF3_lanesMt hB hB]

theorem jMats_getD' (k : ℕ) : jMats.getD k oneM = abGS.eval (jWords.getD k []) := by
  rw [jMats, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getD_eq_getElem?_getD]
  rcases h : jWords[k]? with _ | w
  · simp [GenSys.eval]
  · simp

theorem bindG_all : ∀ k < 4, bindG k = true := by
  intro k hk
  interval_cases k
  exacts [bindG250020, bindG250021, bindG250022, bindG250023]

theorem jW_getD {k : ℕ} (hk : k < 4) : jW.getD k [] = (natsK (swL (k + 1))).map (2 * ·) := by
  rw [jW, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega)]
  simp [hk]

theorem gs_getD {k : ℕ} (hk : k < 4) : gs.getD k 0 = lanesMt (jMats.getD k oneM) := by
  have h := bindG_all k hk
  simp only [bindG, Nat.beq_eq] at h
  rw [h, abL_eq, abiL_eq, evalL_eq abCanon, jMats_getD', jWords_eq, jW_getD hk]

theorem jv : jGS.valid = true := by
  have h := jCheck_true
  simp only [jCheck, Bool.and_eq_true] at h
  exact h.1.1.1.1.1.2

theorem abv : abGS.valid = true := by
  have h := jCheck_true
  simp only [jCheck, Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1

theorem chunks : ∀ c < 16, chunkK (treeOf ed) (treeOf od) gs gi z x1 x2 ed sz s1 s2 c = true := by
  intro c hc
  interval_cases c
  exacts [ch250020, ch250021, ch250022, ch250023, ch250024, ch250025, ch250026, ch250027,
    ch250028, ch250029, ch2500210, ch2500211, ch2500212, ch2500213, ch2500214, ch2500215]

theorem facts : SylFacts gs gi z x1 x2 r c tg ed od := syl_sound glob_true chunks orb_true

theorem gensOK : ∀ k < 4, Canon3 (gs.getD k 0) ∧ Canon3 (gi.getD k 0) ∧
    pkMat3 (gs.getD k 0) * pkMat3 (gi.getD k 0) = 1 := by
  have h := facts.gens
  unfold GensOK at h
  exact h

theorem canon3_gs {k : ℕ} (hk : k < 4) : Canon3 (gs.getD k 0) := (gensOK k hk).1

theorem gi_getD {k : ℕ} (hk : k < 4) : gi.getD k 0 = lanesMt (jGS.invs.getD k oneM) := by
  obtain ⟨hg, hgi, hm⟩ := gensOK k hk
  have hc : canonB (jGS.invs.getD k oneM) = true := jCanon.2 k
  have hcA : canonB (jMats.getD k oneM) = true := jCanon.1 k
  obtain ⟨h1, h2⟩ := GenSys.valid_pair jGS jv k
  refine canon3_inj hgi (canon3_lanesMt hc) ?_
  rw [gs_getD hk, pkMat3_lanesMt hcA] at hm
  have e2 : ofMt (jGS.invs.getD k oneM) * ofMt (jMats.getD k oneM) = 1 := by
    rw [← ofMt_mulM, ← ofMt_oneM]
    exact congrArg ofMt h2
  rw [pkMat3_lanesMt hc]
  calc pkMat3 (gi.getD k 0)
      = ofMt (jGS.invs.getD k oneM) * ofMt (jMats.getD k oneM) * pkMat3 (gi.getD k 0) := by
        rw [e2, Matrix.one_mul]
    _ = ofMt (jGS.invs.getD k oneM) := by rw [Matrix.mul_assoc, hm, Matrix.mul_one]

theorem gs_length : gs.length = 4 := by
  have h := glob_true
  simp only [globK, Bool.and_eq_true, Nat.beq_eq] at h
  exact h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1

theorem gi_length : gi.length = 4 := by
  have h := glob_true
  simp only [globK, Bool.and_eq_true, Nat.beq_eq] at h
  exact h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2

theorem jGS_mats' : jGS.mats = jMats := rfl

theorem getD_indep {l : List ℕ} {i : ℕ} (h : i < l.length) (a b : ℕ) : l.getD i a = l.getD i b := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem evalL_congr {M I M' I' : List ℕ} : ∀ (w : List ℕ) (acc : ℕ),
    (∀ c ∈ w, M.getD (c / 2) one3 = M'.getD (c / 2) one3 ∧
      I.getD (c / 2) one3 = I'.getD (c / 2) one3) →
    w.foldl (fun a c => mulF3 a (bif Nat.beq (c % 2) 0 then M.getD (c / 2) one3
      else I.getD (c / 2) one3)) acc =
    w.foldl (fun a c => mulF3 a (bif Nat.beq (c % 2) 0 then M'.getD (c / 2) one3
      else I'.getD (c / 2) one3)) acc
  | [], _, _ => rfl
  | c :: w, acc, h => by
    rw [List.foldl_cons, List.foldl_cons, (h c (by simp)).1, (h c (by simp)).2]
    exact evalL_congr w _ fun d hd => h d (by simp [hd])

theorem evalL_gs {w : List ℕ} (hw : lettersLt 4 w = true) :
    evalL gs gi w = lanesMt (jGS.eval w) := by
  rw [← evalL_eq jCanon]
  unfold evalL
  refine evalL_congr w one3 fun c hc => ?_
  simp only [lettersLt, List.all_eq_true, decide_eq_true_eq] at hw
  have hk := hw c hc
  rw [lanes_getD, lanes_getD, jGS_mats', ← gs_getD hk, ← gi_getD hk]
  exact ⟨getD_indep (by rw [gs_length]; exact hk) _ _, getD_indep (by rw [gi_length]; exact hk) _ _⟩

theorem letters_x : (lettersLt 4 (lettersK (swL 5)) && lettersLt 4 (lettersK (swL 6))) = true := by
  decide +kernel

theorem x1_eq : x1 = lanesMt x1M := by
  have h := bindX_true
  simp only [bindX, Bool.and_eq_true, Nat.beq_eq] at h
  have hl := letters_x
  simp only [Bool.and_eq_true] at hl
  rw [h.1.1.2, x1M, wx1_eq, evalL_gs hl.1]

theorem x2_eq : x2 = lanesMt x2M := by
  have h := bindX_true
  simp only [bindX, Bool.and_eq_true, Nat.beq_eq] at h
  have hl := letters_x
  simp only [Bool.and_eq_true] at hl
  rw [h.1.2, x2M, wx2_eq, evalL_gs hl.2]

theorem pkMat3_x1 : pkMat3 x1 = ofMt x1M := by
  rw [x1_eq, x1M, pkMat3_lanesMt (CFSG.KC.EvenSporSuz.canonB_eval _ _)]

theorem pkMat3_x2 : pkMat3 x2 = ofMt x2M := by
  rw [x2_eq, x2M, pkMat3_lanesMt (CFSG.KC.EvenSporSuz.canonB_eval _ _)]

theorem pkMat3_z : pkMat3 z = -1 := by
  rw [facts.zneg, one3_eq, lanes, Finset.mul_sum]
  have hp : ∀ t < 144, 2 * (if t / 12 = t % 12 then 1 else 0) < 3 := fun t _ => by
    split <;> omega
  have e : ∑ t ∈ Finset.range 144, 2 * ((if t / 12 = t % 12 then 1 else 0) * 2 ^ (8 * t)) =
      lanes 144 (fun t => 2 * (if t / 12 = t % 12 then 1 else 0)) := by
    unfold lanes
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [e]
  ext i j
  rw [pkMat3_lanes hp, Matrix.neg_apply, Matrix.one_apply]
  have e1 : (12 * i.val + j.val) / 12 = i.val := by omega
  have e2 : (12 * i.val + j.val) % 12 = j.val := by omega
  rw [e1, e2]
  by_cases h : i = j
  · subst h
    simp only [if_true]
    decide
  · have h' : ¬ i.val = j.val := fun e => h (Fin.ext e)
    simp [h, h'] <;> rfl

noncomputable abbrev sylS : Subgroup GL12 :=
  Subgroup.closure {u | ∃ k < 4, vm u = ofMt (jMats.getD k oneM)}

theorem pkMat3_gs {k : ℕ} (hk : k < 4) : pkMat3 (gs.getD k 0) = ofMt (jMats.getD k oneM) := by
  rw [gs_getD hk]
  exact pkMat3_lanesMt (jCanon.1 k)

theorem vm_letterU_two (k : ℕ) : vm (jGS.letterU jv (2 * k)) = ofMt (jMats.getD k oneM) := by
  have e : 2 * k / 2 = k := Nat.mul_div_cancel_left k (by norm_num)
  have h := GenSys.val_letterU jGS jv (2 * k)
  rw [GenSys.letter, if_pos (by omega), e] at h
  exact h

theorem gen_unit {k : ℕ} (hk : k < 4) : ∃ u ∈ sylS, vm u = ofMt (jMats.getD k oneM) :=
  ⟨jGS.letterU jv (2 * k), Subgroup.subset_closure ⟨k, hk, vm_letterU_two k⟩, vm_letterU_two k⟩

theorem monG_sub : ∀ m ∈ monG gs, ∃ u ∈ sylS, vm u = m := by
  intro m hm
  induction hm using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    beta_reduce
    rw [pkMat3_gs k.isLt]
    exact gen_unit k.isLt
  | one => exact ⟨1, one_mem _, rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨v, hv, rfl⟩ := hy
    exact ⟨u * v, mul_mem hu hv, rfl⟩

theorem rmul : ∀ m ∈ monG gs, ∀ p ∈ ed, ∃ q ∈ ed, pkMat3 q.1 = pkMat3 p.1 * m := by
  intro m hm
  induction hm using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    intro p hp
    obtain ⟨v, hv⟩ := facts.closed p hp k k.isLt
    exact ⟨_, hv, (canon3_mulF3 (facts.mem p hp).1 (canon3_gs k.isLt)).2⟩
  | one => exact fun p hp => ⟨p, hp, (Matrix.mul_one _).symm⟩
  | mul x y _ _ hx hy =>
    intro p hp
    obtain ⟨q, hq, hqe⟩ := hx p hp
    obtain ⟨r, hr, hre⟩ := hy q hq
    exact ⟨r, hr, by rw [hre, hqe, Matrix.mul_assoc]⟩

theorem one_mem_ed : ∃ p ∈ ed, pkMat3 p.1 = 1 := by
  obtain ⟨p, hp, he⟩ := facts.one
  exact ⟨p, hp, by rw [he, canon3_one3.2]⟩

theorem enum_back {p : ℕ × ℕ} (hp : p ∈ ed) : ∃ u ∈ sylS, vm u = pkMat3 p.1 :=
  monG_sub _ (facts.mem p hp).2

theorem enum_fwd {u : GL12} (hu : u ∈ sylS) : ∃ p ∈ ed, pkMat3 p.1 = vm u := by
  have step : ∀ x y : GL12, (∃ p ∈ ed, pkMat3 p.1 = vm x) → (∃ p ∈ ed, pkMat3 p.1 = vm y) →
      ∃ p ∈ ed, pkMat3 p.1 = vm (x * y) := by
    rintro x y ⟨p, hp, hpx⟩ ⟨q, hq, hqy⟩
    obtain ⟨r, hr, hre⟩ := rmul _ (facts.mem q hq).2 p hp
    exact ⟨r, hr, by rw [hre, hpx, hqy, vm_mul]⟩
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk, hxk⟩ := hx
    obtain ⟨p, hp, hp1⟩ := one_mem_ed
    obtain ⟨q, hq, hqe⟩ := rmul _ (gen_mem hk) p hp
    exact ⟨q, hq, by rw [hqe, hp1, Matrix.one_mul, pkMat3_gs hk, hxk]⟩
  | one =>
    obtain ⟨p, hp, hp1⟩ := one_mem_ed
    exact ⟨p, hp, by rw [hp1]; rfl⟩
  | mul x y _ _ hx hy => exact step x y hx hy
  | inv x _ hx =>
    have hpow : ∀ n : ℕ, ∃ p ∈ ed, pkMat3 p.1 = vm (x ^ n) := by
      intro n
      induction n with
      | zero =>
        obtain ⟨p, hp, hp1⟩ := one_mem_ed
        exact ⟨p, hp, by rw [hp1, pow_zero]; rfl⟩
      | succ n ih => rw [pow_succ]; exact step _ _ ih hx
    have hpos := orderOf_pos x
    have e : x ^ (orderOf x - 1) = x⁻¹ := eq_inv_of_mul_eq_one_left (by
      rw [← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one])
    rw [← e]
    exact hpow _

theorem inj_ed {p q : ℕ × ℕ} (hp : p ∈ ed) (hq : q ∈ ed) (h : pkMat3 p.1 = pkMat3 q.1) :
    p = q :=
  List.inj_on_of_nodup_map facts.nodup hp hq
    (canon3_inj (facts.mem p hp).1 (facts.mem q hq).1 h)

theorem ncard_eq (Q : GL12 → Prop) (P : ℕ × ℕ → Bool)
    (hQP : ∀ p ∈ ed, ∀ w : GL12, pkMat3 p.1 = vm w → (Q w ↔ P p = true)) :
    Set.ncard {w | w ∈ sylS ∧ Q w} = ed.countP P := by
  rw [← Set.ncard_image_of_injective _ (fun a b (h : vm a = vm b) => vm_inj h)]
  have himg : vm '' {w | w ∈ sylS ∧ Q w} =
      (fun p : ℕ × ℕ => pkMat3 p.1) '' ((ed.filter P).toFinset : Set (ℕ × ℕ)) := by
    ext M
    simp only [Set.mem_image, Set.mem_setOf_eq, List.coe_toFinset, List.mem_filter]
    constructor
    · rintro ⟨w, ⟨hw, hq⟩, rfl⟩
      obtain ⟨p, hp, hpw⟩ := enum_fwd hw
      exact ⟨p, ⟨hp, (hQP p hp w hpw).1 hq⟩, hpw⟩
    · rintro ⟨p, ⟨hp, hP⟩, rfl⟩
      obtain ⟨u, hu, hue⟩ := enum_back hp
      exact ⟨u, ⟨hu, (hQP p hp u hue.symm).2 hP⟩, hue⟩
  rw [himg, Set.InjOn.ncard_image, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup ((facts.nodup.of_map _).filter _), List.countP_eq_length_filter]
  intro p hp q hq h
  simp only [List.coe_toFinset, List.mem_filter, Set.mem_setOf_eq] at hp hq
  exact inj_ed hp.1 hq.1 h

theorem card_sylS : Nat.card sylS = 2 ^ 14 := by
  have h := ncard_eq (fun _ => True) (fun _ => true) (fun _ _ _ _ => by simp)
  rw [List.countP_true, facts.len] at h
  have e : {w | w ∈ sylS ∧ True} = (sylS : Set GL12) := by
    ext w
    simp
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, ← e]
  exact h.trans (by norm_num)

theorem rootCount_eq {cL : ℕ} (hc : Canon3 cL) {c : GL12} (hcv : pkMat3 cL = vm c) :
    rootCount sylS c = sqN ed cL := by
  unfold rootCount
  refine ncard_eq _ _ fun p hp w hpw => ?_
  have hm := canon3_mulF3 (facts.mem p hp).1 (facts.mem p hp).1
  simp only [decide_eq_true_eq]
  constructor
  · intro h
    refine canon3_inj hm.1 hc ?_
    rw [hm.2, hpw, hcv, ← vm_mul, h]
  · intro h
    refine vm_inj ?_
    rw [vm_mul, ← hpw, ← hcv, ← hm.2, h]

theorem mem_of_sq {cL : ℕ} {c : GL12} (hcv : pkMat3 cL = vm c) (h : 0 < sqN ed cL) : c ∈ sylS := by
  obtain ⟨p, hp, hpe⟩ := List.countP_pos_iff.1 h
  simp only [decide_eq_true_eq] at hpe
  obtain ⟨u, hu, hue⟩ := enum_back hp
  have hm := canon3_mulF3 (facts.mem p hp).1 (facts.mem p hp).1
  have : c = u * u := vm_inj (by rw [vm_mul, hue, ← hm.2, hpe, hcv])
  rw [this]
  exact mul_mem hu hu

theorem vm_negOne : vm (-1 : GL12) = -1 := by
  simp [vm] <;> rfl

theorem pkMat3_z_vm : pkMat3 z = vm (-1 : GL12) := pkMat3_z.trans vm_negOne.symm

theorem negOne_mem : (-1 : GL12) ∈ sylS :=
  mem_of_sq pkMat3_z_vm (by rw [facts.cz]; norm_num)

theorem x1_mem {u : GL12} (hu : vm u = ofMt x1M) : u ∈ sylS :=
  mem_of_sq (by rw [pkMat3_x1, hu]) (by rw [facts.c1]; norm_num)

theorem x2_mem {u : GL12} (hu : vm u = ofMt x2M) : u ∈ sylS :=
  mem_of_sq (by rw [pkMat3_x2, hu]) (by rw [facts.c2]; norm_num)

theorem rootCount_negOne : rootCount sylS (-1) = 1056 := by
  rw [rootCount_eq facts.canon.1 pkMat3_z_vm, facts.cz]

theorem rootCount_x1 {u : GL12} (hu : vm u = ofMt x1M) : rootCount sylS u = 384 := by
  rw [rootCount_eq facts.canon.2.1 (by rw [pkMat3_x1, hu]), facts.c1]

theorem rootCount_x2 {u : GL12} (hu : vm u = ofMt x2M) : rootCount sylS u = 352 := by
  rw [rootCount_eq facts.canon.2.2 (by rw [pkMat3_x2, hu]), facts.c2]

theorem ofMt_x2M : ofMt x2M = -ofMt x1M := by
  rw [← pkMat3_x2, ← pkMat3_x1, facts.x2eq,
    (canon3_mulF3 facts.canon.1 facts.canon.2.1).2, pkMat3_z]
  exact neg_one_mul _

section Cover

variable {L : Subgroup GL12} (hA : ∀ u : GL12, vm u = ofMt matA → u ∈ L)
  (hB : ∀ u : GL12, vm u = ofMt matB → u ∈ L)
include hA hB

theorem abGS_letterU_even_mem' (k : ℕ) : abGS.letterU abv (2 * k) ∈ L := by
  have hv : ∀ k, vm (abGS.letterU abv (2 * k)) = ofMt (abGS.mats.getD k oneM) := fun k => by
    rw [GenSys.vm_letterU, GenSys.letter, ite_eq_left (by omega), show 2 * k / 2 = k by omega]
  have hA0 : vm (abGS.letterU abv (2 * 0)) = ofMt matA := (hv 0).trans (by simp [abGS])
  have hB0 : vm (abGS.letterU abv (2 * 3)) = ofMt matB := (hv 3).trans (by simp [abGS])
  have hA' := hA _ hA0
  have hB' := hB _ hB0
  by_cases hk : k < 5
  · interval_cases k
    · exact hA'
    · have : abGS.letterU abv (2 * 1) = abGS.letterU abv (2 * 0) * abGS.letterU abv (2 * 0) :=
        vm_inj (by
          rw [hv, vm_mul, hA0, show abGS.mats.getD 1 oneM = matA2 by simp [abGS]]
          exact ofMt_mulM matA matA)
      rw [this]
      exact mul_mem hA' hA'
    · have : abGS.letterU abv (2 * 2) =
          abGS.letterU abv (2 * 0) * abGS.letterU abv (2 * 0) * abGS.letterU abv (2 * 0) :=
        vm_inj (by
          rw [hv, vm_mul, vm_mul, hA0, show abGS.mats.getD 2 oneM = matA3 by simp [abGS]]
          change ofMt (mulM matA2 matA) = _
          rw [ofMt_mulM]
          exact congrArg (· * ofMt matA) (ofMt_mulM matA matA))
      rw [this]
      exact mul_mem (mul_mem hA' hA') hA'
    · exact hB'
    · have : abGS.letterU abv (2 * 4) = abGS.letterU abv (2 * 3) * abGS.letterU abv (2 * 3) :=
        vm_inj (by
          rw [hv, vm_mul, hB0, show abGS.mats.getD 4 oneM = matB2 by simp [abGS]]
          exact ofMt_mulM matB matB)
      rw [this]
      exact mul_mem hB' hB'
  · have hs : abGS.mats.size = 5 ∧ abGS.invs.size = 5 := by simp [abGS]
    have h1 : abGS.mats.getD (2 * k / 2) oneM = oneM := by
      rw [show 2 * k / 2 = k by omega]
      exact getD_oneM_of_le _ (by omega)
    have h2 : abGS.invs.getD (2 * k / 2) oneM = oneM := by
      rw [show 2 * k / 2 = k by omega]
      exact getD_oneM_of_le _ (by omega)
    rw [GenSys.letterU_one abGS abv h1 h2]
    exact one_mem _

theorem abGS_evalU_mem' (w : List ℕ) : abGS.evalU abv w ∈ L := by
  unfold GenSys.evalU
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
  rcases Nat.even_or_odd' c with ⟨i, rfl | rfl⟩
  · exact abGS_letterU_even_mem' hA hB i
  · rw [GenSys.letterU_odd]
    exact inv_mem (abGS_letterU_even_mem' hA hB i)

theorem sylS_le : sylS ≤ L := by
  refine (Subgroup.closure_le _).2 ?_
  rintro u ⟨k, -, hu⟩
  have e : u = abGS.evalU abv (jWords.getD k []) :=
    vm_inj (by rw [hu, jMats_getD']; exact GenSys.ofMt_eval abGS abv _)
  rw [e]
  exact abGS_evalU_mem' hA hB _

end Cover

theorem bindR_all : ∀ k < 14, bindR k = true := by
  intro k hk
  interval_cases k
  exacts [bindR250020, bindR250021, bindR250022, bindR250023, bindR250024, bindR250025,
    bindR250026, bindR250027, bindR250028, bindR250029, bindR2500210, bindR2500211,
    bindR2500212, bindR2500213]

theorem pkMat3_conj {k : ℕ} (hk : k < 14) :
    pkMat3 (c.getD k 0) = vm (abGS.evalU abv (wordAB (swL (10 + 3 * k)))) := by
  have h := bindR_all k hk
  simp only [bindR, Bool.and_eq_true, Nat.beq_eq] at h
  rw [h.2, abL_eq, abiL_eq, evalL_eq abCanon,
    pkMat3_lanesMt (CFSG.KC.EvenSporSuz.canonB_eval _ _)]
  exact GenSys.ofMt_eval abGS abv _

theorem vm_one : vm (1 : GL12) = 1 := Units.val_one

theorem tgt_cases {k : ℕ} (hk : k < 14) :
    tgtL x1 x2 (tg.getD k 0) = x1 ∨ tgtL x1 x2 (tg.getD k 0) = x2 := by
  rcases (facts.reps k hk).2.2.1 with ht | ht
  · left
    rw [ht, tgtL, Nat.beq_refl, cond_true]
  · right
    have hb : Nat.beq 2 1 = false := rfl
    rw [ht, tgtL, hb, cond_false]

theorem cover {L : Subgroup GL12} (hA : ∀ u : GL12, vm u = ofMt matA → u ∈ L)
    (hB : ∀ u : GL12, vm u = ofMt matB → u ∈ L) {s : GL12} (hs : s ∈ sylS) (hss : s * s = 1)
    (hs1 : s ≠ 1) (hsz : s ≠ -1) :
    ∃ g ∈ L, vm (g * s * g⁻¹) = ofMt x1M ∨ vm (g * s * g⁻¹) = ofMt x2M := by
  obtain ⟨p, hp, hpv⟩ := enum_fwd hs
  have hc := (facts.mem p hp).1
  have hm := canon3_mulF3 hc hc
  have hsq : mulF3 p.1 p.1 = one3 := by
    refine canon3_inj hm.1 canon3_one3.1 ?_
    rw [hm.2, hpv, ← vm_mul, hss, canon3_one3.2, vm_one]
  have hne1 : p.1 ≠ one3 := fun h =>
    hs1 (vm_inj (by rw [← hpv, h, canon3_one3.2, vm_one]))
  have hnez : p.1 ≠ z := fun h => hsz (vm_inj (by rw [← hpv, h, pkMat3_z_vm]))
  obtain ⟨k, hk, h, hh, he⟩ := facts.cover p hp hsq hne1 hnez
  obtain ⟨hR, hC, -, hrc⟩ := facts.reps k hk
  obtain ⟨H, hHS, rfl⟩ := monG_sub h hh
  have hT : Canon3 (tgtL x1 x2 (tg.getD k 0)) := by
    rcases tgt_cases hk with e | e <;> rw [e]
    exacts [facts.canon.2.1, facts.canon.2.2]
  obtain ⟨Cu, hCv, hCL⟩ : ∃ Cu : GL12, pkMat3 (c.getD k 0) = vm Cu ∧ Cu ∈ L :=
    ⟨_, pkMat3_conj hk, abGS_evalU_mem' hA hB _⟩
  have key : vm s * vm (H * Cu) = vm (H * Cu) * pkMat3 (tgtL x1 x2 (tg.getD k 0)) := by
    rw [vm_mul, ← Matrix.mul_assoc, ← hpv, he, Matrix.mul_assoc, ← hCv,
      ← (canon3_mulF3 hR hC).2, hrc, (canon3_mulF3 hC hT).2, hCv, Matrix.mul_assoc]
  have hGL : H * Cu ∈ L := mul_mem (sylS_le hA hB hHS) hCL
  generalize H * Cu = G at key hGL
  refine ⟨G⁻¹, inv_mem hGL, ?_⟩
  have hX : vm (G⁻¹ * s * G⁻¹⁻¹) = pkMat3 (tgtL x1 x2 (tg.getD k 0)) := by
    rw [inv_inv, vm_mul, vm_mul, Matrix.mul_assoc, key, ← Matrix.mul_assoc, ← vm_mul,
      inv_mul_cancel, vm_one, Matrix.one_mul]
  rw [hX]
  rcases tgt_cases hk with e | e
  · left
    rw [e, pkMat3_x1]
  · right
    rw [e, pkMat3_x2]

end CertificateChecks.KernelSyl25002

end
