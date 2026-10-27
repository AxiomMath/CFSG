module

public import Certificates.Kernel.SporSch.Tits.Rank4193K
public import Certificates.Certificate27580
public import CFSG.Certificates.Kernel.Misc.TitsPiSound
import CFSG.Certificates.Kernel.Spor.RawSiftK

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Rank4193

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits CFSG.Certificates.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2268 CertificateChecks.KernelEvenBN
open CFSG.Quasithin.F112S

theorem sB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem mem_surv' {L : Array Level} {q : Array Nat → Bool} {x : Array Nat}
    (h : x ∈ survivors5 1755 L q) : q x = true := by
  simp only [survivors5, List.mem_flatMap, List.mem_filter, List.mem_map, List.mem_range] at h
  obtain ⟨_, _, _, _, _, _, _, _, ⟨_, _, _⟩, hq⟩ := h
  exact hq

theorem all_congr' {l : List Nat} {F G : Nat → Bool} (h : ∀ y ∈ l, F y = G y) :
    l.all F = l.all G := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.all_cons, List.all_cons, h a List.mem_cons_self,
      ih fun y hy => h y (List.mem_cons_of_mem a hy)]

theorem allN_eq_all (n : Nat) (f : Nat → Bool) : allN n f = (List.range n).all f := by
  rw [Bool.eq_iff_iff, List.all_eq_true]
  constructor
  · intro h y hy
    exact CFSG.KS.allN_spec h y (List.mem_range.1 hy)
  · intro h
    exact CFSG.KS.Raw.allN_of_forall fun y hy => h y (List.mem_range.2 hy)

theorem bIf_true (c e : Bool) : bIf(c, true, e) = (c || e) := by cases c <;> rfl

theorem bIf_true' (c t : Bool) : bIf(c, t, true) = (!c || t) := by cases c <;> rfl

theorem memB_eq (y : Nat) (l : List Nat) : memB y l = l.contains y := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    change bIf(Nat.beq y x, true, memB y l) = _
    rw [bIf_true, ih, List.contains_cons]
    cases h : Nat.beq y x
    · have : (y == x) = false := by
        rw [beq_eq_false_iff_ne]
        intro e
        rw [e, Nat.beq_refl] at h
        exact absurd h (by decide)
      rw [this]
    · have : (y == x) = true := by
        rw [beq_iff_eq]
        exact Nat.eq_of_beq_eq_true h
      rw [this]

theorem allR_eq (f : Nat → Bool) (l : List Nat) : allR f l = l.all f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    change bAnd(f x, allR f l) = _
    rw [ih, List.all_cons]
    cases f x <;> rfl

theorem forceL_eq (l : List Nat) (k : List Nat → Bool) : forceL l k = k l := by
  induction l generalizing k with
  | nil => rfl
  | cons x l ih =>
    change strictB x (fun x' => forceL l (fun xs => k (x' :: xs))) = _
    rw [sB_eq, ih]

theorem blt_eq_decide (a b : Nat) : Nat.blt a b = decide (a < b) := by
  rw [Bool.eq_iff_iff, Nat.blt_eq, decide_eq_true_iff]

theorem ble_eq_decide (a b : Nat) : Nat.ble a b = decide (a ≤ b) := by
  rw [Bool.eq_iff_iff, Nat.ble_eq, decide_eq_true_iff]

theorem searchK_eq (N : Nat) (m : Nat → Nat → Nat) :
    ∀ f sp lo, searchK N m f sp lo = search N m f sp lo := by
  intro f
  induction f with
  | zero => intro sp lo; rfl
  | succ f ih =>
    intro sp lo
    change allN N (fun y => bIf(Nat.blt y lo, true, bIf(memB y sp, true,
        bIf(allR (fun s => Nat.blt (m y s) N) sp,
          bIf(allR (fun s => Nat.ble y (m y s)) sp,
            forceL (y :: (sp ++ sp.map (m y))) (fun sp' => searchK N m f sp' (Nat.succ y)), true),
          true)))) = _
    rw [allN_eq_all, search]
    refine all_congr' fun y _ => ?_
    rw [bIf_true, bIf_true, bIf_true', bIf_true', forceL_eq, ih, allR_eq, allR_eq, memB_eq,
      blt_eq_decide]
    simp only [blt_eq_decide, ble_eq_decide, Bool.or_assoc]

theorem search_congr (N : Nat) {m m' : Nat → Nat → Nat} (hm : ∀ i < N, ∀ j < N, m i j = m' i j) :
    ∀ f sp lo, (∀ s ∈ sp, s < N) → search N m f sp lo = search N m' f sp lo := by
  intro f
  induction f with
  | zero => intro sp lo _; rfl
  | succ f ih =>
    intro sp lo hsp
    rw [search, search]
    refine all_congr' fun y hy => ?_
    have hyN := List.mem_range.1 hy
    have e1 : (sp.all fun s => decide (m y s < N)) = sp.all fun s => decide (m' y s < N) :=
      all_congr' fun s hs => by rw [hm y hyN s (hsp s hs)]
    have e2 : (sp.all fun s => decide (y ≤ m y s)) = sp.all fun s => decide (y ≤ m' y s) :=
      all_congr' fun s hs => by rw [hm y hyN s (hsp s hs)]
    rw [e1, e2]
    cases hc : sp.all fun s => decide (m' y s < N)
    · simp
    · have hlt : ∀ s ∈ sp, m' y s < N := by
        intro s hs
        simpa using List.all_eq_true.1 hc s hs
      have e3 : sp.map (m y) = sp.map (m' y) :=
        List.map_congr_left fun s hs => hm y hyN s (hsp s hs)
      rw [e3, ih]
      intro s hs
      simp only [List.mem_cons, List.mem_append, List.mem_map] at hs
      rcases hs with rfl | hs | ⟨t, ht, rfl⟩
      · exact hyN
      · exact hsp s hs
      · exact hlt t ht

@[expose] noncomputable def SL : List (Array Nat) := survivors5 1755 titsSLevels isInv

theorem invs_def : invs = SL.toArray := rfl

theorem SL_eq : SL = E32.SI.L.map (unpack 1755 11) :=
  CertificateChecks.Batch27580.sInvs_eq

theorem SL_len : SL.length = 143 := by
  rw [SL_eq, List.length_map]
  exact Nat.eq_of_beq_eq_true ch4193len

theorem numInvs_eq : numInvs = 143 := by
  rw [numInvs, invs_def, List.size_toArray, SL_len]

theorem props : (∀ x ∈ SL, isInvA 1755 x (invCand 1755 x) = true ∧
      siftA 1755 (rawLevels 1755 titsSArrs (baseArr 1755 titsSBase)) (baseArr 1755 titsSBase) 0 x =
        true) ∧
    SL.Pairwise (fun a b => eqA 1755 a b = false) :=
  surv5K_propsT isInv bindsS permS TitsS.hl

theorem invs_get {i : Nat} (hi : i < 143) : invs[i]! = SL[i]'(by rw [SL_len]; exact hi) := by
  rw [invs_def, getElem!_pos _ i (by simp [SL_len, hi]), List.getElem_toArray]

theorem invs_mem {i : Nat} (hi : i < 143) : invs[i]! ∈ SL := by
  rw [invs_get hi]
  exact List.getElem_mem _

theorem invs_IT {i : Nat} (hi : i < 143) : invs[i]! = unpack 1755 11 (IT i) := by
  have e := Nat.eq_of_beq_eq_true (allN_spec ch4193it i hi)
  have hl : i < E32.SI.L.length := by
    have := SL_len
    rw [SL_eq, List.length_map] at this
    omega
  rw [invs_get hi, e, List.getD_eq_getElem _ _ hl]
  simp only [SL_eq, List.getElem_map]

@[expose] noncomputable def sg (i : Nat) : Equiv.Perm (Fin 1755) :=
  CFSG.Monster.B.Co2.permOfArr 1755 invs[i]!

theorem rep_sg {i : Nat} (hi : i < 143) : CFSG.Monster.B.Co2.Rep 1755 invs[i]! (sg i) :=
  (CFSG.Monster.B.Co2.rep_permOfArr ((props.1 _ (invs_mem hi)).1)).1

theorem sg_sq {i : Nat} (hi : i < 143) : sg i * sg i = 1 := by
  have h2 := mem_surv' (L := titsSLevels) (q := isInv) (invs_mem hi)
  simp only [isInv, Bool.and_eq_true] at h2
  exact CFSG.Monster.B.Co2.eq_of_eqA (CFSG.Monster.B.Co2.rep_compA (rep_sg hi) (rep_sg hi))
    CFSG.Monster.B.Co2.rep_idA h2.1

theorem sg_ne_one {i : Nat} (hi : i < 143) : sg i ≠ 1 := by
  have h2 := mem_surv' (L := titsSLevels) (q := isInv) (invs_mem hi)
  simp only [isInv, Bool.and_eq_true, Bool.not_eq_true'] at h2
  intro h1
  have := (CFSG.Monster.B.Co2.eqA_iff (rep_sg hi) CFSG.Monster.B.Co2.rep_idA).2 h1
  rw [h2.2] at this
  exact Bool.false_ne_true this

theorem sg_inj {i j : Nat} (hi : i < 143) (hj : j < 143) (h : sg i = sg j) : i = j := by
  by_contra hne
  have hP := List.pairwise_iff_getElem.1 props.2
  have hl : SL.length = 143 := SL_len
  rcases Nat.lt_or_gt_of_ne hne with hij | hij
  · have := hP i j (by omega) (by omega) hij
    rw [← invs_get hi, ← invs_get hj] at this
    rw [(CFSG.Monster.B.Co2.eqA_iff (rep_sg hi) (rep_sg hj)).2 h] at this
    exact Bool.false_ne_true this.symm
  · have := hP j i (by omega) (by omega) hij
    rw [← invs_get hi, ← invs_get hj] at this
    rw [(CFSG.Monster.B.Co2.eqA_iff (rep_sg hj) (rep_sg hi)).2 h.symm] at this
    exact Bool.false_ne_true this.symm

theorem prodAt_eq' {i j : Nat} (hi : i < numInvs) (hj : j < numInvs) :
    prodAt i j = prodIdx i j := by
  unfold prodAt prodTab
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn,
    getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem exists_of_allN_false {n : Nat} {f : Nat → Bool} (h : allN n f = false) :
    ∃ i < n, f i = false := by
  by_contra hc
  have : allN n f = true := CFSG.KS.Raw.allN_of_forall fun i hi => by
    cases hf : f i
    · exact absurd ⟨i, hi, hf⟩ hc
    · rfl
  rw [h] at this
  exact absurd this (by decide)

theorem pt_IT {i x : Nat} (hi : i < 143) (hx : x < 1755) :
    pg 11 (mask 11) (IT i) x = ((sg i) ⟨x, hx⟩ : Nat) := by
  rw [← unpack_getT hx, ← invs_IT hi]
  exact (rep_sg hi).apply hx

theorem groupS : ∃ G : Subgroup (Equiv.Perm (Fin 1755)),
    (∀ i < 143, sg i ∈ G) ∧
    ∀ γ ∈ G, (∀ t < 5, ∀ h : (baseArr 1755 titsSBase)[t]! < 1755,
      γ ⟨(baseArr 1755 titsSBase)[t]!, h⟩ = ⟨(baseArr 1755 titsSBase)[t]!, h⟩) → γ = 1 := by
  obtain ⟨G, hmem, hsep⟩ := chain_group bindsS TitsS.head TitsS.hl (NS := 220) (CH := 8)
    (by norm_num) TitsS.hs CertificateChecks.Batch27580.ndS
  exact ⟨G, fun i hi => (hmem _ _ (rep_sg hi)).1 (props.1 _ (invs_mem hi)).2, hsep⟩

theorem base_eq {i j k : Nat} (hi : i < 143) (hj : j < 143) (hk : k < 143)
    (h : baseEqK (IT i) (IT j) (IT k) = true) : sg i * sg j = sg k := by
  obtain ⟨G, hG, hsep⟩ := groupS
  have hbl := CFSG.KS.Raw.Orb.base_lt_of_levels bindsS TitsS.hl
  have hBP : ∀ t < 5, (baseArr 1755 titsSBase)[t]! = pg 11 (mask 11) TitsS.BP t :=
    fun t ht => bindsS.2.2.2.2.2.2 t ht
  have hfix : ∀ t < 5, ∀ hb : (baseArr 1755 titsSBase)[t]! < 1755,
      ((sg k)⁻¹ * (sg i * sg j)) ⟨(baseArr 1755 titsSBase)[t]!, hb⟩ =
        ⟨(baseArr 1755 titsSBase)[t]!, hb⟩ := by
    intro t ht hb
    have e := allN_spec h t ht
    rw [sB_eq, ← hBP t ht, Nat.beq_eq] at e
    rw [pt_IT hj hb, pt_IT hi (sg j _).2, pt_IT hk hb] at e
    rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq, Equiv.Perm.mul_apply]
    exact Fin.ext e
  have h1 := hsep _ (G.mul_mem (G.inv_mem (hG k hk)) (G.mul_mem (hG i hi) (hG j hj))) hfix
  exact (inv_mul_eq_one.1 h1).symm

theorem moved_ne {i j : Nat} (hi : i < 143) (hj : j < 143) (h : movedK (IT i) (IT j) = true) :
    (sg i * sg j) * (sg i * sg j) ≠ 1 := by
  intro h1
  have h' : allN 1755 (fun x => Nat.beq (pg 11 (mask 11) (IT i) (pg 11 (mask 11) (IT j)
      (pg 11 (mask 11) (IT i) (pg 11 (mask 11) (IT j) x)))) x) = false := by
    cases ha : allN 1755 (fun x => Nat.beq (pg 11 (mask 11) (IT i) (pg 11 (mask 11) (IT j)
        (pg 11 (mask 11) (IT i) (pg 11 (mask 11) (IT j) x)))) x)
    · rfl
    · unfold movedK at h
      rw [ha] at h
      exact absurd h (by decide)
  obtain ⟨x, hx, hf⟩ := exists_of_allN_false h'
  have e := congrArg (fun g : Equiv.Perm (Fin 1755) => ((g ⟨x, hx⟩ : Fin 1755) : Nat)) h1
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] at e
  rw [pt_IT hj hx, pt_IT hi (sg j _).2, pt_IT hj (sg i _).2, pt_IT hi (sg j _).2, e,
    Nat.beq_refl] at hf
  exact absurd hf (by decide)

theorem find_none {p : Array Nat} {g : Equiv.Perm (Fin 1755)} (hp : CFSG.Monster.B.Co2.Rep 1755 p g)
    (hg : ∀ k < 143, sg k ≠ g) :
    ((List.range numInvs).find? fun k => eqA 1755 p invs[k]!) = none := by
  rw [List.find?_eq_none]
  intro k hk
  have hk' : k < 143 := by rw [← numInvs_eq]; exact List.mem_range.1 hk
  intro he
  exact hg k hk' ((CFSG.Monster.B.Co2.eqA_iff hp (rep_sg hk')).1 (by simpa using he)).symm

theorem find_some {p : Array Nat} {k : Nat} (hk : k < 143)
    (hp : CFSG.Monster.B.Co2.Rep 1755 p (sg k)) :
    ((List.range numInvs).find? fun k => eqA 1755 p invs[k]!) = some k := by
  rw [List.find?_eq_some_iff_getElem]
  have hkN : k < (List.range numInvs).length := by rw [List.length_range, numInvs_eq]; exact hk
  refine ⟨?_, k, hkN, by rw [List.getElem_range], fun j hj => ?_⟩
  · exact (CFSG.Monster.B.Co2.eqA_iff hp (rep_sg hk)).2 rfl
  · rw [List.getElem_range]
    have hj' : j < 143 := by omega
    have hne : eqA 1755 p invs[j]! = false := by
      cases he : eqA 1755 p invs[j]!
      · rfl
      · have := (CFSG.Monster.B.Co2.eqA_iff hp (rep_sg hj')).1 he
        exact absurd (sg_inj hk hj' this) (by omega)
    simp [hne]

theorem prodAt_eq_mulT {i j : Nat} (hi : i < 143) (hj : j < 143) : prodAt i j = mulT i j := by
  have hc := allN_spec (allN_spec (show allN 143 (fun i => allN 143 (fun j => pcK mulT i j)) =
    true from ?_) i hi) j hj
  rotate_left
  · refine CFSG.KS.Raw.allN_of_forall fun i hi => ?_
    rcases (show i < 36 ∨ (36 ≤ i ∧ i < 72) ∨ (72 ≤ i ∧ i < 108) ∨ 108 ≤ i by omega) with
      h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | h
    · exact allN_spec ch4193pc0 i h
    · have := allN_spec ch4193pc1 (i - 36) (by omega)
      rwa [show Nat.add 36 (i - 36) = i by change 36 + (i - 36) = i; omega] at this
    · have := allN_spec ch4193pc2 (i - 72) (by omega)
      rwa [show Nat.add 72 (i - 72) = i by change 72 + (i - 72) = i; omega] at this
    · have := allN_spec ch4193pc3 (i - 108) (by omega)
      rwa [show Nat.add 108 (i - 108) = i by change 108 + (i - 108) = i; omega] at this
  have hp : CFSG.Monster.B.Co2.Rep 1755 (compA 1755 invs[i]! invs[j]!) (sg i * sg j) :=
    CFSG.Monster.B.Co2.rep_compA (rep_sg hi) (rep_sg hj)
  rw [prodAt_eq' (by rw [numInvs_eq]; exact hi) (by rw [numInvs_eq]; exact hj), prodIdx]
  unfold pcK at hc
  rw [sB_eq, sB_eq, sB_eq] at hc
  cases hlt : Nat.blt (mulT i j) 143
  · rw [hlt] at hc
    change bAnd(Nat.beq (mulT i j) 143, bIf(Nat.beq i j, true, movedK (IT i) (IT j))) = true at hc
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 hc
    rw [Nat.eq_of_beq_eq_true h1, find_none hp, numInvs_eq]
    · rfl
    intro k hk he
    have hsq : (sg i * sg j) * (sg i * sg j) = 1 := by rw [← he]; exact sg_sq hk
    cases hij : Nat.beq i j
    · rw [hij] at h2
      exact moved_ne hi hj h2 hsq
    · rw [← Nat.eq_of_beq_eq_true hij, sg_sq hi] at he
      exact sg_ne_one hk he
  · rw [hlt] at hc
    have hk : mulT i j < 143 := Nat.blt_eq.mp hlt
    rw [find_some hk (base_eq hi hj hk hc ▸ hp)]
    rfl

theorem invsOK_k : invsOK = true := by
  rw [invsOK, Array.all_eq_true]
  intro i hi
  have hi' : i < 143 := by rw [← numInvs_eq]; exact hi
  have e : invs[i] = invs[i]! := (getElem!_pos invs i hi).symm
  rw [e, (props.1 _ (invs_mem hi')).1, mem_surv' (L := titsSLevels) (q := isInv) (invs_mem hi')]
  rfl

theorem invsDistinct_k : invsDistinct = true := by
  rw [invsDistinct, CFSG.Monster.B.Co2.allLt_iff]
  intro i hi
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro j hj
  rw [numInvs_eq] at hi hj
  by_cases hij : i = j
  · simp [hij]
  · have hne : eqA 1755 invs[i]! invs[j]! = false := by
      cases he : eqA 1755 invs[i]! invs[j]!
      · rfl
      · exact absurd (sg_inj hi hj ((CFSG.Monster.B.Co2.eqA_iff (rep_sg hi) (rep_sg hj)).1 he))
          hij
    simp [hij, hne]

theorem any_SL (a : Array Nat) :
    SL.any (eqA 1755 a) = (List.range numInvs).any fun i => eqA 1755 a invs[i]! := by
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨x, hx, he⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hi' : i < 143 := by rw [← SL_len]; exact hi
    refine ⟨i, List.mem_range.2 (by rw [numInvs_eq]; exact hi'), ?_⟩
    rw [invs_get hi']
    exact he
  · rintro ⟨i, hi, he⟩
    have hi' : i < 143 := by rw [← numInvs_eq]; exact List.mem_range.1 hi
    exact ⟨_, invs_mem hi', he⟩

theorem invsComplete_k : invsComplete = true := by
  have h := CertificateChecks.Batch27580.partA titsSLevels isInv
  rw [invsComplete]
  have e : (fun y => !isInv y || (survivors5 1755 titsSLevels isInv).any (eqA 1755 y)) =
      fun a => !isInv a || (List.range numInvs).any fun i => eqA 1755 a invs[i]! := by
    funext a
    rw [← any_SL a]
    rfl
  rw [e] at h
  exact h

theorem search_k : search numInvs prodAt 6 [] 0 = true := by
  rw [numInvs_eq, search_congr 143 (m' := mulT) (fun i hi j hj => prodAt_eq_mulT hi hj) 6 [] 0
    (by simp), ← searchK_eq]
  exact ch4193srch

theorem piArr_eq : CFSG.Quasithin.titsPiArr = unpack 1755 11 CertificateChecks.KernelMisc.TitsPi.P :=
  CFSG.KC.TitsPi.cmpL_sound CertificateChecks.KernelMisc.TitsPi.bind

theorem outerOK_k : outerOK = true := by
  have cP := (CertificateChecks.KernelSpor.Tits2264.permC_spec CertificateChecks.KernelMisc.TitsPi.perm).2.1
  obtain ⟨-, -, -, rP⟩ := canonK_facts cP
  refine all5K_sound bindsS permS TitsS.hl (P := outQ CertificateChecks.KernelMisc.TitsPi.P)
    (fun t0 t1 t2 t3 t4 c0 c1 c2 c3 c4 _ h => ?_) ch4193out
  have hg := (gpt_facts c0 c1 c2 c3 c4).2
  have hs : sqQ CertificateChecks.KernelMisc.TitsPi.P t0 t1 t2 t3 t4 = false := by
    cases hq : sqQ CertificateChecks.KernelMisc.TitsPi.P t0 t1 t2 t3 t4
    · rfl
    · unfold outQ at h
      rw [hq] at h
      exact absurd h (by decide)
  obtain ⟨x, hx, hf⟩ := exists_of_allN_false hs
  rw [Bool.not_eq_true', Bool.eq_false_iff]
  intro he
  have e := CFSG.Monster.B.Co2.allLt_spec he hx
  rw [beq_iff_eq, CFSG.Monster.B.Co2.idA_get hx, CFSG.Monster.B.Co2.compA_get hx,
    CFSG.Monster.B.Co2.compA_get hx, piArr_eq, unpack_getT hx, (hg _ (rP x hx)).1,
    CFSG.Monster.B.Co2.compA_get (hg _ (rP x hx)).2, unpack_getT (hg _ (rP x hx)).2,
    (hg _ (rP _ (hg _ (rP x hx)).2)).1] at e
  change Nat.beq (gpt 11 (mask 11) t0 t1 t2 t3 t4 (pg 11 (mask 11) CertificateChecks.KernelMisc.TitsPi.P
    (gpt 11 (mask 11) t0 t1 t2 t3 t4 (pg 11 (mask 11) CertificateChecks.KernelMisc.TitsPi.P x)))) x =
    false at hf
  rw [e, Nat.beq_refl] at hf
  exact absurd hf (by decide)

theorem titsRankCheck_k : invsOK = true ∧ invsDistinct = true ∧ invsComplete = true ∧
    search numInvs prodAt 6 [] 0 = true ∧ outerOK = true :=
  ⟨invsOK_k, invsDistinct_k, invsComplete_k, search_k, outerOK_k⟩

end CertificateChecks.KernelSporSch.Rank4193

end
