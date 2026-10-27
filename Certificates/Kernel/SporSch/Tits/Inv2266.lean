module

public import Certificates.Kernel.SporSch.Tits.Inv2266EH
public import Certificates.Kernel.SporSch.Tits.Inv2266ENt
public import Certificates.Kernel.SporSch.Tits.Inv2266ENk
public import Certificates.Kernel.SporSch.Tits.Inv2266ENc
public import Certificates.Kernel.SporSch.Tits.Inv2266K
public import Certificates.Kernel.SporSch.Tits.Inv2266D2
public import CFSG.Certificates.Kernel.Spor.SiftRSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.TitsInv

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.BfsPin
open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Monster.B.Co2
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2264
open CertificateChecks.KernelSpor.Tits2268 CertificateChecks.KernelMisc
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.TitsCommon
open CertificateChecks.KernelSporSch.TitsHelp CertificateChecks.KernelSporSch.TitsAbel

theorem t_eq : titsTArr = unpack 1755 11 TitsT := by
  unfold titsTArr
  rw [wa_eq tW, Nat.eq_of_beq_eq_true tB]

theorem g1_eq : titsGenArrs[1]! = unpack 1755 11 (TitsText.F 1) := gen_eq (by norm_num)

theorem g1i_eq : invCand 1755 (unpack 1755 11 (TitsText.F 1)) = unpack 1755 11 (pinv (TitsText.F 1)) :=
  (invEqK_sound (allN_spec permG 1 (by norm_num))).1

theorem part1 : lettersOK 13 titsTWord = true ∧ inK titsTArr = true ∧
    eqA 1755 titsTArr (idA 1755) = false ∧
    eqA 1755 (compA 1755 titsTArr titsTArr) (idA 1755) = true ∧
    (∀ j < 3, inS (conjArr titsGenArrs[1]! titsSArrs[j]!) = true) ∧
    inS (compA 1755 titsGenArrs[1]! titsGenArrs[1]!) = true ∧ inS titsGenArrs[1]! = false ∧
    all5 1755 titsSLevels (fun a =>
      !eqA 1755 (compA 1755 (compA 1755 a titsGenArrs[1]!) (compA 1755 a titsGenArrs[1]!))
        (idA 1755)) = true := by
  refine ⟨by decide, siftK_soundR bindsK permK TitsK.hl t_eq (hi_of cT) (range_of_canonK cT) kTK,
    ?_, ?_,
    fun j hj => ?_, ?_, ?_, ?_⟩
  · rw [t_eq]
    exact neIdK_sound kTne
  · rw [t_eq]
    exact sqIdK_sound kTsq
  · unfold conjArr
    rw [g1_eq, g1i_eq, s_get (by omega), cu cG1 (cS (by omega)), cu (cc cG1 (cS (by omega))) cG1i]
    exact inS_of (cc (cc cG1 (cS (by omega))) cG1i) (allN_spec k5 j hj)
  · rw [g1_eq, cu cG1 cG1]
    exact inS_of (cc cG1 cG1) k6
  · have e : inS (unpack 1755 11 (TitsText.F 1)) = sS (TitsText.F 1) :=
      siftK_eq bindsS permS TitsS.hl rfl (hi_of cG1) (range_of_canonK cG1)
    rw [g1_eq, e]
    cases h : sS (TitsText.F 1)
    · rfl
    · have k := k7
      rw [h] at k
      exact absurd k (by decide)
  · refine all5K_sound bindsS permS TitsS.hl (fun t0 t1 t2 t3 t4 c0 c1 c2 c3 c4 _ h => ?_) TitsS8.all
    rw [g1_eq, ← sqGPts_sound c0 c1 c2 c3 c4 cG1, ← sqGR_eq]
    change bIf(sqGR (TitsText.F 1) t0 t1 t2 t3 t4, false, true) = true at h
    cases hs : sqGR (TitsText.F 1) t0 t1 t2 t3 t4
    · rfl
    · rw [hs] at h
      exact absurd h (by decide)

theorem bD13 : Bind13 titsDerivedArrs TitsD.S TitsD.SI :=
  ⟨bindsD.2.2.2.1, bindsD.2.2.2.2.1, permD⟩

theorem wa_def (wd : List Int) :
    wordArr 1755 titsDerivedArrs wd = wordA 1755 titsDerivedArrs (rawInvs 1755 titsDerivedArrs) wd :=
  rfl

theorem isInvW {wd : List Int} (hl : lettersK 13 wd = true) :
    isInvA 1755 (wordArr 1755 titsDerivedArrs wd) (invCand 1755 (wordArr 1755 titsDerivedArrs wd)) =
      true := by
  rw [wa_def]
  exact wPerm_sound bD13 hl

theorem zipA_map {α : Type} {g : α → Nat → Bool} {f : α → Array Nat} :
    ∀ {A : List α} {L : List Nat}, zipA g A L = true →
      (∀ a ∈ A, ∀ l ∈ L, g a l = true → f a = unpack 1755 11 l) →
      A.map f = L.map (unpack 1755 11)
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => (Bool.false_ne_true h).elim
  | _ :: _, [], h, _ => (Bool.false_ne_true h).elim
  | a :: A, l :: L, h, hf => by
    have h' : Bool.rec (motive := fun _ => Bool) false (zipA g A L) (g a l) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    rw [List.map_cons, List.map_cons, hf a List.mem_cons_self l List.mem_cons_self h1,
      zipA_map h2 fun b hb m hm => hf b (List.mem_cons_of_mem _ hb) m (List.mem_cons_of_mem _ hm)]

theorem ic_eq : titsInvConj = TitsIC.map (unpack 1755 11) := by
  unfold titsInvConj
  refine zipA_map kICz fun bw _ y hy hg => ?_
  obtain ⟨b, wd⟩ := bw
  have hc : C y := allL_spec kICc y hy
  change conjW TitsD.S TitsD.SI wd (Bool.rec (motive := fun _ => Nat) TitsT TitsZ b) y = true at hg
  dsimp only
  unfold conjArr
  rw [wa_def]
  cases b
  · rw [ite_eq_right_of_eq_false _ _ (by simp), t_eq]
    exact conjW_sound bD13 cT hc hg
  · rw [ite_eq_left_of_eq_true _ _ (by simp), z_eq]
    exact conjW_sound bD13 canonZ hc hg

theorem memR_any {t0 t1 t2 t3 t4 : Nat} (h0 : C t0) (h1 : C t1) (h2 : C t2) (h3 : C t3)
    (h4 : C t4) : ∀ {L : List Nat}, (∀ y ∈ L, C y) → memR L t0 t1 t2 t3 t4 = true →
      anyEq (L.map (unpack 1755 11)) (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4)) = true
  | [], _, h => (Bool.false_ne_true h).elim
  | y :: L, hc, h => by
    have h' : Bool.rec (motive := fun _ => Bool) (memR L t0 t1 t2 t3 t4) true
        (eqR y t0 t1 t2 t3 t4) = true := h
    unfold anyEq
    rw [List.map_cons, List.any_cons]
    cases he : eqR y t0 t1 t2 t3 t4
    · rw [he] at h'
      have := memR_any h0 h1 h2 h3 h4 (fun z hz => hc z (List.mem_cons_of_mem _ hz)) h'
      unfold anyEq at this
      rw [this, Bool.or_true]
    · rw [← eqPts_sound h0 h1 h2 h3 h4 (hc y List.mem_cons_self), ← eqR_eq, he, Bool.true_or]

private theorem strictB_app (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem p2_core (f m s e : Bool) (hf : f = false → s = false)
    (h : bIf(f, bIf(m, true, bIf(s, bIf(e, true, false), true)), true) = true) :
    bIf(s, bIf(e, true, m), true) = true := by
  revert hf h
  cases f <;> cases m <;> cases s <;> cases e <;> decide

theorem p2_sound {t0 t1 t2 t3 t4 : Nat} (h : P2 t0 t1 t2 t3 t4 = true) :
    bIf(sqR t0 t1 t2 t3 t4, bIf(eqR (pidn 1755 11) t0 t1 t2 t3 t4, true,
      memR TitsIC t0 t1 t2 t3 t4), true) = true := by
  rw [sqR_eq, eqR_eq, memR_eq]
  refine p2_core _ _ _ _ (fun hf => ?_) h
  cases hs : sqPts 1755 11 (mask 11) t0 t1 t2 t3 t4
  · rfl
  · unfold sqPts at hs
    have h1 : Nat.beq (gpt 11 (mask 11) t0 t1 t2 t3 t4 (gpt 11 (mask 11) t0 t1 t2 t3 t4
        (nat_lit 1754))) (nat_lit 1754) = true := allN_spec hs (nat_lit 1754) (by norm_num)
    exact absurd (h1.symm.trans hf) (by decide)

theorem p3_sound {t0 t1 t2 t3 t4 : Nat} (h : P3 t0 t1 t2 t3 t4 = true) (y : Nat)
    (hy : y ∈ TitsEX) : bIf(conjR TitsT y t0 t1 t2 t3 t4, false, true) = true := by
  unfold P3 at h
  simp only [strictB_app] at h
  have hq := allL_spec h y hy
  beta_reduce at hq
  rw [conjR_eq]
  cases hb : Nat.beq (pg 11 (mask 11) y (gpt 11 (mask 11) t0 t1 t2 t3 t4 (nat_lit 1754)))
      (gpt 11 (mask 11) t0 t1 t2 t3 t4 (pg 11 (mask 11) TitsT (nat_lit 1754)))
  · cases hc : conjPts 1755 11 (mask 11) TitsT y t0 t1 t2 t3 t4
    · rfl
    · unfold conjPts at hc
      have h1 : Nat.beq (gpt 11 (mask 11) t0 t1 t2 t3 t4 (pg 11 (mask 11) TitsT (nat_lit 1754)))
          (pg 11 (mask 11) y (gpt 11 (mask 11) t0 t1 t2 t3 t4 (nat_lit 1754))) = true :=
        allN_spec hc (nat_lit 1754) (by norm_num)
      rw [Nat.eq_of_beq_eq_true h1, Nat.beq_refl] at hb
      exact absurd hb (by decide)
  · rw [hb] at hq
    exact hq

theorem part2 : titsInvCert.all (fun bw => lettersOK 13 bw.2 &&
      isInvA 1755 (wordArr 1755 titsDerivedArrs bw.2)
        (invCand 1755 (wordArr 1755 titsDerivedArrs bw.2))) = true ∧
    all5 1755 titsSLevels (fun a => !eqA 1755 (compA 1755 a a) (idA 1755) ||
      eqA 1755 a (idA 1755) || anyEq titsInvConj a) = true := by
  refine ⟨?_, ?_⟩
  · rw [List.all_eq_true]
    rintro ⟨b, wd⟩ hbw
    have hl : lettersK 13 wd = true := allA_spec kIC _ hbw
    dsimp only
    rw [lettersK_sound hl, isInvW hl]
    rfl
  · refine all5K_sound bindsS permS TitsS.hl (fun t0 t1 t2 t3 t4 c0 c1 c2 c3 c4 _ h => ?_) TitsS2.all
    rw [← sqPts_sound c0 c1 c2 c3 c4, TitsCentral.id_eq,
      ← eqPts_sound c0 c1 c2 c3 c4 TitsCentral.canId, ic_eq, ← sqR_eq, ← eqR_eq]
    replace h := p2_sound h
    cases hs : sqR t0 t1 t2 t3 t4
    · rfl
    · rw [hs] at h
      cases he : eqR (pidn 1755 11) t0 t1 t2 t3 t4
      · rw [he] at h
        rw [memR_any c0 c1 c2 c3 c4 (fun y hy => allL_spec kICc y hy) h]
        rfl
      · rfl

theorem zipAF_map {α : Type} {q : α → Bool} {g : α → Nat → Bool} {f : α → Array Nat} :
    ∀ {A : List α} {L : List Nat}, zipAF q g A L = true →
      (∀ a ∈ A, ∀ l ∈ L, g a l = true → f a = unpack 1755 11 l) →
      (A.filter q).map f = L.map (unpack 1755 11)
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => (Bool.false_ne_true h).elim
  | a :: A, L, h, hf => by
    have h' : Bool.rec (motive := fun _ => Bool) (zipAF q g A L)
        (List.rec (motive := fun _ => Bool) false (fun l L' _ => Bool.rec (motive := fun _ => Bool)
          false (zipAF q g A L') (g a l)) L) (q a) = true := h
    cases hq : q a
    · rw [hq] at h'
      rw [List.filter_cons_of_neg (by simp [hq])]
      exact zipAF_map h' fun b hb m hm => hf b (List.mem_cons_of_mem _ hb) m hm
    · rw [hq] at h'
      cases L with
      | nil => exact (Bool.false_ne_true h').elim
      | cons l L' =>
        obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
        rw [List.filter_cons_of_pos hq, List.map_cons, List.map_cons,
          hf a List.mem_cons_self l List.mem_cons_self h1,
          zipAF_map h2 fun b hb m hm =>
            hf b (List.mem_cons_of_mem _ hb) m (List.mem_cons_of_mem _ hm)]

theorem ex_eq : titsExcl = TitsEX.map (unpack 1755 11) := by
  unfold titsExcl
  have hq : (titsFixWords.filter fun pw => decide (2 < pw.1)) = titsFixWords.filter qEx := by
    refine List.filter_congr fun pw _ => ?_
    obtain ⟨p, wd⟩ := pw
    change decide (2 < p) = Nat.blt 2 p
    rw [Bool.eq_iff_iff, decide_eq_true_iff, Nat.blt_eq]
  rw [hq]
  refine zipAF_map kEXz fun pw _ y hy hg => ?_
  obtain ⟨p, wd⟩ := pw
  have hc : C y := allL_spec kEXc y hy
  change exclW TitsD.S TitsD.SI wd TitsT y = true at hg
  dsimp only
  rw [wa_def, t_eq]
  exact exclW_sound bD13 cT hc hg

theorem fix_eq : titsFixWords.map Prod.fst = fixPts := rfl

theorem part3a : (∀ p < 1755, titsTArr[p]! = p → p ∈ titsFixWords.map Prod.fst) ∧
    titsFixWords.all (fun pw => lettersOK 13 pw.2 &&
      (wordArr 1755 titsDerivedArrs pw.2)[0]! == pw.1 &&
      isInvA 1755 (wordArr 1755 titsDerivedArrs pw.2)
        (invCand 1755 (wordArr 1755 titsDerivedArrs pw.2))) = true ∧
    all5 1755 titsHLevels (fun a => isInvA 1755 a (invCand 1755 a) &&
      titsExcl.all fun y => !eqA 1755 (conjArr a titsTArr) y) = true := by
  refine ⟨fun p hp hfix => ?_, ?_, ?_⟩
  · rw [fix_eq]
    rw [t_eq, unpack_get hp] at hfix
    have h := allN_spec kFix p hp
    rw [hfix, Nat.beq_refl] at h
    exact memN_spec h
  · rw [List.all_eq_true]
    rintro ⟨p, wd⟩ hpw
    obtain ⟨hl, h0⟩ := (bAnd_iff _ _).1 (allA_spec kFW _ hpw)
    dsimp only
    rw [lettersK_sound hl, isInvW hl, wa_def, wPt_sound bD13 hl (by norm_num),
      Nat.eq_of_beq_eq_true h0]
    simp
  · refine all5K_sound bindsH permH TitsH.hl (fun t0 t1 t2 t3 t4 c0 c1 c2 c3 c4 hinv h => ?_)
      TitsH3.all
    rw [hinv, Bool.true_and, ex_eq, List.all_map, List.all_eq_true]
    intro y hy
    have hc : C y := allL_spec kEXc y hy
    have hq := p3_sound h y hy
    rw [Function.comp_apply]
    unfold conjArr
    rw [t_eq, ← conjPts_sound c0 c1 c2 c3 c4 cT hc hinv, ← conjR_eq]
    cases hs : conjR TitsT y t0 t1 t2 t3 t4
    · rfl
    · rw [hs] at hq
      exact absurd hq (by decide)

theorem mem_surv {L : Array Level} {q : Array Nat → Bool} {x : Array Nat}
    (h : x ∈ survivors5 1755 L q) : q x = true := by
  simp only [survivors5, List.mem_flatMap, List.mem_filter, List.mem_map, List.mem_range] at h
  obtain ⟨_, _, _, _, _, _, _, _, ⟨_, _, _⟩, hq⟩ := h
  exact hq

theorem commA_eq {t0 t1 t2 t3 t4 : Nat} (c0 : C t0) (c1 : C t1) (c2 : C t2) (c3 : C t3)
    (c4 : C t4) : commR TitsT t0 t1 t2 t3 t4 =
      commA (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4)) titsTArr := by
  rw [commR_eq, t_eq, commPts_sound c0 c1 c2 c3 c4 cT]
  rfl

theorem canOf {LR TR : Nat → Nat} (hc : allN 5 (fun i => allN (rcnt (LR i)) (fun a =>
    canonK 1755 11 (mask 11) (1755 * 11) (trAt 1755 (1755 * 11) LR TR i a))) = true)
    {t0 t1 t2 t3 t4 : Nat} (h : IsTr5 LR TR t0 t1 t2 t3 t4) :
    C t0 ∧ C t1 ∧ C t2 ∧ C t3 ∧ C t4 := by
  obtain ⟨⟨a0, h0, rfl⟩, ⟨a1, h1, rfl⟩, ⟨a2, h2, rfl⟩, ⟨a3, h3, rfl⟩, ⟨a4, h4, rfl⟩⟩ := h
  exact ⟨allN_spec (allN_spec hc 0 (by norm_num)) a0 h0, allN_spec (allN_spec hc 1 (by norm_num)) a1 h1,
    allN_spec (allN_spec hc 2 (by norm_num)) a2 h2, allN_spec (allN_spec hc 3 (by norm_num)) a3 h3,
    allN_spec (allN_spec hc 4 (by norm_num)) a4 h4⟩

theorem sTH : siftA 1755 (rawLevels 1755 titsHArrs (baseArr 1755 titsHBase)) (baseArr 1755 titsHBase)
    0 (unpack 1755 11 TitsT) = true :=
  siftK_soundR bindsH permH TitsH.hl rfl (hi_of cT) (range_of_canonK cT) kTH
theorem sTN : siftA 1755 (rawLevels 1755 titsNArrs (baseArr 1755 titsNBase)) (baseArr 1755 titsNBase)
    0 (unpack 1755 11 TitsT) = true :=
  siftK_soundR bindsN permN TitsN.hl rfl (hi_of cT) (range_of_canonK cT) kTN

theorem ndH : (baseArr 1755 titsHBase).toList.Nodup := by decide
theorem ndN : (baseArr 1755 titsNBase).toList.Nodup := by decide

theorem agrTH : Agrees TitsH.LR TitsH.TR PTH (fun a => commA a titsTArr) :=
  fun t0 t1 t2 t3 t4 h => by
    rw [t_eq]
    exact baseCommG_eq bindsH TitsH.head TitsH.hl (NS := 220) (CH := 8) (by norm_num) TitsH.hs ndH
      h cT sTH

theorem agrTN : Agrees TitsN.LR TitsN.TR PTN (fun a => commA a titsTArr) :=
  fun t0 t1 t2 t3 t4 h => by
    rw [t_eq]
    exact baseCommG_eq bindsN TitsN.head TitsN.hl (NS := 220) (CH := 8) (by norm_num) TitsN.hs ndN
      h cT sTN

theorem hKN (j : Nat) (hj : j < 7) : siftA 1755 (rawLevels 1755 titsNArrs (baseArr 1755 titsNBase))
    (baseArr 1755 titsNBase) 0 titsKArrs[j]! = true :=
  siftK_soundR bindsN permN TitsN.hl (bindsK.2.2.2.2.1 j hj) (hi_of (allN_spec canK j hj))
    (range_of_canonK (allN_spec canK j hj)) (allN_spec kKN j hj)

theorem agrK : Agrees TitsN.LR TitsN.TR PK (fun a => commA a titsTArr && inK a) :=
  fun t0 t1 t2 t3 t4 h => by
    change Bool.rec (motive := fun _ => Bool) false
      (ktKB TitsK.LR TitsK.TRI TitsK.BP TitsN.BP t0 t1 t2 t3 t4) (PTN t0 t1 t2 t3 t4) = _
    rw [agrTN t0 t1 t2 t3 t4 h, ktKB_eq bindsK permK TitsK.hl bindsN TitsN.head TitsN.hl
      (NS := 220) (CH := 8) (by norm_num) TitsN.hs ndN hKN h]
    cases commA (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4)) titsTArr <;> rfl

theorem propsH : (∀ x ∈ titsCHt, isInvA 1755 x (invCand 1755 x) = true ∧ inH x = true) ∧
    titsCHt.Pairwise (fun a b => eqA 1755 a b = false) :=
  surv5K_propsT (fun a => commA a titsTArr) bindsH permH TitsH.hl
theorem propsN : (∀ x ∈ titsCNt, isInvA 1755 x (invCand 1755 x) = true ∧ inN x = true) ∧
    titsCNt.Pairwise (fun a b => eqA 1755 a b = false) :=
  surv5K_propsT (fun a => commA a titsTArr) bindsN permN TitsN.hl

theorem ascK_lt {T : Nat} : ∀ {C : List Nat} {lo : Nat}, ascK T C lo = true → ∀ k ∈ C, k < T
  | [], _, _, k, hk => absurd hk List.not_mem_nil
  | c :: C, lo, h, k, hk => by
    have h' : Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false (ascK T C (Nat.succ c)) (Nat.blt c T))
        (Nat.ble lo c) = true := h
    obtain ⟨-, h2⟩ := (bAnd_iff _ _).1 h'
    obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
    rcases List.mem_cons.1 hk with rfl | hk
    · exact Nat.blt_eq ▸ h3
    · exact ascK_lt h4 k hk

theorem allL_eq_all {f : Nat → Bool} : ∀ (L : List Nat), allL f L = L.all f
  | [] => rfl
  | x :: L => by
    change Bool.rec (motive := fun _ => Bool) false (allL f L) (f x) = (f x && L.all f)
    rw [allL_eq_all L]
    cases f x <;> rfl

theorem qt_def : titsQt = survivors5 1755 (rawLevels 1755 titsNArrs (baseArr 1755 titsNBase))
    (fun a => commA a titsTArr && inK a) := by
  unfold titsQt titsCNt
  rw [survivors5_filter]
  rfl

theorem qt_eq : titsQt = TitsMN.CK.map
    (fun k => unpack 1755 11 (prodCode 1755 11 (mask 11) (1755 * 11) TitsN.LR TitsN.TR k)) := by
  rw [qt_def]
  exact surv5K_soundCT bindsN permN TitsN.hl agrK mK aK TitsNkE.all

theorem gc_mem {k : Nat} (hk : k ∈ TitsMN.GC) : k ∈ TitsMN.CK := by
  have h := (bAnd_iff (allL (fun g => memN g TitsMN.CK) TitsMN.GC) _).1 kTree
  exact memN_spec (allL_spec h.1 k hk)

theorem agrC : Agrees TitsN.LR TitsN.TR PC (fun a => commA a titsTArr &&
    titsQt.all fun q => commA a q) := fun t0 t1 t2 t3 t4 h => by
  obtain ⟨c0, c1, c2, c3, c4⟩ := canOf canTRN h
  have cx : C (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4) :=
    canonK_pcomp (canonK_pcomp (canonK_pcomp (canonK_pcomp c0 c1) c2) c3) c4
  change Bool.rec (motive := fun _ => Bool) false
    (ctKG TitsN.BP TitsN.LR TitsN.TR TitsMN.GC t0 t1 t2 t3 t4) (PTN t0 t1 t2 t3 t4) = _
  have hall : ctKG TitsN.BP TitsN.LR TitsN.TR TitsMN.GC t0 t1 t2 t3 t4 =
      titsQt.all fun q => commA (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4)) q := by
    rw [qt_eq, qtree_sound bindsN TitsN.head TitsN.hl (NS := 220) (CH := 8) (by norm_num)
      TitsN.hs ndN aK kTree _ cx]
    rw [List.all_map, ctKG, allL_eq_all, Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    refine forall_congr' fun k => imp_congr_right fun hk => ?_
    rw [Function.comp_apply, baseComm_eq bindsN TitsN.head TitsN.hl (NS := 220) (CH := 8)
      (by norm_num) TitsN.hs ndN h (ascK_lt aK k (gc_mem hk))]
  rw [agrTN t0 t1 t2 t3 t4 h, hall]
  cases commA (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4)) titsTArr <;> rfl

theorem ccq_def : titsCCQ = survivors5 1755 (rawLevels 1755 titsNArrs (baseArr 1755 titsNBase))
    (fun a => commA a titsTArr && titsQt.all fun q => commA a q) := by
  unfold titsCCQ titsCNt
  rw [survivors5_filter]
  rfl

theorem part3b : all5 1755 titsHLevels (fun a => !commA a titsTArr || anyEq titsCHt a) = true ∧
    titsCHt.length = 512 ∧
    titsCHt.all (fun c => isInvA 1755 c (invCand 1755 c) && commA c titsTArr && inH c) = true ∧
    titsCHt.Pairwise (fun a b => eqA 1755 a b = false) := by
  refine ⟨all5_surv _ _, ?_, ?_, propsH.2⟩
  · exact (surv5K_countT bindsH permH TitsH.hl agrTH TitsHtE.all).trans
      (Nat.eq_of_beq_eq_true cntH)
  · rw [List.all_eq_true]
    intro c hc
    have hq : commA c titsTArr = true := mem_surv (q := fun a => commA a titsTArr) hc
    obtain ⟨h1, h2⟩ := propsH.1 c hc
    rw [h1, hq, Bool.true_and, Bool.true_and]
    exact h2

theorem part4 : all5 1755 titsNLevels (fun a => !commA a titsTArr || anyEq titsCNt a) = true ∧
    titsCNt.length = 1536 ∧ titsQt.length = 256 ∧ titsCCQ.length = 8 ∧
    titsCNt.all (fun c => isInvA 1755 c (invCand 1755 c) && commA c titsTArr && inN c) = true ∧
    titsCNt.Pairwise (fun a b => eqA 1755 a b = false) ∧ titsCCQ.all inK = true := by
  refine ⟨all5_surv _ _, ?_, ?_, ?_, ?_, propsN.2, ?_⟩
  · exact (surv5K_countT bindsN permN TitsN.hl agrTN TitsNtE.all).trans
      (Nat.eq_of_beq_eq_true cntN)
  · rw [qt_def]
    exact (surv5K_countT bindsN permN TitsN.hl agrK TitsNkE.all).trans (Nat.eq_of_beq_eq_true cntK)
  · rw [ccq_def]
    exact (surv5K_countT bindsN permN TitsN.hl agrC TitsNcE.all).trans (Nat.eq_of_beq_eq_true cntC)
  · rw [List.all_eq_true]
    intro c hc
    have hq : commA c titsTArr = true := mem_surv (q := fun a => commA a titsTArr) hc
    obtain ⟨h1, h2⟩ := propsN.1 c hc
    rw [h1, hq, Bool.true_and, Bool.true_and]
    exact h2
  · rw [List.all_eq_true]
    intro x hx
    rw [ccq_def] at hx
    have h : (commA x titsTArr && inK x) = true :=
      surv5K_subT bindsN permN TitsN.hl agrC TitsNcE.all agrK TitsNkE.all subCK x hx
    rw [Bool.and_eq_true] at h
    exact h.2

end CertificateChecks.KernelSporSch.TitsInv

end
