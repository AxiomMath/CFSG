module

public import Certificates.Kernel.ONanF2.Checks
public import Certificates.Kernel.ONanF2K.Check
public import CFSG.Certificates.Kernel.ONanF2Sound

public section

namespace CFSG.KC.ONanF2.Glue

open CFSG.KC.ONanF2 CFSG.KC.ONanF2K CFSG.KC.ONanF2.Checks CFSG.KS.ONanF2
open CFSG.OddStandard.ONanRec.F2 hiding enc

theorem beqE (x : AlpE) {c : ℕ} (hc : c < 512) : Nat.beq (enc x) c = true ↔ x = dec c := by
  rw [beq_iff (enc_lt x) hc, dec_enc]

theorem cmE (x : AlpE) {c : ℕ} (hc : c < 512) : cmK (enc x) c = true ↔ x * dec c = dec c * x := by
  rw [cmK_iff (enc_lt x) hc, dec_enc]

theorem cmE' (x : AlpE) {c : ℕ} (hc : c < 512) : cmK c (enc x) = true ↔ dec c * x = x * dec c := by
  rw [cmK_iff hc (enc_lt x), dec_enc]

theorem eq_of_beq {a b : ℕ} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem bound_maskOf (q : ℕ → Bool) (c : ℕ) (h : (maskOf q 512).testBit c = true) : c < 512 := by
  rw [testBit_maskOf, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem pairsE_inv : ∀ p ∈ pairsE, dec p.2 = (dec p.1)⁻¹ := by decide +kernel

theorem genE_eq : genE = pairsE.map fun p => dec p.1 := by decide +kernel

theorem dgen : ∀ i : Fin 5, dec (![16, 4, 1, 64, 256] i) = AlpE.gen i := by decide +kernel

theorem invE_eq : ∀ i : Fin 7, invE i = dec (invC i) := by decide +kernel

theorem invC_lt : ∀ i : Fin 7, invC i < 512 := by decide +kernel

theorem dec34 : dec 34 = AlpE.zc := by decide +kernel

theorem bit_all : ∀ c < 512, (Nat.sub (Nat.shiftLeft 1 512) 1).testBit c = true := by decide +kernel

theorem bit_nonV : ∀ c < 512, 64 ≤ c →
    (Nat.sub (Nat.shiftLeft 1 512) (Nat.shiftLeft 1 64)).testBit c = true := by
  decide +kernel

theorem hV0 : SubOK genV0E ballV0 32 ∧ Rep mV0 ballV0 :=
  subOK_of_subB gV0L genV0E (by decide +kernel) mV0 32 chV0
theorem hPd : SubOK genPdE ballPd 64 ∧ Rep mPd ballPd :=
  subOK_of_subB gPdL genPdE (by decide +kernel) mPd 64 chPd
theorem hComm : SubOK genCommE ballComm 64 ∧ Rep mPd ballComm :=
  subOK_of_subB gCommL genCommE (by decide +kernel) mPd 64 chComm
theorem hV : SubOK genVE ballV 64 ∧ Rep mV ballV :=
  subOK_of_subB gVL genVE (by decide +kernel) mV 64 chV
theorem hW : SubOK genWE ballW 8 ∧ Rep mW ballW :=
  subOK_of_subB gWL genWE (by decide +kernel) mW 8 chW
theorem hVt : SubOK genVtE ballVt 128 ∧ Rep mVt ballVt :=
  subOK_of_subB gVtL genVtE (by decide +kernel) mVt 128 chVt
theorem hQ : SubOK genQE ballQ 32 ∧ Rep mQ ballQ :=
  subOK_of_subB gQL genQE (by decide +kernel) mQ 32 chQ
theorem hR : SubOK genRE ballR 16 ∧ Rep mR ballR :=
  subOK_of_subB gRL genRE (by decide +kernel) mR 16 chR

theorem getD_ballMaxL (i : Fin 7) : ballMaxL.getD i [] = ballFix (genMaxE i) := by
  simp [ballMaxL, List.getD_eq_getElem?_getD]

theorem getD_ballCentL (i : Fin 3) : ballCentL.getD i [] = ballFix (genCentE i) := by
  simp [ballCentL, List.getD_eq_getElem?_getD]

theorem getD_ballCVL (i : Fin 7) : ballCVL.getD i [] = ballFix (genCV i) := by
  simp [ballCVL, List.getD_eq_getElem?_getD]

theorem getD_classLists (i : Fin 7) : classLists.getD i [] = orbitC genE (invE i) := by
  simp only [List.getD_eq_getElem?_getD, classLists, invEL, List.map_ofFn, List.getElem?_ofFn,
    i.isLt, ↓reduceDIte, Option.getD_some, Function.comp_apply, Fin.eta]

theorem getD_invEL (i : Fin 7) : invEL.getD i 1 = invE i := by
  simp only [List.getD_eq_getElem?_getD, invEL, List.getElem?_ofFn, i.isLt, ↓reduceDIte,
    Option.getD_some, Fin.eta]

theorem genMax_eq : ∀ i : Fin 7, genMaxE i = (gMaxL i).map dec := by decide +kernel
theorem genCent_eq : ∀ i : Fin 3, genCentE i = (gCentL i).map dec := by decide +kernel
theorem genCV_eq : ∀ i : Fin 7, genCV i = (gCVL i).map dec := by decide +kernel

theorem hMax (i : Fin 7) :
    SubOK (genMaxE i) (ballMaxL.getD i []) 256 ∧ Rep (mMax i) (ballMaxL.getD i []) := by
  rw [getD_ballMaxL]
  exact subOK_of_subB _ _ (genMax_eq i) _ _ (chMax i)

theorem hCent (i : Fin 3) :
    SubOK (genCentE i) (ballCentL.getD i []) 32 ∧ Rep (mCent i) (ballCentL.getD i []) := by
  rw [getD_ballCentL]
  exact subOK_of_subB _ _ (genCent_eq i) _ _ (chCent i)

theorem hCV (i : Fin 7) :
    SubOK (genCV i) (ballCVL.getD i []) (cardCV i) ∧ Rep (mCV i) (ballCVL.getD i []) := by
  rw [getD_ballCVL]
  exact subOK_of_subB _ _ (genCV_eq i) _ _ (chCV i)

theorem hCls (i : Fin 7) :
    ClassOK genE (invE i) (classLists.getD i []) (![1, 2, 4, 16, 32, 16, 16] i) ∧
      Rep (mCls i) (classLists.getD i []) := by
  rw [getD_classLists, invE_eq]
  exact classOK_of_clsOKB pairsE pairsE_inv genE genE_eq (invC_lt i) _ _ (chCls i)

theorem hInv (u : AlpE) : mInv.testBit (enc u) = true ↔ u * u = 1 ∧ u ≠ 1 := by
  rw [← eq_of_beq chInv, testBit_maskOf_enc, Bool.and_eq_true, Bool.not_eq_true', ← enc_mul,
    beqE _ (by decide), dec_zero]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun h => ?_⟩
    rw [h, enc_one] at h2
    exact Bool.noConfusion h2
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    cases h : Nat.beq (enc u) 0
    · rfl
    · rw [beqE _ (by decide), dec_zero] at h
      exact absurd h h2

theorem mInv_lt (c : ℕ) (h : mInv.testBit c = true) : c < 512 :=
  bound_maskOf _ c (by rw [eq_of_beq chInv]; exact h)

theorem factCentre_holds : factCentre := by
  refine ⟨by decide +kernel, fun x hx => ?_⟩
  have h := forall_of_allB chCentre x
  have hc : ∀ i : Fin 5, cmK (![16, 4, 1, 64, 256] i) (enc x) = true := by
    intro i
    rw [cmE' x (by fin_cases i <;> decide), dgen]
    exact hx i
  have h0 : cmK 16 (enc x) = true := hc 0
  have h1 : cmK 4 (enc x) = true := hc 1
  have h2 : cmK 1 (enc x) = true := hc 2
  have h3 : cmK 64 (enc x) = true := hc 3
  have h4 : cmK 256 (enc x) = true := hc 4
  simp only [h0, h1, h2, h3, h4, Bool.and_self, Bool.not_true, Bool.false_or, Bool.or_eq_true,
    beqE x (by decide : (0 : ℕ) < 512), beqE x (by decide : (34 : ℕ) < 512), dec_zero, dec34] at h
  exact h

theorem factClasses_holds : factClasses := by
  refine ⟨by decide +kernel, fun u hu => ?_, fun i => (hCls i).1, fun i j hij u hu hu' => ?_,
    ?_, fun i => ?_⟩
  · rw [allInvs, List.mem_filter, decide_eq_true_eq] at hu
    have hb := (hInv u).2 hu.2
    have hz := eq_of_beq chInvCover
    have hU : (Nat.lor (mCls 0) (Nat.lor (mCls 1) (Nat.lor (mCls 2) (Nat.lor (mCls 3)
        (Nat.lor (mCls 4) (Nat.lor (mCls 5) (mCls 6))))))).testBit (enc u) = true := by
      have := congrArg (fun m => m.testBit (enc u)) hz
      simp only [testBit_diffM, hb, Nat.zero_testBit, Bool.true_and, Bool.not_eq_false'] at this
      exact this
    simp only [testBit_lor, Bool.or_eq_true] at hU
    rcases hU with h | h | h | h | h | h | h
    · exact ⟨0, ((hCls 0).2.1 u).2 h⟩
    · exact ⟨1, ((hCls 1).2.1 u).2 h⟩
    · exact ⟨2, ((hCls 2).2.1 u).2 h⟩
    · exact ⟨3, ((hCls 3).2.1 u).2 h⟩
    · exact ⟨4, ((hCls 4).2.1 u).2 h⟩
    · exact ⟨5, ((hCls 5).2.1 u).2 h⟩
    · exact ⟨6, ((hCls 6).2.1 u).2 h⟩
  · have h1 := ((hCls i).2.1 u).1 hu
    have h2 := ((hCls j).2.1 u).1 hu'
    have := congrArg (fun m => m.testBit (enc u)) (chClsDisj i j hij)
    simp only [testBit_land, h1, h2, Bool.true_and, Nat.zero_testBit] at this
    exact Bool.noConfusion this
  · rw [card_eq_cntM _ mInv (fun x => by
      rw [Finset.mem_filter, hInv]
      simp) mInv_lt]
    exact eq_of_beq chInvCnt
  · rw [getD_invEL, invE_eq,
      card_filter_cntQ _ (fun g => cmK g (invC i)) (fun x => cmE x (invC_lt i)), chCentr i]

theorem nvL_lt : ∀ p ∈ nvL1 ++ nvL2 ++ nvL3, p.1 < 512 := by decide +kernel

theorem factNonV_holds : factNonV := by
  intro x hx
  have hge : 64 ≤ enc x := by
    have : x.d.val ≠ 0 := fun h => hx (Fin.ext h)
    simp only [enc, Nat.add_eq, Nat.mul_eq]
    omega
  have hz := eq_of_beq chNvCover
  have hU : (Nat.lor (lorP nvL1) (Nat.lor (lorP nvL2) (lorP nvL3))).testBit (enc x) = true := by
    have := congrArg (fun m => m.testBit (enc x)) hz
    simp only [testBit_diffM, bit_nonV _ (enc_lt x) hge, Nat.zero_testBit, Bool.true_and,
      Bool.not_eq_false'] at this
    exact this
  simp only [testBit_lor, Bool.or_eq_true, testBit_lorP] at hU
  obtain ⟨p, hp, hb⟩ : ∃ p ∈ nvL1 ++ nvL2 ++ nvL3, p.2.testBit (enc x) = true := by
    rcases hU with ⟨p, hp, hb⟩ | ⟨p, hp, hb⟩ | ⟨p, hp, hb⟩ <;> exact ⟨p, by simp [hp], hb⟩
  have hs : clsB pairsE p.1 p.2 = true ∧ 16 ≤ cntM p.2 512 := by
    rcases List.mem_append.1 hp with hp | hp
    · rcases List.mem_append.1 hp with hp | hp
      · exact nvB_sound _ _ chNv1 p hp
      · exact nvB_sound _ _ chNv2 p hp
    · exact nvB_sound _ _ chNv3 p hp
  obtain ⟨hRp, hnd, hc⟩ := orbit_of_clsB pairsE pairsE_inv genE genE_eq (nvL_lt p hp) p.2 hs.1
  have hx' : x ∈ orbitC genE (dec p.1) := (hRp.1 x).2 hb
  have hc' : ∀ y ∈ orbitC genE (dec p.1), IsConj x y := fun y hy => (hc x hx').symm.trans (hc y hy)
  have hle := card_cent_mul_le x _ hnd hc'
  rw [card_alpE, hRp.length_eq hnd] at hle
  have := Nat.mul_le_mul_left (Finset.univ.filter fun g : AlpE => g * x = x * g).card hs.2
  omega

theorem factSub_holds : factSub :=
  ⟨hV0.1, hPd.1, hComm.1, hV.1, hW.1, hVt.1, hQ.1, hR.1, fun i => (hMax i).1, fun i => (hCent i).1⟩

theorem factMax_holds : factMax := by
  intro i j
  rw [exists_common (hMax i).2 (hCls j).2, chMaxT i j]

theorem factQR_holds : factQR := by
  have hRL : Rep mR (rL.map dec) := by
    have := rep_lorL rL (by decide +kernel)
    rwa [eq_of_beq chRL] at this
  refine ⟨fun x hxQ hxR => ?_, fun x => ?_, fun u hu h1 h2 => ?_, fun x hx h1 => ?_⟩
  · have hb : (Nat.land mQ mR).testBit (enc x) = true := by
      rw [testBit_land, (hQ.2.1 x).1 hxQ, (hR.2.1 x).1 hxR]
      rfl
    rw [eq_of_beq chQR1] at hb
    exact List.mem_singleton.1 ((rep_one.1 x).2 hb)
  · have hb : (imgM (rmulK rL) mQ 512).testBit (enc x) = true := by
      rw [eq_of_beq chQR2]
      exact bit_all _ (enc_lt x)
    obtain ⟨c, hc, hQc, hy⟩ := (testBit_imgM _ _ _ _).1 hb
    obtain ⟨z, hz, hze⟩ := (hn_rmul rL c hc (enc x)).1 hy
    obtain ⟨r, hr, hrz⟩ : ∃ r ∈ rL, dec c * dec r = z := by
      simpa only [List.map_map, List.mem_map, Function.comp_apply] using hz
    have hx : dec c * dec r = x := by rw [hrz, ← enc_inj, hze]
    refine ⟨dec r, (hR.2.mem_iff hRL _).2 (List.mem_map.2 ⟨r, hr, rfl⟩), ?_⟩
    rw [← hx, mul_inv_cancel_right]
    exact (hQ.2.1 _).2 (by rwa [enc_dec hc])
  · have hb : (Nat.land mQ mInv).testBit (enc u) = true := by
      rw [testBit_land, (hQ.2.1 u).1 hu, (hInv u).2 ⟨h1, h2⟩]
      rfl
    have := congrArg (fun m => m.testBit (enc u)) (eq_of_beq chQR3)
    simp only [testBit_diffM, hb, Nat.zero_testBit, Bool.true_and, Bool.not_eq_false',
      testBit_lor, Bool.or_eq_true] at this
    rcases this with h | h | h
    · exact Or.inl (((hCls 1).2.1 u).2 h)
    · exact Or.inr (Or.inl (((hCls 2).2.1 u).2 h))
    · exact Or.inr (Or.inr (((hCls 4).2.1 u).2 h))
  · by_cases hx1 : x = 1
    · exact Or.inl hx1
    · have hb : (Nat.land mR mInv).testBit (enc x) = true := by
        rw [testBit_land, (hR.2.1 x).1 hx, (hInv x).2 ⟨h1, hx1⟩]
        rfl
      rw [eq_of_beq chQR4] at hb
      have := List.mem_singleton.1 (((rep_single (by decide : (34 : ℕ) < 512)).1 x).2 hb)
      exact Or.inr (this.trans dec34)

theorem factCent_holds : factCent := by
  have hc3 : ∀ i : Fin 3, invE (![3, 5, 6] i) = dec (![131, 256, 268] i) := by decide +kernel
  have hlt3 : ∀ i : Fin 3, ![131, 256, 268] i < 512 := by decide +kernel
  have chC := chCentC
  refine ⟨fun i g => ?_, fun i j => ?_, fun g => ?_, fun g => ?_, fun g => ?_⟩
  · rw [hc3, rep_maskOf (chC i) (hCent i).2 g, cmE g (hlt3 i)]
  · rw [length_filter_eq (hCent i).2 (hCent i).1.2.2.1 _ (P := Nat.land mInv (mCls j)) (fun x => by
      rw [testBit_land, Bool.and_eq_true, ← (hCls j).2.1 x, hInv x, and_assoc]),
      chCentCount i j]
  · rw [rep_maskOf (eq_of_beq chCVt) hVt.2 g, cmE g (by decide),
      (by decide +kernel : dec 8 = AlpE.gen 1 ^ 2)]
  · have hM0 : Rep (mMax 0) (ballMaxL.getD 0 []) := (hMax 0).2
    rw [rep_maskOf (eq_of_beq chCM0) hM0 g, cmE g (by decide),
      (by decide +kernel : dec 17 = AlpE.gen 0 * AlpE.gen 2)]
  · have hM1 : Rep (mMax 1) (ballMaxL.getD 1 []) := (hMax 1).2
    rw [rep_maskOf (eq_of_beq chCM1) hM1 g, cmE g (by decide),
      (by decide +kernel : dec 27 = xE)]

theorem factDerived_holds : factDerived := by
  refine ⟨fun x hx => (hPd.2.mem_iff hComm.2 x).1 hx, fun x => ?_⟩
  rw [hPd.2.1, eq_of_beq chDer, testBit_land, testBit_land, Bool.and_eq_true, Bool.and_eq_true,
    ← (hMax 0).2.1, ← (hMax 1).2.1, ← (hMax 3).2.1]
  exact Iff.rfl

theorem ordE (x : AlpE) : ordB8 x.d.val (enc (x ^ 2)) (enc (x ^ 4)) (enc (x ^ 8)) = true := by
  have h := forall_of_allB chOrd x
  have p2 : x ^ 2 = x * x := sq x
  have p4 : x ^ 4 = x ^ 2 * x ^ 2 := by rw [← pow_add]
  have p8 : x ^ 8 = x ^ 4 * x ^ 4 := by rw [← pow_add]
  simp only [p8, p4, p2, enc_mul, ← dC_enc]
  exact h

theorem beq0E (y : AlpE) : Nat.beq (enc y) 0 = true ↔ y = 1 := by
  rw [beqE y (by decide), dec_zero]

theorem nbF {a b : ℕ} : Nat.beq a b = false ↔ a ≠ b := by
  rw [← Bool.not_eq_true, Nat.beq_eq]

theorem encE0 (y : AlpE) : enc y = 0 ↔ y = 1 := by rw [← enc_one, enc_inj]

theorem encEc (y : AlpE) {c : ℕ} (hc : c < 512) : enc y = c ↔ y = dec c :=
  ⟨fun h => by rw [← h, dec_enc], fun h => by rw [h, enc_dec hc]⟩

theorem ordB8_spec (d : ℕ) (x2 x4 x8 : AlpE) (h : ordB8 d (enc x2) (enc x4) (enc x8) = true) :
    (d = 0 → x4 = 1) ∧ ((d = 1 ∨ d = 3) → x8 * x8 = 1 ∧ x8 ≠ 1) ∧
    ((d = 2 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7) → x8 = 1) ∧
    ((d = 2 ∨ d = 4 ∨ d = 6) → x4 = 1 → x2 ≠ 1 → x2 = dec 34) ∧
    (d = 5 → x4 = 1 → x2 ≠ 1 → x2 = dec 40) ∧ (d = 7 → x4 = 1 → x2 ≠ 1 → x2 = dec 10) := by
  simp only [ordB8, ← enc_mul, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', nbF,
    Nat.beq_eq, ne_eq, encE0, encEc x2 (by decide : (34 : ℕ) < 512),
    encEc x2 (by decide : (40 : ℕ) < 512), encEc x2 (by decide : (10 : ℕ) < 512)] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨fun hd => h1.resolve_left (not_not.2 hd), fun hd => h2.resolve_left (by omega),
    fun hd => h3.resolve_left (by omega), fun hd h4' h2' => ?_, fun hd h4' h2' => ?_,
    fun hd h4' h2' => ?_⟩
  · rcases h4 with ((h | h) | h) | h
    · omega
    · exact absurd h4' h
    · exact absurd h h2'
    · exact h
  · rcases h5 with ((h | h) | h) | h
    · exact absurd hd h
    · exact absurd h4' h
    · exact absurd h h2'
    · exact h
  · rcases h6 with ((h | h) | h) | h
    · exact absurd hd h
    · exact absurd h4' h
    · exact absurd h h2'
    · exact h

theorem factOrders_holds : factOrders := by
  have S := fun x => ordB8_spec _ _ _ _ (ordE x)
  have p16 : ∀ x : AlpE, x ^ 16 = x ^ 8 * x ^ 8 := fun x => by rw [← pow_add]
  have v : ∀ (x : AlpE) (k : Fin 8), x.d = k → x.d.val = k.val := fun x k h => by rw [h]
  refine ⟨fun x hd => (S x).1 (v x 0 hd), fun x hd => ?_, fun x hd => ?_,
    fun x hd h4 h2 => ?_, fun x hd h4 h2 => ?_, fun x hd h4 h2 => ?_⟩
  · rw [p16]
    exact (S x).2.1 (hd.imp (v x 1) (v x 3))
  · refine (S x).2.2.1 ?_
    rcases hd with h | h | h | h | h
    exacts [Or.inl (v x 2 h), Or.inr (Or.inl (v x 4 h)), Or.inr (Or.inr (Or.inl (v x 5 h))),
      Or.inr (Or.inr (Or.inr (Or.inl (v x 6 h)))), Or.inr (Or.inr (Or.inr (Or.inr (v x 7 h))))]
  · rw [(S x).2.2.2.1 (hd.imp (v x 2) (Or.imp (v x 4) (v x 6))) h4 h2, dec34]
  · rw [(S x).2.2.2.2.1 (v x 5 hd) h4 h2]
    decide +kernel
  · rw [(S x).2.2.2.2.2 (v x 7 hd) h4 h2]
    decide +kernel

theorem factCV_holds : factCV := by
  intro i
  refine ⟨(hCV i).1, fun g hd => ?_⟩
  have h := forall_of_allB (chCVc i) g
  have hd' : dC (enc g) = 0 := by rw [dC_enc, hd]; rfl
  have hb : Nat.beq 0 0 = true := rfl
  rw [hd', dec_enc, bitB_eq, hb, Bool.not_true, Bool.false_or, iffB_iff] at h
  exact h.trans ((hCV i).2.1 g).symm

theorem wL_lt : ∀ c ∈ wL, c < 512 := by decide +kernel

theorem factW_holds : factW := by
  have hWL : Rep mW (wL.map dec) := by
    have := rep_lorL wL wL_lt
    rwa [eq_of_beq chWL] at this
  have hdz : ∀ g : AlpE, Nat.beq (dC (enc g)) 0 = true ↔ g.d = 0 := fun g => by
    rw [Nat.beq_eq, dC_enc, Fin.ext_iff]
    rfl
  refine ⟨fun x hd => ?_, fun g => ?_, fun g => ?_, fun g w hw => ?_⟩
  · rw [rep_maskOf (eq_of_beq chW1) hW.2 x, Bool.and_eq_true, hdz, ← enc_mul, beq0E]
    exact ⟨fun h => ⟨hd, h⟩, fun h => h.2⟩
  · have h := forall_of_allB chW2 g
    rw [iffB_iff, Bool.and_eq_true, Bool.and_eq_true, cmE g (by decide), cmE g (by decide),
      cmE g (by decide), hdz] at h
    rw [← h, (by decide +kernel : genWE = [dec 32, dec 8, dec 2])]
    simp [and_assoc]
  · have h := forall_of_allB chW3 g
    rw [iffB_iff, Bool.and_eq_true, Bool.and_eq_true, cmE g (by decide), cmE g (by decide),
      cmE g (by decide), hdz] at h
    rw [← h, (by decide +kernel : genVE = [dec 16, dec 4, dec 1])]
    simp [and_assoc]
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ((hW.2.mem_iff hWL w).1 hw)
    have h := forall_of_allB chW4 g
    rw [wConjB, allL_iff] at h
    have hb := h c hc
    rw [bitB_eq] at hb
    have hi : dec (invK (enc g)) = g⁻¹ := by
      rw [dec, ← decN_inv expK_true]
      exact congrArg (·⁻¹) (dec_enc g)
    have he : dec (mulK (mulK (enc g) c) (invK (enc g))) = g * dec c * g⁻¹ := by
      rw [dec_mulK, dec_mulK, dec_enc, hi]
    rw [hW.2.1, ← he, enc_dec (mulK_lt _ _)]
    exact hb

theorem f2Check_true : f2Check = true := by
  simp only [f2Check, decide_eq_true factCentre_holds, decide_eq_true factClasses_holds,
    decide_eq_true factNonV_holds, decide_eq_true factSub_holds, decide_eq_true factMax_holds,
    decide_eq_true factQR_holds, decide_eq_true factCent_holds, decide_eq_true factDerived_holds,
    decide_eq_true factOrders_holds, decide_eq_true factCV_holds, decide_eq_true factW_holds,
    Bool.and_self]

end CFSG.KC.ONanF2.Glue
