module

public import Certificates.Kernel.Sporadic.Fi24E.Data
public import Certificates.Kernel.Sporadic.Fi24ThreeO.Facts
public import CFSG.Certificates.Kernel.Spor.Fi24ESound
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_json CFSG.KD.Fi24E.Ck "Certificates/Kernel/Sporadic/Fi24E/data/fx.json" 368573
  17745223704333308909 (zR1 : Nat) (zR2 : Nat) (zR3 : Nat) (zR4 : Nat)

public section

namespace CFSG.KD.Fi24E.Ck

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24Net CFSG.KC.Fi24FixP CFSG.KC.Fi24ThreeO
  CFSG.KC.Fi24Oct CFSG.KC.Fi24E CFSG.KS.Fi24ThreeO CFSG.KD.Fi24Net CFSG.KD.Fi24Kit CFSG.KD.Fi24Oct
  CFSG.KD.Fi24ThreeO CFSG.KD.Fi24E

@[expose] noncomputable def fxAgr (cs ks : List Nat) (a : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun a => a)
    (fun k _ ih a => strictN (Nat.xor (wkC NW NT cs (idPl19 k)) (idPl19 k)) (fun d =>
      strictN (Nat.xor a (Nat.land a d)) ih)) ks a

@[expose] noncomputable def fxAgrL (css kss : List (List Nat)) : Nat :=
  List.rec (motive := fun _ => List (List Nat) → Nat) (fun _ => ptsM)
    (fun cs _ ih kss => List.rec (motive := fun _ => Nat) (ih List.nil)
      (fun ks t _ => strictN (ih t) (fxAgr cs ks)) kss) css kss

@[expose] noncomputable def fxAgrOK (css kss : List (List Nat)) (P : Nat) : Bool :=
  letB (fxAgrL css kss) (fun A => Nat.beq (Nat.land A P) A)

@[expose] noncomputable def fxPl : List (List Nat) :=
  [[7, 5, 0], [8, 14], [], [6], [], [12, 10], [8], [13, 2], [4, 7], [1, 0], [11]]

theorem fxA_t : fxAgrOK fcs fxPl (plOf pts) = true := by quickRfl

theorem testBit_fxAgr {cs : List Nat} {x : Nat} (hx : x < 524288) (hc : cP NW NT cs x = x) :
    ∀ (ks : List Nat) (a : Nat), (fxAgr cs ks a).testBit x = a.testBit x
  | [], _ => rfl
  | k :: ks, a => by
    have e : fxAgr cs (k :: ks) a =
        fxAgr cs ks (a ^^^ (a &&& (wkC NW NT cs (idPl19 k) ^^^ idPl19 k))) := by
      change strictN _ (fun d => strictN (Nat.xor a (Nat.land a d)) (fxAgr cs ks)) = _
      rw [CFSG.KS.Fi24NetPt.strictN_eq, CFSG.KS.Fi24NetPt.strictN_eq]
      rfl
    rw [e, testBit_fxAgr hx hc ks, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_xor,
      testBit_wkC vn cs _ hx, hc, Bool.xor_self, Bool.and_false, Bool.xor_false]

theorem testBit_fxAgrL {x : Nat} (hx : x < 306936) :
    ∀ (css kss : List (List Nat)), (∀ cs ∈ css, cP NW NT cs x = x) →
      (fxAgrL css kss).testBit x = true
  | [], _, _ => ptsM_bit hx
  | cs :: css, [], h => testBit_fxAgrL hx css [] fun c hc => h c (List.mem_cons_of_mem cs hc)
  | cs :: css, ks :: t, h => by
    have e : fxAgrL (cs :: css) (ks :: t) = fxAgr cs ks (fxAgrL css t) := by
      change strictN (fxAgrL css t) (fxAgr cs ks) = _
      rw [CFSG.KS.Fi24NetPt.strictN_eq]
    rw [e, testBit_fxAgr (by omega) (h cs List.mem_cons_self) ks]
    exact testBit_fxAgrL hx css t fun c hc => h c (List.mem_cons_of_mem cs hc)

theorem fixAllOK_of_fxAgr {css kss : List (List Nat)} {P : Nat} (h : fxAgrOK css kss P = true) :
    fixAllOK NW NT css P = true := by
  have hl : ∀ (v : Nat) (k : Nat → Bool), letB v k = k v := fun v k => by cases v <;> rfl
  unfold fxAgrOK at h
  unfold fixAllOK
  rw [hl] at h ⊢
  have eA : fxAgrL css kss &&& P = fxAgrL css kss := Nat.eq_of_beq_eq_true h
  have e : fixAll NW NT css &&& P = fixAll NW NT css := by
    refine Nat.eq_of_testBit_eq fun x => ?_
    rw [Nat.testBit_and]
    cases hb : (fixAll NW NT css).testBit x
    · rfl
    · obtain ⟨hx, hf⟩ := (CFSG.KS.Fi24E.testBit_fixAll vn css x).1 hb
      have hA := testBit_fxAgrL hx css kss hf
      rw [← eA, Nat.testBit_and, Bool.and_eq_true] at hA
      rw [hA.2]
      rfl
  have hn : ∀ u v : Nat, Nat.land u v = u &&& v := fun _ _ => rfl
  rw [hn, e]
  exact Nat.beq_refl _

theorem fx_t : fx = true := fixAllOK_of_fxAgr (css := fcs) (kss := fxPl) (P := plOf pts) fxA_t

theorem zA1_t : Nat.beq (fxAgr zc [0, 1, 2, 3] ptsM) zR1 = true := by quickRfl

theorem zA2_t : Nat.beq (fxAgr zc [4, 5, 6, 7] zR1) zR2 = true := by quickRfl

theorem zA3_t : Nat.beq (fxAgr zc [8, 9, 10, 11] zR2) zR3 = true := by quickRfl

theorem zA4_t : Nat.beq (fxAgr zc [12, 13, 14, 15] zR3) zR4 = true := by quickRfl

theorem zA5_t : Nat.beq (popcount (fxAgr zc [16, 17, 18] zR4) 524288) z = true := by quickRfl

theorem fxAgr_cons (cs : List Nat) (k : Nat) (ks : List Nat) (a : Nat) :
    fxAgr cs (k :: ks) a = fxAgr cs ks (a ^^^ (a &&& (wkC NW NT cs (idPl19 k) ^^^ idPl19 k))) := by
  change strictN _ (fun d => strictN (Nat.xor a (Nat.land a d)) (fxAgr cs ks)) = _
  rw [CFSG.KS.Fi24NetPt.strictN_eq, CFSG.KS.Fi24NetPt.strictN_eq]
  rfl

theorem fxAgr_append (cs : List Nat) : ∀ (ks ls : List Nat) (a : Nat),
    fxAgr cs (ks ++ ls) a = fxAgr cs ls (fxAgr cs ks a)
  | [], _, _ => rfl
  | k :: ks, ls, a => by
    rw [List.cons_append, fxAgr_cons, fxAgr_cons, fxAgr_append cs ks ls]

theorem testBit_fxAgr_le (cs : List Nat) {x : Nat} : ∀ (ks : List Nat) (a : Nat),
    (fxAgr cs ks a).testBit x = true → a.testBit x = true
  | [], _, h => h
  | k :: ks, a, h => by
    rw [fxAgr_cons] at h
    have h2 := testBit_fxAgr_le cs ks _ h
    rw [Nat.testBit_xor, Nat.testBit_and] at h2
    cases ha : a.testBit x
    · rw [ha] at h2
      simp at h2
    · rfl

theorem testBit_fxAgr_iff {cs : List Nat} {x : Nat} (hx : x < 524288) : ∀ (ks : List Nat),
    (∀ k ∈ ks, k < 19) → ∀ (a : Nat), ((fxAgr cs ks a).testBit x = true ↔
      a.testBit x = true ∧ ∀ k ∈ ks, (cP NW NT cs x).testBit k = x.testBit k)
  | [], _, a => by simp [fxAgr]
  | k :: ks, hks, a => by
    rw [fxAgr_cons, testBit_fxAgr_iff hx ks (fun k' hk' => hks k' (List.mem_cons_of_mem k hk')),
      List.forall_mem_cons, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_xor, testBit_wkC vn cs _ hx,
      CFSG.KS.Fi24FixP.testBit_idPl19 (hks k List.mem_cons_self),
      CFSG.KS.Fi24FixP.testBit_idPl19 (hks k List.mem_cons_self), decide_eq_true (cP_lt vn cs hx),
      decide_eq_true hx, Bool.true_and, Bool.true_and]
    cases a.testBit x <;> cases (cP NW NT cs x).testBit k <;> cases x.testBit k <;> simp

theorem fixC_eq_fxAgr (cs : List Nat) :
    fixC NW NT cs = fxAgr cs [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18] ptsM := by
  refine Nat.eq_of_testBit_eq fun x => ?_
  by_cases hx : x < 524288
  · refine Bool.eq_iff_iff.2 ?_
    rw [testBit_fixC vn, testBit_fxAgr_iff hx _ (by decide), CFSG.KS.Fi24E.testBit_ptsM,
      decide_eq_true_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun k _ => by rw [h2]⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, Nat.eq_of_testBit_eq fun i => ?_⟩
      by_cases hi : i < 19
      · exact h2 i (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
      · have h19 : (524288 : Nat) ≤ 2 ^ i :=
          Nat.pow_le_pow_right (n := 2) (by decide) (Nat.le_of_not_lt hi)
        rw [Nat.testBit_lt_two_pow (by have := cP_lt vn cs hx; omega),
          Nat.testBit_lt_two_pow (by omega)]
  · have h1 : (fixC NW NT cs).testBit x = false := by
      cases e : (fixC NW NT cs).testBit x
      · rfl
      · exact absurd ((testBit_fixC vn cs x).1 e).1 (by omega)
    have h2 : (fxAgr cs [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]
        ptsM).testBit x = false := by
      cases e : (fxAgr cs [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]
          ptsM).testBit x
      · rfl
      · have := testBit_fxAgr_le cs _ _ e
        rw [CFSG.KS.Fi24E.testBit_ptsM] at this
        exact absurd (of_decide_eq_true this) (by omega)
    rw [h1, h2]

theorem zz_t : zz = true := by
  have e : fixS (walkP (plC NW NT) zc) = fxAgr zc [16, 17, 18] zR4 := by
    have e0 : fixS (walkP (plC NW NT) zc) = fixC NW NT zc := rfl
    have eL : [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18] =
        [0, 1, 2, 3] ++ ([4, 5, 6, 7] ++ ([8, 9, 10, 11] ++ ([12, 13, 14, 15] ++ [16, 17, 18]))) := rfl
    rw [e0, fixC_eq_fxAgr, eL, fxAgr_append, fxAgr_append, fxAgr_append, fxAgr_append,
      Nat.eq_of_beq_eq_true zA1_t, Nat.eq_of_beq_eq_true zA2_t, Nat.eq_of_beq_eq_true zA3_t,
      Nat.eq_of_beq_eq_true zA4_t]
  unfold zz Fi24FixP.fixOK
  rw [e]
  exact zA5_t

end CFSG.KD.Fi24E.Ck

end
