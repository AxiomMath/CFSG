module

public import Certificates.Kernel.Gen2711.ONTW
public import CFSG.Certificates.Kernel.Spor.OrdSound
public import CFSG.Certificates.Kernel.CosetLat.MatEnc
import all CFSG.Certificates.Kernel.Spor.OrdSound

public section

namespace CFSG.KC.OpsLayK

open CFSG.KC.LQT CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.KC.Ord CFSG.KS.Ord

variable (c : Lay)

theorem lay_mul_sound (hc : c.ok = true) {A B : Nat} (hA : Canon c.p c.d c.w A)
    (hB : Canon c.p c.d c.w B) :
    Canon c.p c.d c.w (c.mul A B) ∧
      ordMat c.p c.d c.w c.S (c.mul A B) = ordMat c.p c.d c.w c.S A * ordMat c.p c.d c.w c.S B :=
  mulR_sound hc hA hB

theorem lay_canon_inj (hc : c.ok = true) {A B : Nat} (hA : Canon c.p c.d c.w A)
    (hB : Canon c.p c.d c.w B) (h : ordMat c.p c.d c.w c.S A = ordMat c.p c.d c.w c.S B) :
    A = B := by
  obtain ⟨-, hS, hw, -⟩ := consts_facts (show constsOK c.p c.w c.S c.d c.T c.L c.H c.CM c.RM c.ONE
    c.LV c.HV = true from hc)
  rw [hS] at h
  exact CFSG.KC.CosetLat.canon_eq_of_ordMat hw hA hB h

theorem lay_one (hc : c.ok = true) :
    Canon c.p c.d c.w c.ONE ∧ ordMat c.p c.d c.w c.S c.ONE = 1 :=
  one_sound hc

theorem lay_mul_assoc (hc : c.ok = true) {A B C : Nat} (hA : Canon c.p c.d c.w A)
    (hB : Canon c.p c.d c.w B) (hC : Canon c.p c.d c.w C) :
    c.mul (c.mul A B) C = c.mul A (c.mul B C) := by
  have hAB := lay_mul_sound c hc hA hB
  have hBC := lay_mul_sound c hc hB hC
  have h1 := lay_mul_sound c hc hAB.1 hC
  have h2 := lay_mul_sound c hc hA hBC.1
  refine lay_canon_inj c hc h1.1 h2.1 ?_
  rw [h1.2, h2.2, hAB.2, hBC.2, mul_assoc]

theorem lay_mul_one (hc : c.ok = true) {A : Nat} (hA : Canon c.p c.d c.w A) :
    c.mul A c.ONE = A := by
  have h := lay_mul_sound c hc hA (lay_one c hc).1
  refine lay_canon_inj c hc h.1 hA ?_
  rw [h.2, (lay_one c hc).2, mul_one]

theorem lay_one_mul (hc : c.ok = true) {A : Nat} (hA : Canon c.p c.d c.w A) :
    c.mul c.ONE A = A := by
  have h := lay_mul_sound c hc (lay_one c hc).1 hA
  refine lay_canon_inj c hc h.1 hA ?_
  rw [h.2, (lay_one c hc).2, one_mul]

@[expose] def LetCanon (T : List Nat) (u : Word) : Prop :=
  ∀ x ∈ u, Canon c.p c.d c.w (powK c (getR c T x.1) x.2)

theorem evalWL_canon (hc : c.ok = true) (T : List Nat) :
    ∀ u : Word, LetCanon c T u → Canon c.p c.d c.w (evalWL c T u)
  | [], _ => (lay_one c hc).1
  | x :: u, h => (lay_mul_sound c hc (h x List.mem_cons_self)
      (evalWL_canon hc T u fun y hy => h y (List.mem_cons_of_mem _ hy))).1

theorem evalWL_append (hc : c.ok = true) (T : List Nat) :
    ∀ u v : Word, LetCanon c T u → LetCanon c T v →
      evalWL c T (u ++ v) = c.mul (evalWL c T u) (evalWL c T v)
  | [], v, _, hv => (lay_one_mul c hc (evalWL_canon c hc T v hv)).symm
  | x :: u, v, hu, hv => by
    have hu' : LetCanon c T u := fun y hy => hu y (List.mem_cons_of_mem _ hy)
    rw [List.cons_append, evalWL, evalWL, evalWL_append hc T u v hu' hv,
      lay_mul_assoc c hc (hu x List.mem_cons_self) (evalWL_canon c hc T u hu')
        (evalWL_canon c hc T v hv)]

@[expose] def runWS : List Op → List (Option Word) → List (Option Word)
  | [], W => W
  | .mul i j k :: p, W =>
    runWS p (W.set k ((W.getD i none).bind fun u => (W.getD j none).map fun v => u ++ v))
  | .pow _ _ k :: p, W => runWS p (W.set k none)

@[expose] def WInv (T R : List Nat) (W : List (Option Word)) : Prop :=
  R.length = W.length ∧
    ∀ i u, W.getD i none = some u → LetCanon c T u ∧ getR c R i = evalWL c T u

theorem getD_set_none {W : List (Option Word)} {k m : Nat} {a : Option Word} {u : Word}
    (h : (W.set k a).getD m none = some u) :
    (m = k ∧ k < W.length ∧ a = some u) ∨ (m ≠ k ∧ W.getD m none = some u) := by
  by_cases hm : m = k
  · subst hm
    left
    by_cases hk : m < W.length
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_set_self hk, Option.getD_some] at h
      exact ⟨rfl, hk, h⟩
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using hk),
        Option.getD_none] at h
      cases h
  · right
    refine ⟨hm, ?_⟩
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hm)] using h

theorem runF_runWS (hc : c.ok = true) (T : List Nat) :
    ∀ (p : List Op) (R : List Nat) (W : List (Option Word)), WInv c T R W →
      WInv c T (runF c p R) (runWS p W)
  | [], _, _, h => h
  | .mul i j k :: p, R, W, ⟨hl, h⟩ => by
    change WInv c T (runF c p (R.set k (c.mul (getR c R i) (getR c R j)))) (runWS p _)
    refine runF_runWS hc T p _ _ ⟨by rw [List.length_set, List.length_set, hl], fun m u hu => ?_⟩
    rcases getD_set_none hu with ⟨rfl, hk, ha⟩ | ⟨hm, hu⟩
    · obtain ⟨u1, h1, ha⟩ := Option.bind_eq_some_iff.mp ha
      obtain ⟨u2, h2, rfl⟩ := Option.map_eq_some_iff.mp ha
      obtain ⟨c1, e1⟩ := h i u1 h1
      obtain ⟨c2, e2⟩ := h j u2 h2
      have cu : LetCanon c T (u1 ++ u2) := fun x hx => by
        rcases List.mem_append.mp hx with hx | hx
        · exact c1 x hx
        · exact c2 x hx
      refine ⟨cu, ?_⟩
      rw [getR_set_eq c (by rw [hl]; exact hk), e1, e2, evalWL_append c hc T u1 u2 c1 c2]
    · rw [getR_set_neW c R (Ne.symm hm)]
      exact h m u hu
  | .pow e i k :: p, R, W, ⟨hl, h⟩ => by
    change WInv c T (runF c p (R.set k (powK c (getR c R i) e))) (runWS p _)
    refine runF_runWS hc T p _ _ ⟨by rw [List.length_set, List.length_set, hl], fun m u hu => ?_⟩
    rcases getD_set_none hu with ⟨-, -, ha⟩ | ⟨hm, hu⟩
    · cases ha
    · rw [getR_set_neW c R (Ne.symm hm)]
      exact h m u hu

@[expose] def initW (L : Word) (n : Nat) : List (Option Word) :=
  L.foldr (fun x W => W.set (pReg x.1 x.2) (some [x])) (List.replicate n none)

theorem getD_initW : ∀ (L : Word) (n i : Nat) (u : Word), (initW L n).getD i none = some u →
    ∃ x ∈ L, i = pReg x.1 x.2 ∧ u = [x]
  | [], n, i, u, h => by
    simp only [initW, List.foldr_nil, List.getD_eq_getElem?_getD, List.getElem?_replicate] at h
    split at h <;> simp at h
  | x :: L, n, i, u, h => by
    rcases getD_set_none (W := initW L n) h with ⟨rfl, -, ha⟩ | ⟨-, h'⟩
    · exact ⟨x, List.mem_cons_self, rfl, (Option.some.inj ha).symm⟩
    · obtain ⟨y, hy, e1, e2⟩ := getD_initW L n i u h'
      exact ⟨y, List.mem_cons_of_mem _ hy, e1, e2⟩

theorem getR_runF_notTgt :∀ (p : List Op) (R : List Nat) (i : Nat),
    (∀ o ∈ p, Op.tgt o ≠ i) → getR c (runF c p R) i = getR c R i
  | [], _, _, _ => rfl
  | o :: p, R, i, h => by
    change getR c (runF c p (R.set (Op.tgt o) (stepV c R o))) i = _
    rw [getR_runF_notTgt p _ i fun o' ho' => h o' (List.mem_cons_of_mem _ ho'),
      getR_set_neW c R (h o List.mem_cons_self)]

end CFSG.KC.OpsLayK

end
