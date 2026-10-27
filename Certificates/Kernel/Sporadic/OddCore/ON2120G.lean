module

public import Certificates.Kernel.Sporadic.OddCore.ON2119B
public import CFSG.Sporadic.ONOddCore.GraphDefs

public section

set_option linter.unusedSectionVars false

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON2119

open CFSG.ONSchreier.Native hiding posArr
open CFSG.ONSchreier CFSG.Sporadic.ON.Native CFSG.Sporadic.ONOddCore
open CFSG.KS.TW CFSG.KS.PW CertificateChecks.KernelSpor.ON3
open CFSG.KC.Enum hiding pcomp
open CertificateChecks.KernelSpor.ON (TT UU)

@[expose] noncomputable def gsF (k : Nat) (G : Nat → Nat → Nat) (i x : Nat) : Nat :=
  nIf(Nat.blt i k, G i x, x)

@[expose] noncomputable def wordF (k : Nat) (G : Nat → Nat → Nat) (w : List Nat) (x : Nat) : Nat :=
  w.foldr (fun l y => gsF k G (Nat.sub l 1) y) x

theorem gsF_lt {k i x : Nat} {G : Nat → Nat → Nat} (h : i < k) : gsF k G i x = G i x := by
  unfold gsF
  have hb : Nat.blt i k = true := by rw [Nat.blt_eq]; exact h
  rw [hb]

theorem gsF_ge {k i x : Nat} {G : Nat → Nat → Nat} (h : ¬ i < k) : gsF k G i x = x := by
  unfold gsF
  have hb : Nat.blt i k = false := by
    cases hc : Nat.blt i k with
    | false => rfl
    | true => rw [Nat.blt_eq] at hc; exact absurd hc h
  rw [hb]

theorem posArr_nil (n : Nat) (gs : Array (Array Nat)) :
    CFSG.Sporadic.ONOddCore.posArr n gs [] = pid n := rfl

theorem posArr_cons (n : Nat) (gs : Array (Array Nat)) (l : Nat) (w : List Nat) :
    CFSG.Sporadic.ONOddCore.posArr n gs (l :: w) =
      pcomp n (gs.getD (l - 1) (pid n)) (CFSG.Sporadic.ONOddCore.posArr n gs w) := rfl

section G


theorem good_tab {t : Array Nat} {F G : Nat → Nat} (ht : Good t F)
    (hG : ∀ x < 245520, t[x]! = G x ∧ G x < 245520) : Good t G :=
  ⟨ht.1, ht.2.1, hG⟩

theorem good_hA {i : Nat} (hi : i < 3) : Good (wordArrs Data.MWords)[i]! (mG i) := by
  have hw : plettersOK 7 Data.MWords[i]! = true := by interval_cases i <;> decide
  have h := good_word hw
  rw [← wordArrs_get (by rw [mw_size]; exact hi)] at h
  exact good_tab h (m_get hi)

theorem good_getD {gs : Array (Array Nat)} {G : Nat → Nat → Nat}
    (hg : ∀ i < gs.size, Good gs[i]! (G i)) (i : Nat) :
    Good (gs.getD i (pid nPts)) (gsF gs.size G i) := by
  by_cases h : i < gs.size
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h, Option.getD_some,
      ← getElem!_pos gs i h]
    have e : gsF gs.size G i = G i := by funext x; exact gsF_lt h
    rw [e]
    exact hg i h
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega), Option.getD_none]
    have e : gsF gs.size G i = fun x => x := by funext x; exact gsF_ge h
    rw [e]
    exact good_pid

theorem good_posArr {gs : Array (Array Nat)} {G : Nat → Nat → Nat}
    (hg : ∀ i < gs.size, Good gs[i]! (G i)) :
    ∀ w : List Nat, Good (posArr nPts gs w) (wordF gs.size G w) := by
  intro w
  induction w with
  | nil =>
    have e := posArr_nil nPts gs
    have hf : wordF gs.size G [] = fun x => x := by funext x; rfl
    rw [e, hf]
    exact good_pid
  | cons l w ih =>
    have e := posArr_cons nPts gs l w
    have hf : wordF gs.size G (l :: w) = fun x => gsF gs.size G (l - 1) (wordF gs.size G w x) := by
      funext x; rfl
    rw [e, hf]
    exact good_pcomp (good_getD hg (l - 1)) ih

theorem posPt_eq {gs : Array (Array Nat)} {G : Nat → Nat → Nat}
    (hg : ∀ i < gs.size, Good gs[i]! (G i)) :
    ∀ (w : List Nat) (p : Nat), p < 245520 →
      posPt gs w p = wordF gs.size G w p ∧ wordF gs.size G w p < 245520
  | [], p, hp => ⟨rfl, hp⟩
  | l :: w, p, hp => by
    obtain ⟨e, hlt⟩ := posPt_eq hg w p hp
    have e1 : posPt gs (l :: w) p = (gs.getD (l - 1) #[])[posPt gs w p]?.getD (posPt gs w p) := rfl
    have e2 : wordF gs.size G (l :: w) p = gsF gs.size G (l - 1) (wordF gs.size G w p) := rfl
    rw [e1, e2, e]
    by_cases h : l - 1 < gs.size
    · have hg' := hg (l - 1) h
      rw [getElem!_pos gs _ h] at hg'
      have hs := hg'.1
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h, Option.getD_some,
        getElem?_pos _ _ (by rw [hs]; exact hlt), Option.getD_some,
        ← getElem!_pos _ _ (by rw [hs]; exact hlt), gsF_lt h]
      exact hg'.2.2 _ hlt
    · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (xs := gs) (by omega),
        Option.getD_none, gsF_ge h]
      exact ⟨by simp, hlt⟩

theorem good_qPow : ∀ k : Nat, Good (qPowArr k) (fun x => Nat.repeat QT k x)
  | 0 => good_pid
  | k + 1 => by
    have h1 : Good qArr QT :=
      good_tab (good_word (w := Data.centerGeneratorWord) (by decide +kernel)) q_get
    have hf : (fun x => Nat.repeat QT (k + 1) x) = fun x => QT (Nat.repeat QT k x) := by
      funext x; rfl
    rw [hf]
    exact good_pcomp h1 (good_qPow k)

end G

end CertificateChecks.KernelSpor.ON2119

end
