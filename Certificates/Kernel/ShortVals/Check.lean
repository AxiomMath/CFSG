module

public import Certificates.Kernel.ShortVals.Data
public import CFSG.Certificates.Kernel.ShortVals.Sound
public import CFSG.Certificates.Kernel.Common.Cover
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelShortVals

open CFSG.KC.ShortVals CFSG.KD.ShortVals CFSG.YGroups.Y443Native
open CFSG.Monster.AxisCount.Native CFSG.Monster.B.Rep4371.Native

theorem tabA : ∀ i < 24, ∀ j < 24, ((aK AP i j : ℕ) : ℤ) = Aent i j := by decide +kernel

theorem tabWK : ∀ t < 2048, wAt WT t = wordK (2 * t) := by decide +kernel

theorem tabW : ∀ t < 2048, wAt WT t = wordN (2 * t) :=
  fun t ht => (tabWK t ht).trans (wordK_eq _)

theorem tabOctK : ((List.range 4096).filter fun a => popcN 24 (wordK a) == 8).map
      (fun a => (wordK a, suppList (wordK a))) =
    (List.range 759).map (fun o => (wAt OWT o, (List.range 8).map (cAt OC o))) := by
  decide +kernel

theorem tabOct : (octTab ()).toList.map (fun a => (wordN a, suppList (wordN a))) =
    (List.range 759).map (fun o => (wAt OWT o, (List.range 8).map (cAt OC o))) := by
  have h := tabOctK
  simp only [wordK_eq] at h
  unfold octTab
  rw [List.toList_toArray]
  exact h

theorem tabOct_at {o : ℕ} (ho : o < 759) : wAt OWT o = wordN (octTab ())[o]! ∧
    suppList (wordN (octTab ())[o]!) = (List.range 8).map (cAt OC o) := by
  have h := congrArg (fun l => l[o]?) tabOct
  simp only [List.getElem?_map, List.getElem?_range ho, Option.map_some] at h
  cases hx : (octTab ()).toList[o]? with
  | none =>
    rw [hx] at h
    exact absurd h (by simp)
  | some a =>
    rw [hx, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    have ha : (octTab ())[o]! = a := by
      rw [Array.getElem?_toList] at hx
      rw [getElem!_def, hx]
    rw [ha]
    exact ⟨h.1.symm, h.2⟩

theorem tabOW : ∀ o < 759, wAt OWT o = wordN (octTab ())[o]! := fun _ ho => (tabOct_at ho).1

theorem tabOC : ∀ o < 759, suppList (wordN (octTab ())[o]!) = (List.range 8).map (cAt OC o) :=
  fun _ ho => (tabOct_at ho).2

theorem tabET : ∀ m < 64, eAt ET m = (evenTab ())[m]! := by decide +kernel

theorem tabPT : ∀ q < 276, pAt PT q 0 = ((pairTab ())[q]!).1 ∧ pAt PT q 1 = ((pairTab ())[q]!).2 ∧
    ((pairTab ())[q]!).1 < 24 ∧ ((pairTab ())[q]!).2 < 24 := by decide +kernel

theorem chkPair : ∀ q < 276, pairOK AP PT VP RP PP q = true := by kc_cover 276

theorem chkOdd : ∀ t < 2048, oddOK AP WT VP RP PP t = true := by kc_cover 64

theorem chkOct : ∀ o < 759, octOK AP OWT OC ET VP RP PP o = true := by kc_cover 24

theorem chkInc : ∀ k < 98279, incOK VP k = true := by kc_cover 1024

theorem shortValsOK_true : shortValsOK () = true :=
  shortValsOK_of_checks AP WT OWT OC ET PT VP RP PP tabA tabW tabOW tabOC tabET tabPT chkPair
    chkOdd chkOct chkInc

end CertificateChecks.KernelShortVals

end
