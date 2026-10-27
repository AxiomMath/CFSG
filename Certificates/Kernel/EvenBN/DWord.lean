module

public import Certificates.Kernel.Sporadic.Tits.Words2264
public import Certificates.Data.TitsFiveLocal
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelEvenBN

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.Sporadic.Schreier.Tits
open CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native CertificateChecks.KernelSpor.Tits2264
open Certificates.MaxD2Perm Certificates.FusD2Perm

@[expose] noncomputable def wTP (w : List Int) : Nat :=
  wordK 1755 11 (mask 11) (pidn 1755 11) Dk DIk w

theorem wordT_eq_wordA {n : Nat} {gs gi : Array (Array Nat)} (hs : gi.size = gs.size) :
    ∀ w : List Int, lettersOK gs.size w = true → wordT n gs gi w = wordA n gs gi w
  | [], _ => rfl
  | z :: w, h => by
    simp only [lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at h
    obtain ⟨⟨hz0, hzk⟩, hw⟩ := h
    have ih := wordT_eq_wordA (n := n) hs w (by simpa only [lettersOK] using hw)
    change comp n _ (wordT n gs gi w) = compA n (letterA gs gi z) (wordA n gs gi w)
    rw [ih]
    change compA n _ _ = compA n _ _
    congr 1
    unfold letterA
    by_cases hz : 0 < z
    · rw [ite_eq_left hz, ite_eq_left hz, Array.getD_eq_getD_getElem?,
        getElem!_pos gs (z.toNat - 1) (by omega), Array.getElem?_eq_getElem (by omega)]
      rfl
    · rw [ite_eq_right hz, ite_eq_right hz, Array.getD_eq_getD_getElem?,
        getElem!_pos gi ((-z).toNat - 1) (by omega), Array.getElem?_eq_getElem (by omega)]
      rfl

theorem gT_bind : titsDData.gT.size = 2 ∧ ∀ k < 2, titsDData.gT[k]! = unpack 1755 11 (Dk k) := by
  refine ⟨rfl, fun k hk => ?_⟩
  interval_cases k
  · exact titsDArr_eq (by decide)
  · exact titsDArr_eq (by decide)

theorem szOK1755 : szOK 1755 11 = true := by quickRfl

theorem wT_eq {w : List Int} (hl : lettersK 2 w = true) :
    wT titsDData w = unpack 1755 11 (wTP w) := by
  have h : wordEqK 1755 11 (mask 11) (pidn 1755 11) Dk DIk 2 w (wTP w) = true := by
    unfold wordEqK
    rw [szOK1755, hl, wTP, Nat.beq_refl]
  obtain ⟨e, hlo⟩ := wordEqK_sound gT_bind dArrs_perm h
  unfold wT
  rw [wordT_eq_wordA (by simp [Certificates.MaxD2Perm.giT]) w (by rw [gT_bind.1]; exact hlo)]
  exact e

end CertificateChecks.KernelEvenBN

end
