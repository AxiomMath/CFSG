module

public import Certificates.Kernel.Sporadic.Fi24Sev.Facts
public import Certificates.Kernel.Sporadic.Fi24Sev.Words

public section

namespace CFSG.KD.Fi24Sev.Seven

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
open CFSG.Sporadic.Fi24 (J)
open CFSG.KD.Fi24ThreeO.Group CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24SevenNative


theorem sl_codes : ∀ e ∈ CFSG.KD.Fi24Sev.sl, ∀ l ∈ e.2.2, l < 26 := by decide +kernel

theorem sl_words : ∀ e ∈ CFSG.KD.Fi24Sev.sl, e.1 < 1087 ∧ CFSG.KD.F24S.W7.getD e.1 [] = e.2.1 := by
  decide +kernel

theorem sl_y : ∃ e ∈ CFSG.KD.Fi24Sev.sl, e.1 = 66 ∧ e.2.2 = CFSG.KD.Fi24Sev.wrA := by decide +kernel

theorem sl_c : ∃ e ∈ CFSG.KD.Fi24Sev.sl, e.1 = 67 ∧ e.2.2 = CFSG.KD.Fi24Sev.wrB := by decide +kernel

theorem words_eq (hB : Bridge) : ∀ e ∈ CFSG.KD.Fi24Sev.sl,
    wordElt e.2.2 = CFSG.Sporadic.Fi23.slpG CFSG.Sporadic.Fi24.genG fi24SevenData.words e.1 :=
  CFSG.KD.Fi24Sev.Words.wordElt_eq_slpG hB (CFSG.KS.Fi24Sev.slOK_spec CFSG.KD.Fi24Sev.Ck.slc_t)
    sl_codes sl_words

theorem card_centralizer_y (hB : Bridge) :
    Nat.card (Subgroup.centralizer
      ({CFSG.Sporadic.Fi23.slpG CFSG.Sporadic.Fi24.genG fi24SevenData.words 66} : Set J)) = 17640 := by
  obtain ⟨e, he, h1, h2⟩ := sl_y
  rw [← h1, ← words_eq hB e he, h2]
  exact CFSG.KD.Fi24Sev.Cent.card_cent_A hB

theorem card_centralizer_c (hB : Bridge) :
    Nat.card (Subgroup.centralizer
      ({CFSG.Sporadic.Fi23.slpG CFSG.Sporadic.Fi24.genG fi24SevenData.words 67} : Set J)) = 2058 := by
  obtain ⟨e, he, h1, h2⟩ := sl_c
  rw [← h1, ← words_eq hB e he, h2]
  exact CFSG.KD.Fi24Sev.Cent.card_cent_B hB

end CFSG.KD.Fi24Sev.Seven

end
