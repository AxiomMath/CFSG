module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Fi23KInputs
import Certificates.Kernel.Fi23Kt.Checks
import all Certificates.Kernel.Fi23Pf.Glue
import Certificates.Kernel.Fi23M.Facts
import Certificates.Kernel.Fi23M.WGlue
import Certificates.Kernel.VecCert.WordProg
import CFSG.Certificates.Kernel.Spor.Mat3Sound
import CFSG.Certificates.Kernel.DecTextSound
import CFSG.Certificates.Kernel.Common.StrSplit
import CFSG.Certificates.Kernel.Common.StrChars
import CFSG.Certificates.Kernel.Common.Harness
import all Init.Data.List.SplitOn.Basic

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23Kt

open CFSG.F3.Native CFSG.Sporadic.Fi23 CFSG.Sporadic.Fi23.Native CertificateChecks.KernelFi23M
  CertificateChecks.KernelWP CFSG.KS.Mat3 CFSG.KD.Fi23Kt
open CertificateChecks.KernelFi23Pf (Facts Facts.mul facts_D facts_conj facts_prod facts_id eqW_of
  neW_of commW_of cw dW7 gm parseWord_ofList)

#ks_chars_of CertificateChecks.KernelFi23Kt.Txt CFSG.EvenSporadicStandard.HypOne.Fi23.kTxt

noncomputable def LS : List (List Char) := Txt.chars.splitOn '\n'

noncomputable def GS : List (List Nat) := ((LS.drop 1).take 9).map CFSG.KC.DecText.natsK

noncomputable def PR : List Nat := CFSG.KC.DecText.natsK (LS.getD 10 [])

noncomputable def VS : List Nat := CFSG.KC.DecText.natsK (LS.getD 11 [])

noncomputable def DS : List Nat := CFSG.KC.DecText.natsK (LS.getD 12 [])

noncomputable def ES : List Nat := CFSG.KC.DecText.natsK (LS.getD 13 [])

theorem lines_eq : CFSG.EvenSporadicStandard.HypOne.Fi23.kLines = LS.map String.ofList := by
  have e : ("\n" : String) = String.singleton '\n' := rfl
  rw [CFSG.EvenSporadicStandard.HypOne.Fi23.kLines, Txt.eq, e, LS]
  exact CFSG.KC.Str.splitOn_ofList Txt.chars '\n'

theorem len_LS : 14 ≤ LS.length := by decide +kernel

theorem getElem!_LS (i : Nat) (hi : i < LS.length) :
    (LS.map String.ofList)[i]! = String.ofList (LS.getD i []) := by
  rw [getElem!_pos _ i (by simpa using hi), List.getElem_map, List.getD_eq_getElem _ _ hi]

theorem N_eq : CFSG.EvenSporadicStandard.HypOne.Fi23.kN = 9 := by
  rw [CFSG.EvenSporadicStandard.HypOne.Fi23.kN, lines_eq, getElem!_LS 0 (by have := len_LS; omega),
    CFSG.KC.Str.toNat!_ofList (by decide +kernel)
      (List.all_eq_true.1 (by quickRfl : (LS.getD 0 []).all Char.isDigit = true))]
  decide +kernel

theorem gens_eq : CFSG.EvenSporadicStandard.HypOne.Fi23.kGens = GS := by
  rw [CFSG.EvenSporadicStandard.HypOne.Fi23.kGens, lines_eq, N_eq, ← List.map_drop,
    ← List.map_take, List.map_map]
  have hd : ((LS.drop 1).take 9).all CFSG.KC.DecText.digitsOK = true := by quickRfl
  rw [GS]
  exact List.map_congr_left fun l hl => parseWord_ofList (List.all_eq_true.1 hd l hl)

theorem line_eq (i : Nat) (hi : i < 14) (hd : CFSG.KC.DecText.digitsOK (LS.getD i []) = true) :
    CFSG.EvenSporadicStandard.Solomon78.parseWord (LS.map String.ofList)[i]! =
      CFSG.KC.DecText.natsK (LS.getD i []) := by
  rw [getElem!_LS i (by have := len_LS; omega)]
  exact parseWord_ofList hd

theorem par_eq : CFSG.EvenSporadicStandard.HypOne.Fi23.kPar = PR := by
  rw [CFSG.EvenSporadicStandard.HypOne.Fi23.kPar, N_eq, lines_eq]
  exact line_eq 10 (by norm_num) (by quickRfl)

theorem even_eq : CFSG.EvenSporadicStandard.HypOne.Fi23.kEven = VS := by
  rw [CFSG.EvenSporadicStandard.HypOne.Fi23.kEven, N_eq, lines_eq]
  exact line_eq 11 (by norm_num) (by quickRfl)

theorem wd_eq : CFSG.EvenSporadicStandard.HypOne.Fi23.kWordD = DS := by
  rw [CFSG.EvenSporadicStandard.HypOne.Fi23.kWordD, N_eq, lines_eq]
  exact line_eq 12 (by norm_num) (by quickRfl)

theorem we_eq : CFSG.EvenSporadicStandard.HypOne.Fi23.kWordE = ES := by
  rw [CFSG.EvenSporadicStandard.HypOne.Fi23.kWordE, N_eq, lines_eq]
  exact line_eq 13 (by norm_num) (by quickRfl)

theorem lists' : CFSG.KC.WP.statesOK 2 WC PS 15 = true ∧ CFSG.KC.WP.relProgsOK 2 15 PE 41 = true ∧
    CFSG.KC.WP.relProgsOK 2 15 PF 41 = true := by
  have h := lists
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem good : ∀ k < 15, Good (CFSG.KS.Mat3.Canon3 64009) (mat3 253 64009) CFSG.KD.Fi23M.RB 2 (RS k) (WC k) :=
  states_good hs hroot hinv lists'.1 fun k hk => S.all k hk

theorem top_good {P : List Nat} (hl : CFSG.KC.WP.letsOK 2 P = true)
    (hr : CFSG.KC.WP.refsOK 15 P = true) :
    Good (CFSG.KS.Mat3.Canon3 64009) (mat3 253 64009) CFSG.KD.Fi23M.RB 2
      (CFSG.KC.Ord.progTop CFSG.KD.Fi23M.RB 2 RS CFSG.KD.Fi23M.MUL CFSG.KD.Fi23M.ONE P)
      (CFSG.KC.WP.progWord WC P) :=
  top_sound hs hroot hinv hl fun ins hi h1 => good _ (refs_of 15 P hr ins hi h1)

theorem eq_words (j : Nat) (hj : j < 41) :
    wordMat (mat3 253 64009) CFSG.KD.Fi23M.RB 2 (CFSG.KC.WP.progWord WC (PE j)) =
      wordMat (mat3 253 64009) CFSG.KD.Fi23M.RB 2 (CFSG.KC.WP.progWord WC (PF j)) := by
  obtain ⟨hlE, hrE⟩ := relProgsOK_spec 41 lists'.2.1 j hj
  obtain ⟨hlF, hrF⟩ := relProgsOK_spec 41 lists'.2.2 j hj
  have e : CFSG.KC.Ord.progTop CFSG.KD.Fi23M.RB 2 RS CFSG.KD.Fi23M.MUL CFSG.KD.Fi23M.ONE (PE j) =
      CFSG.KC.Ord.progTop CFSG.KD.Fi23M.RB 2 RS CFSG.KD.Fi23M.MUL CFSG.KD.Fi23M.ONE (PF j) :=
    Nat.eq_of_beq_eq_true (E.all j hj)
  rw [← (top_good hlE hrE).2, ← (top_good hlF hrF).2, e]

noncomputable def eqOK (j : Nat) (U V : List Nat) : Bool :=
  (CFSG.KC.WP.progWord WC (PE j) == U.map cd) && (CFSG.KC.WP.progWord WC (PF j) == V.map cd) &&
    U.all (fun x => decide (x < 2)) && V.all (fun x => decide (x < 2))

theorem gm_eq_of {j : Nat} (hj : j < 41) {U V : List Nat} (h : eqOK j U V = true) : gm U = gm V := by
  unfold eqOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hU, hV⟩, hu⟩, hv⟩ := h
  have e := eq_words j hj
  rw [hU, hV, wordMat_cd U hu, wordMat_cd V hv] at e
  exact e

noncomputable def stOK (k : Nat) (U : List Nat) : Bool :=
  (WC k == U.map cd) && U.all (fun x => decide (x < 2))

theorem gm_ne_of {k l : Nat} (hk : k < 15) (hl : l < 15) {U V : List Nat} (hU : stOK k U = true)
    (hV : stOK l V = true)
    (hn : Bool.rec (motive := fun _ => Bool) true false (Nat.beq (RS k) (RS l)) = true) :
    gm U ≠ gm V := by
  unfold stOK at hU hV
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hU hV
  intro e
  have gk := good k hk
  have gl := good l hl
  have ek : mat3 253 64009 (RS k) = gm U := by rw [gk.2, hU.1, wordMat_cd U hU.2]
  have el : mat3 253 64009 (RS l) = gm V := by rw [gl.2, hV.1, wordMat_cd V hV.2]
  have hkl := mat3_inj (d := 253) (by norm_num) gk.1 gl.1 (by rw [ek, el]; exact e)
  rw [hkl, Nat.beq_refl] at hn
  exact absurd hn (by decide)

noncomputable def uT (i : Nat) : List Nat := cw (GS.getD i [])

def uD1 : List Nat := cw CFSG.EvenSporadicStandard.Solomon78.fi23G1

def uC : List Nat := cw CFSG.EvenSporadicStandard.Solomon78.fi23G2

noncomputable def tOK (i : Nat) : Bool :=
  eqOK (3 + 3 * i) (uT i ++ dW7) (dW7 ++ uT i) && eqOK (4 + 3 * i) (uT i ++ uD1) (uD1 ++ uT i) &&
    eqOK (5 + 3 * i) (uT i ++ uC) (uC ++ uT i)

noncomputable def uP (j : Nat) : List Nat := uT (PR.getD j 0) ++ uT j

noncomputable def bOK (j : Nat) : Bool :=
  decide (PR.getD j 0 < 9) && eqOK (29 + j) (uP j ++ (uP j ++ uP j)) []

theorem gs_lt : GS.all (fun w => w.all fun x => decide (x < 2)) = true := by quickRfl

theorem gs_len : GS.length = 9 := by decide +kernel

theorem gs_word {g : List Nat} (hg : g ∈ GS) : ∀ x ∈ g, x < 2 := by
  have h := List.all_eq_true.1 gs_lt g hg
  simpa using h

theorem facts_T : ∀ x < (GS.map CFSG.EvenSporadicStandard.Solomon78.conjW).toArray.size,
    Facts (GS.map CFSG.EvenSporadicStandard.Solomon78.conjW).toArray[x]! (uT x) := by
  intro x hx
  simp only [List.size_toArray, List.length_map] at hx
  rw [List.getElem!_toArray, getElem!_pos _ x (by simpa using hx), List.getElem_map, uT,
    List.getD_eq_getElem _ _ hx]
  exact facts_conj _ (gs_word (List.getElem_mem hx))

theorem g1_lt : ∀ x ∈ CFSG.EvenSporadicStandard.Solomon78.fi23G1, x < 2 := by decide

theorem g2_lt : ∀ x ∈ CFSG.EvenSporadicStandard.Solomon78.fi23G2, x < 2 := by decide

theorem facts_word {w : List Nat} (h : w.all (fun x => decide (x < 9)) = true) :
    Facts (prodW 253 (GS.map CFSG.EvenSporadicStandard.Solomon78.conjW).toArray w)
      (w.map uT).flatten := by
  refine facts_prod _ uT facts_T w fun x hx => ?_
  have hx' := List.all_eq_true.1 h x hx
  simpa [gs_len] using hx'

theorem kCheckOf_true : CFSG.EvenSporadicStandard.HypOne.Fi23.kCheckOf
    CFSG.EvenSporadicStandard.Solomon78.fi23G1 CFSG.EvenSporadicStandard.Solomon78.fi23G2 GS PR VS
      DS ES = true := by
  have fD := facts_D
  have fD1 := facts_conj _ g1_lt
  have fC := facts_conj _ g2_lt
  have fTi : ∀ i < 9, Facts (GS.map CFSG.EvenSporadicStandard.Solomon78.conjW).toArray[i]! (uT i) :=
    fun i hi => facts_T i (by simpa [gs_len] using hi)
  unfold CFSG.EvenSporadicStandard.HypOne.Fi23.kCheckOf
  simp only [Bool.and_eq_true, Bool.not_eq_true', gs_len]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩,
    ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · quickRfl
  · quickRfl
  · quickRfl
  · quickRfl
  · quickRfl
  · exact commW_of fD fD1 (gm_eq_of (j := 0) (by norm_num) (by quickRfl))
  · exact commW_of fD fC (gm_eq_of (j := 1) (by norm_num) (by quickRfl))
  · exact commW_of fD1 fC (gm_eq_of (j := 2) (by norm_num) (by quickRfl))
  · exact canonW_matD
  · exact canonW_of_canonM fD1.canon
  · exact canonW_of_canonM fC.canon
  · exact neW_of fD fD1 (gm_ne_of (k := 0) (l := 1) (by norm_num) (by norm_num) (by quickRfl)
      (by quickRfl) n01)
  · exact neW_of fD fC (gm_ne_of (k := 0) (l := 2) (by norm_num) (by norm_num) (by quickRfl)
      (by quickRfl) n02)
  · exact neW_of fD1 fC (gm_ne_of (k := 1) (l := 2) (by norm_num) (by norm_num) (by quickRfl)
      (by quickRfl) n12)
  · rw [List.all_eq_true]
    intro i hi
    have hi' : i < 9 := List.mem_range.1 hi
    have hall : (List.range 9).all tOK = true := by quickRfl
    have ht := List.all_eq_true.1 hall i hi
    unfold tOK at ht
    simp only [Bool.and_eq_true] at ht ⊢
    obtain ⟨⟨h0, h1⟩, h2⟩ := ht
    exact ⟨⟨commW_of (fTi i hi') fD (gm_eq_of (by omega) h0),
      commW_of (fTi i hi') fD1 (gm_eq_of (by omega) h1)⟩,
      commW_of (fTi i hi') fC (gm_eq_of (by omega) h2)⟩
  · rw [List.all_eq_true]
    intro j hj
    have hj' : j < 9 := List.mem_range.1 hj
    have hall : (List.range 9).all (fun j => j == 0 || bOK j) = true := by quickRfl
    have hb := List.all_eq_true.1 hall j hj
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0
      rfl
    · have hb' : bOK j = true := by
        have hne : (j == 0) = false := by simp; omega
        rw [hne, Bool.false_or] at hb
        exact hb
      unfold bOK at hb'
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hb'
      obtain ⟨hp, he⟩ := hb'
      have fP := (fTi _ hp).mul (fTi j hj')
      have h := eqW_of (fP.mul (fP.mul fP)) facts_id (gm_eq_of (by omega) he)
      unfold CFSG.EvenSporadicStandard.HypOne.Fi23.braidW
      rw [h]
      simp
  · exact eqW_of (facts_word (w := [0]) (by decide)) (facts_word (by quickRfl))
      (gm_eq_of (j := 38) (by norm_num) (by quickRfl))
  · exact eqW_of fD (facts_word (by quickRfl)) (gm_eq_of (j := 39) (by norm_num) (by quickRfl))
  · exact eqW_of fD1 (facts_word (by quickRfl)) (gm_eq_of (j := 40) (by norm_num) (by quickRfl))

public theorem fi23KCheck_true : CFSG.EvenSporadicStandard.HypOne.Fi23.fi23KCheck = true := by
  rw [CFSG.EvenSporadicStandard.HypOne.Fi23.fi23KCheck, gens_eq, par_eq, even_eq, wd_eq, we_eq]
  exact kCheckOf_true

end CertificateChecks.KernelFi23Kt
