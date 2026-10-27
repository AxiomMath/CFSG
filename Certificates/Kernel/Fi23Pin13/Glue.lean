module

public import Certificates.Kernel.Fi23Pin13.Checks
public import Certificates.Kernel.Fi23Five.Glue
public import Certificates.Kernel.Fi23M.Keys
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.Fi23PinThirteenInputs
public import Certificates.Kernel.Misc.Perm.CharsCat
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib

public section

set_option maxRecDepth 400000

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23R CFSG.KD.Fi23K CFSG.Sporadic.Th.Native CFSG.Sporadic.Fi23.Native CertificateChecks.KernelFi23R
  CertificateChecks.KernelFi23M CertificateChecks.KernelFi23Five
  CFSG.HardMathSupport.Dickson.Sec6.I1431.Fi23PinNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native CFSG.KD.Fi23Pin13

#ks_chars_cat CertificateChecks.KernelFi23Pin13.YC
  CFSG.HardMathSupport.Dickson.Sec6.I1431.Fi23PinNative.y13Str
#ks_chars_cat CertificateChecks.KernelFi23Pin13.GC
  CFSG.HardMathSupport.Dickson.Sec6.I1431.Fi23PinNative.g13Str

namespace CertificateChecks.KernelFi23Pin13

@[expose] def cL (c : Char) : Nat := if c = 'a' ∨ c = 'A' then 39 else if c = 'b' then 40 else 41

theorem pinY : ((YC.chars.map cL).reverse == wY) = true := by quickRfl

theorem pinG : ((GC.chars.map cL).reverse == wG) = true := by quickRfl

theorem letters_ok (s : String) : ∀ z ∈ strLetters s, z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2 := by
  intro z hz
  unfold strLetters at hz
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hz
  split_ifs <;> simp

theorem regZ_letters (s : String) :
    (strLetters s).reverse.map regZ = (s.toList.map cL).reverse := by
  unfold strLetters
  rw [List.map_reverse, List.map_map]
  congr 1
  apply List.map_congr_left
  intro c _
  simp only [Function.comp_apply, cL]
  by_cases h1 : c = 'a' <;> by_cases h2 : c = 'A' <;> by_cases h3 : c = 'b' <;>
    simp [h1, h2, h3, regZ]


theorem tabEq {A B : Table} {u v : List ℕ} (hA : RW A u) (hB : RW B v) (e : wp u = wp v) :
    eqTab A B = true := by
  rw [beq_iff_eq.1 (RW.beq hA hB e)]
  exact eqTab_self B

theorem ne_of_chk {x : ℕ} (h : Bool.not (Nat.beq x 2) = true) : x ≠ 2 := by
  rw [Bool.not_eq_eq_eq_not, Bool.not_true] at h
  exact Nat.ne_of_beq_eq_false h

theorem nil_ok : ∀ c ∈ ([] : List ℕ), okL c := fun _ h => absurd h List.not_mem_nil

theorem rw_Y : RW (wordT 31671 (genTables orbLit) y13Letters) wY :=
  (rw_wordT y13Letters (letters_ok _)).word (by
    unfold y13Letters
    rw [regZ_letters, YC.eq, String.toList_ofList]
    exact beq_iff_eq.1 pinY)

theorem rw_G : RW (wordT 31671 (genTables orbLit) g13Letters) wG :=
  (rw_wordT g13Letters (letters_ok _)).word (by
    unfold g13Letters
    rw [regZ_letters, GC.eq, String.toList_ofList]
    exact beq_iff_eq.1 pinG)

theorem rw_D : RW (dTable orbLit) [43] := by
  rw [dTable_eq]
  exact rw_dTab

theorem pin13_ok : fi23Pin13OK orbLit = true := by
  have hY := rw_Y
  have hG := rw_G
  have hD := rw_D
  have t1 : eqTab (powT 31671 13 (wordT 31671 (genTables orbLit) y13Letters)) (idT 31671) = true :=
    tabEq (rw_powT hY 13) rw_idT (wp_eq_of_eqB ch17403_y13 (ok_powW hY.2.1 13) nil_ok)
  have t2 : eqTab (wordT 31671 (genTables orbLit) y13Letters) (idT 31671) = false :=
    eqTab_false (i := 2) (by norm_num) (by
      rw [hY.ap (by norm_num), rw_idT.ap (by norm_num)]
      exact ne_of_chk ch17403_mvY)
  have t3 : eqTab (compT 31671 (wordT 31671 (genTables orbLit) y13Letters)
      (wordT 31671 (genTables orbLit) g13Letters))
      (compT 31671 (wordT 31671 (genTables orbLit) g13Letters)
        (powT 31671 4 (wordT 31671 (genTables orbLit) y13Letters))) = true :=
    tabEq (rw_compT hY hG) (rw_compT hG (rw_powT hY 4))
      (wp_eq_of_eqB ch17403_rel (ok_append hG.2.1 hY.2.1) (ok_append (ok_powW hY.2.1 4) hG.2.1))
  have t4 : eqTab (compT 31671 (dTable orbLit) (wordT 31671 (genTables orbLit) y13Letters))
      (compT 31671 (wordT 31671 (genTables orbLit) y13Letters) (dTable orbLit)) = true :=
    tabEq (rw_compT hD hY) (rw_compT hY hD)
      (wp_eq_of_eqB ch17403_dy (ok_append hY.2.1 hD.2.1) (ok_append hD.2.1 hY.2.1))
  have t5 : eqTab (powT 31671 2 (dTable orbLit)) (idT 31671) = true :=
    tabEq (rw_powT hD 2) rw_idT (wp_eq_of_eqB ch17403_d2 (ok_powW hD.2.1 2) nil_ok)
  have t6 : eqTab (dTable orbLit) (idT 31671) = false :=
    eqTab_false (i := 2) (by norm_num) (by
      rw [hD.ap (by norm_num), rw_idT.ap (by norm_num)]
      exact ne_of_chk ch17403_mvD)
  unfold fi23Pin13OK
  simp only [t1, t2, t3, t4, t5, t6, Bool.not_false, Bool.and_self]

end CertificateChecks.KernelFi23Pin13

end
