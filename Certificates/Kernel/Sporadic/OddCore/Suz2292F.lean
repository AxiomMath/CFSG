
module

public import Certificates.Kernel.Sporadic.OddCore.Suz2292
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue3
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue2
import CFSG.Certificates.Kernel.Spor.RawCongr
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Sporadic.SmallOddCore.ClassSimple
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
public import CFSG.Certificates.Kernel.Spor.TPathSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.OddCore

open CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2.Native CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KS.Row CFSG.KS.TBfs CFSG.KS.PEnum CFSG.KS.Mathieu CFSG.Perm.Native
open CFSG.Sporadic.Th.Native

theorem rowArr_congr {w : Nat} {F : Nat → Nat} {o1 o2 : Nat}
    (h : ∀ j < 715, F (Nat.add o1 j) = F (Nat.add o2 j)) :
    rowArr 22880 w F o1 = rowArr 22880 w F o2 := by
  apply Array.ext (by simp [rowArr])
  intro i h1 _
  have hi : i < 22880 := by simpa [rowArr] using h1
  simp only [rowArr, Array.getElem_ofFn, rg]
  have e5 : Nat.shiftRight i 5 < 715 := by
    change i >>> 5 < 715
    rw [Nat.shiftRight_eq_div_pow]
    omega
  rw [h _ e5]

theorem gens_eq : certArr 2 = certArr 0 ∧ certArr 3 = certArr 1 := by
  obtain ⟨h1, h2⟩ := (by simpa only [bAnd_iff] using gens_rows :
    allN 715 (fun j => Nat.beq (SuzCertT.F (Nat.add 1430 j)) (SuzCertT.F j)) = true ∧
    allN 715 (fun j => Nat.beq (SuzCertT.F (Nat.add 2145 j)) (SuzCertT.F (Nat.add 715 j))) = true)
  refine ⟨?_, ?_⟩
  · rw [certArr_eq (by omega), certArr_eq (by omega)]
    refine rowArr_congr fun j hj => ?_
    have e : Nat.add (715 * 0) j = j := Nat.zero_add j
    rw [e]
    exact Nat.eq_of_beq_eq_true (allN_spec h1 j hj)
  · rw [certArr_eq (by omega), certArr_eq (by omega)]
    exact rowArr_congr fun j hj => Nat.eq_of_beq_eq_true (allN_spec h2 j hj)

theorem deriv_eq {j : Nat} (hj : j < 10) (h2 : 2 ≤ j)
    (hd : ∀ x < 22880, Nat.beq (cg (j + 2) x) (wpt (certDerivs[j]!) x) = true) :
    eqA 22880 certStrongArrs[j]! (wordA 22880 certStrongArrs certStrongInvs certDerivs[j]!) =
      true := by
  have hl : lettersOK 10 certDerivs[j]! = true := by
    interval_cases j <;> decide
  rw [CertificateChecks.KernelSpor.OddCore.eqA_iff]
  intro x hx
  rw [strong_rows hj, rowArr_get hx, word_get hl hx]
  exact Nat.eq_of_beq_eq_true (hd x hx)

theorem derivs_pt {x : Nat} (hx : x < 22880) :
    Nat.beq (cg 4 x) (wpt (certDerivs[2]!) x) = true ∧
    Nat.beq (cg 5 x) (wpt (certDerivs[3]!) x) = true ∧
    Nat.beq (cg 6 x) (wpt (certDerivs[4]!) x) = true ∧
    Nat.beq (cg 7 x) (wpt (certDerivs[5]!) x) = true ∧
    Nat.beq (cg 8 x) (wpt (certDerivs[6]!) x) = true ∧
    Nat.beq (cg 9 x) (wpt (certDerivs[7]!) x) = true ∧
    Nat.beq (cg 10 x) (wpt (certDerivs[8]!) x) = true ∧
    Nat.beq (cg 11 x) (wpt (certDerivs[9]!) x) = true := by
  have ha := allN_spec dwA2292 x hx
  have hb := allN_spec dwB2292 x hx
  simp only [bAnd_iff] at ha hb
  exact ⟨ha.1, ha.2.1, hb.1, ha.2.2, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2⟩

theorem derivs_ok : ∀ j < 10, 2 ≤ j → eqA 22880 certStrongArrs[j]!
    (wordA 22880 certStrongArrs certStrongInvs certDerivs[j]!) = true := by
  intro j hj h2
  interval_cases j
  · exact deriv_eq (by omega) h2 fun x hx => (derivs_pt hx).1
  · exact deriv_eq (by omega) h2 fun x hx => (derivs_pt hx).2.1
  · exact deriv_eq (by omega) h2 fun x hx => (derivs_pt hx).2.2.1
  · exact deriv_eq (by omega) h2 fun x hx => (derivs_pt hx).2.2.2.1
  · exact deriv_eq (by omega) h2 fun x hx => (derivs_pt hx).2.2.2.2.1
  · exact deriv_eq (by omega) h2 fun x hx => (derivs_pt hx).2.2.2.2.2.1
  · exact deriv_eq (by omega) h2 fun x hx => (derivs_pt hx).2.2.2.2.2.2.1
  · exact deriv_eq (by omega) h2 fun x hx => (derivs_pt hx).2.2.2.2.2.2.2

theorem fix_get {j k : Nat} (hj : j < 10) (hk : k < 6) :
    ((certStrongArrs[j]!)[k]! == k) = (nget fixBits (6 * j + k) == 1) := by
  have hb := allN_spec fix_ok (6 * j + k) (by omega)
  have e1 : Nat.div (6 * j + k) 6 = j := by
    change (6 * j + k) / 6 = j
    omega
  have e2 : Nat.mod (6 * j + k) 6 = k := by
    change (6 * j + k) % 6 = k
    omega
  rw [e1, e2] at hb
  rw [strong_rows hj, rowArr_get (by omega)]
  have e3 : rg 15 (mask 15) SuzCertT.F (ocs j) k = cg (Nat.add j 2) k := rfl
  rw [e3]
  cases h : Nat.beq (cg (Nat.add j 2) k) k
  · rw [h] at hb
    have hne : cg (Nat.add j 2) k ≠ k := fun e => by simp [e] at h
    have hf : nget fixBits (6 * j + k) = 0 := (Nat.eq_of_beq_eq_true hb).symm
    simp [hne, hf]
  · rw [h] at hb
    have he : cg (Nat.add j 2) k = k := Nat.eq_of_beq_eq_true h
    have hf : nget fixBits (6 * j + k) = 1 := (Nat.eq_of_beq_eq_true hb).symm
    simp [he, hf]

theorem fixes_eq {j i : Nat} (hj : j < 10) (hi : i ≤ 6) :
    fixesFirst certBaseNat.toArray certStrongArrs[j]! i =
      allLt i (fun k => nget fixBits (6 * j + k) == 1) := by
  unfold fixesFirst
  apply CFSG.KS.Raw.allLt_congr
  intro k hk
  have hk6 : k < 6 := by omega
  have hb : certBaseNat.toArray[k]! = k := by
    interval_cases k <;> rfl
  rw [hb, fix_get hj (by omega)]

theorem levels_eq : ∀ i ≤ 6, levelIdx certStrongArrs certBaseNat.toArray i = certLevelIdx i := by
  intro i hi
  unfold levelIdx
  have hs : certStrongArrs.size = 10 := rfl
  rw [hs]
  rw [List.filter_congr (q := fun j => allLt i (fun k => nget fixBits (6 * j + k) == 1))
    (fun j hj => fixes_eq (List.mem_range.1 hj) hi)]
  interval_cases i <;> decide

theorem tbfsSl_spec {n cnt r lo len : Nat} {L : Nat → Nat → Nat} {LV : Nat → Nat}
    {PTS POS PAR LAB TI : Nat → Nat} (h : tbfsSlK n cnt r L LV PTS POS PAR LAB TI lo len = true) :
    ∀ k, lo ≤ k → k < lo + len → k < cnt → tbfsPtK n cnt r L LV PTS POS PAR LAB TI k = true := by
  intro k h1 h2 h3
  have h' := allN_spec h (k - lo) (by omega)
  rw [strictB_app'] at h'
  have e : Nat.add lo (k - lo) = k := by
    change lo + (k - lo) = k
    omega
  rw [e, Eq.mpr Nat.blt_eq h3] at h'
  exact h'

theorem lt_get {l x : Nat} (hl : l < 20) (hx : x < 22880) : ap certLetters[l]! x = certLt l x := by
  have hl2 : l / 2 < 10 := by omega
  have hsz : l < certLetters.size := by simp [certLetters]; omega
  rw [ap, getElem!_pos certLetters l hsz]
  simp only [certLetters, Array.getElem_ofFn]
  have e1 : Nat.shiftRight l 1 = l / 2 := Nat.shiftRight_eq_div_pow l 1
  have e2 : Nat.land l 1 = l % 2 := Nat.and_two_pow_sub_one_eq_mod l 1
  unfold certLt
  rw [e1, e2]
  by_cases he : l % 2 = 0
  · simp only [he, ↓reduceIte]
    have hs : x < (certStrongArrs[l / 2]!).size := by rw [strong_rows hl2]; simp [rowArr]; omega
    rw [CFSG.Sporadic.SmallOddCore.getElem!_map_eq _ _ hs, UInt32.toNat_ofNat', strong_rows hl2,
      rowArr_get hx, Nat.mod_eq_of_lt (by have := rangeF hl2 x hx; omega)]
    rfl
  · have ho : l % 2 = 1 := by omega
    simp only [ho, Nat.one_ne_zero, ↓reduceIte]
    have hs : x < (certStrongInvs[l / 2]!).size := by
      rw [strongInv_rows hl2]; simp [rowArr]; omega
    rw [CFSG.Sporadic.SmallOddCore.getElem!_map_eq _ _ hs, UInt32.toNat_ofNat', strongInv_rows hl2,
      rowArr_get hx, Nat.mod_eq_of_lt (by have := rangeG hl2 x hx; omega)]
    rfl

theorem lv_lt : ∀ i < 6, ∀ t < (certLevelLetters i).size, (certLevelLetters i)[t]! < 20 := by
  decide

theorem lv_ok {i : Nat} (hi : i < 6) {LV : List Nat} (hL : LV = (certLevelLetters i).toList) :
    (certLevelLetters i).size = LV.length ∧ ∀ t < LV.length, (certLevelLetters i)[t]! = nget LV t ∧
      nget LV t < certLetters.size ∧
      ∀ x < 22880, ap certLetters[nget LV t]! x = certLt (nget LV t) x := by
  have hlen : (certLevelLetters i).size = LV.length := by rw [hL, Array.length_toList]
  refine ⟨hlen, fun t ht => ?_⟩
  have hv : (certLevelLetters i)[t]! = nget LV t := by
    rw [nget_get LV ht, getElem!_pos _ t (by rw [hlen]; exact ht)]
    simp only [hL, Array.getElem_toList]
  have hlt : nget LV t < 20 := by
    rw [← hv]
    exact lv_lt i hi t (by rw [hlen]; exact ht)
  refine ⟨hv, by simp [certLetters]; exact hlt, fun x hx => lt_get hlt hx⟩

theorem orbPath_of {i r cnt : Nat} (hi : i < 6) {LV : List Nat}
    (hL : LV = (certLevelLetters i).toList) (hr : LV.length = r) {PTS POS PAR LAB TI : Nat → Nat}
    (hc : cnt = certOrbitSizes.getD i 0)
    (hh : tpathHdK (certBaseNat.getD i 0) cnt PTS = true)
    (hp : ∀ k < cnt, tpathPtK 22880 r certLt (nget LV) PTS POS PAR LAB TI k = true) :
    ∃ T : Tree, orbPathOK 22880 (certBaseNat.getD i 0) T certLetters (certLevelLetters i) = true ∧
      T.pts.size = certOrbitSizes.getD i 0 := by
  obtain ⟨h1, h2⟩ := lv_ok hi hL
  subst hr
  exact ⟨_, tpathK_sound ⟨h1, h2⟩ hh hp, by rw [← hc]; simp [tbfsRec]⟩

theorem orbPaths : ∀ i < 6, ∃ T : Tree, orbPathOK 22880 (certBaseNat.getD i 0) T certLetters
      (certLevelLetters i) = true ∧ T.pts.size = certOrbitSizes.getD i 0 := by
  intro i hi
  interval_cases i
  · exact orbPath_of (i := 0) (r := 20) (cnt := CT0.cnt) (LV := lvK0) (by omega) (by decide) rfl rfl t0_hd fun k hk => by
      have hc : CT0.cnt = 22880 := rfl
      rcases Nat.lt_or_ge k 11440 with a | a
      · exact tpathSl_spec t0_pa k (Nat.zero_le _) (by omega) hk
      · exact tpathSl_spec t0_pb k a (by omega) hk
  · exact orbPath_of (i := 1) (r := 16) (cnt := CT1.cnt) (LV := lvK1) (by omega) (by decide) rfl rfl t1_hd fun k hk => by
      have hc : CT1.cnt = 8505 := rfl
      exact tpathSl_spec t1_p k (Nat.zero_le _) (by omega) hk
  · exact orbPath_of (i := 2) (r := 12) (cnt := CT2.cnt) (LV := lvK2) (by omega) (by decide) rfl rfl t2_hd fun k hk => by
      have hc : CT2.cnt = 1152 := rfl
      exact tpathSl_spec t2_p k (Nat.zero_le _) (by omega) hk
  · exact orbPath_of (i := 3) (r := 2) (cnt := CT3.cnt) (LV := lvK3) (by omega) (by decide) rfl rfl t3_hd fun k hk => by
      have hc : CT3.cnt = 2 := rfl
      exact tpathSl_spec t3_p k (Nat.zero_le _) (by omega) hk
  · exact orbPath_of (i := 4) (r := 0) (cnt := CT4.cnt) (LV := []) (by omega) (by decide) rfl rfl t4_hd fun k hk => by
      have hc : CT4.cnt = 1 := rfl
      exact tpathSl_spec t4_p k (Nat.zero_le _) (by omega) hk
  · exact orbPath_of (i := 5) (r := 0) (cnt := CT5.cnt) (LV := []) (by omega) (by decide) rfl rfl t5_hd fun k hk => by
      have hc : CT5.cnt = 1 := rfl
      exact tpathSl_spec t5_p k (Nat.zero_le _) (by omega) hk

theorem facts2292 : certArr 2 = certArr 0 ∧ certArr 3 = certArr 1 ∧
    (∀ j < 10, 2 ≤ j → eqA 22880 certStrongArrs[j]!
      (wordA 22880 certStrongArrs certStrongInvs certDerivs[j]!) = true) ∧
    (∀ i ≤ 6, levelIdx certStrongArrs certBaseNat.toArray i = certLevelIdx i) ∧
    (∀ i < 6, ∃ T : Tree, orbPathOK 22880 (certBaseNat.getD i 0) T certLetters
      (certLevelLetters i) = true ∧ T.pts.size = certOrbitSizes.getD i 0) ∧
    (∀ j < 10, ∀ x < 22880, (certStrongArrs[j]!)[x]! < 2 ^ 32 ∧ (certStrongInvs[j]!)[x]! < 2 ^ 32) ∧
    (∀ j < 10, certStrongInvs[j]!.size = 22880) := by
  refine ⟨gens_eq.1, gens_eq.2, derivs_ok, levels_eq, orbPaths,
    fun j hj x hx => ⟨?_, ?_⟩, fun j hj => ?_⟩
  · rw [strong_rows hj, rowArr_get hx]
    exact Nat.lt_trans (rangeF hj x hx) (by decide)
  · rw [strongInv_rows hj, rowArr_get hx]
    exact Nat.lt_trans (rangeG hj x hx) (by decide)
  · rw [strongInv_rows hj]
    simp [rowArr]

end CertificateChecks.KernelSpor.OddCore

end
