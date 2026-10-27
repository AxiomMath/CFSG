module

public import Certificates.Kernel.Sporadic.Fi24Seven.Glue

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelF24S

open CFSG.KC.SlpM CFSG.KD.F24S CFSG.Sporadic.Fi24.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24SevenNative CFSG.HardMathSupport.Dickson.I271.Fi7

noncomputable abbrev Ws7 : Array (List Int) := (W7.map decW).toArray ++ (E7.map decW).toArray

noncomputable abbrev S7 : Array Mat781 := semArr gW Ws7

theorem ws7_eq : Ws7 = ((WL 1).map decW).toArray := layer_words E7

theorem slp_ws7 : CFSG.Sporadic.Fi23.Native.slpOK Ws7 = true := by
  rw [ws7_eq]
  exact slpOK_of_slpC slp7

theorem ws7_size : Ws7.size = 1206 := by
  simp [Ws7, w7_len, e7_len]

theorem good7 {k : Nat} (hk : k < 2412) : Good (mLetters Ws7)[k]! (S7.getD k 1) := by
  obtain ⟨⟨-, hI⟩, hs⟩ := mLetters_good slp_ws7
  exact hI k (by rw [hs, ws7_size]; omega)

theorem semE7 (u : List Nat) : semE gW (WL 1) u = semWord gW S7 (decW u) := by
  unfold semE
  rw [← ws7_eq]

theorem eq7 {K nRr : Nat} (hk : ∀ k < K, CK k = true)
    (hp : planOK K nRr nBase lyK pcR pnR inK ouK = true) {e : List Nat × List Nat}
    (h : hasEq lyK eqK K 1 e = true) : semWord gW S7 (decW e.1) = semWord gW S7 (decW e.2) := by
  rw [← semE7, ← semE7]
  exact eq_of_has hk hp h

theorem has7 {e : List Nat × List Nat} (he : e ∈ eqs7) : hasEq lyK eqK nK1 1 e = true :=
  allL_spec eqs7_ok e he

theorem letter7 {j : Nat} (hj : 2 < j) : semLetter gW S7 (j : Int) = S7.getD (2 * (j - 3)) 1 := by
  unfold semLetter
  rw [if_neg (by simp; omega), if_pos (by omega)]
  simp

theorem word1 {c j : Nat} (hc : c = 2 * j) (hj : 2 < j) :
    semWord gW S7 (decW [c]) = S7.getD (2 * (j - 3)) 1 := by
  rw [show decW [c] = [decC c] from rfl, decC_even hc, semWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, letter7 hj]

theorem word2 {c d i j : Nat} (hc : c = 2 * i) (hd : d = 2 * j) (hi : 2 < i) (hj : 2 < j) :
    semWord gW S7 (decW [c, d]) = S7.getD (2 * (i - 3)) 1 * S7.getD (2 * (j - 3)) 1 := by
  rw [show decW [c, d] = [decC c, decC d] from rfl, decC_even hc, decC_even hd, semWord,
    List.map_cons, List.map_cons, List.map_nil, List.prod_cons, List.prod_cons, List.prod_nil,
    mul_one, letter7 hi, letter7 hj]

theorem wordPow (n : Nat) : semWord gW S7 (decW (List.replicate n 2416)) = S7.getD 2410 1 ^ n := by
  induction n with
  | zero => rw [pow_zero]; rfl
  | succ n ih =>
    rw [List.replicate_succ, show decW (2416 :: List.replicate n 2416) = decC 2416 :: decW
      (List.replicate n 2416) from rfl, decC_even (j := 1208) rfl, semWord, List.map_cons,
      List.prod_cons]
    rw [semWord] at ih
    rw [ih, letter7 (j := 1208) (by norm_num), pow_succ']

theorem fi7OK_of (hk : ∀ k < nK1, CK k = true) : fi7OK () = true := by
  have hp := plan1_ok
  have E : ∀ u v, (u, v) ∈ eqs7 → semWord gW S7 (decW u) = semWord gW S7 (decW v) :=
    fun u v he => eq7 (e := (u, v)) hk hp (has7 he)
  have hne : semWord gW S7 (decW [2416, 2416]) ≠ semWord gW S7 (decW []) := by
    have := ne_of_has (e := ([2416, 2416], [])) hk hp nes7_ok
    rwa [semE7, semE7] at this
  have e1 : S7.getD 2406 1 = S7.getD 0 1 := by
    have := E [2412] [6] (by simp [eqs7])
    rwa [word1 (j := 1206) rfl (by norm_num), word1 (j := 3) rfl (by norm_num)] at this
  have e2 : S7.getD 2408 1 = S7.getD 2 1 := by
    have := E [2414] [8] (by simp [eqs7])
    rwa [word1 (j := 1207) rfl (by norm_num), word1 (j := 4) rfl (by norm_num)] at this
  have c1 : S7.getD 2170 1 * S7.getD 134 1 = S7.getD 134 1 * S7.getD 2170 1 := by
    have := E [2176, 140] [140, 2176] (by simp [eqs7])
    rwa [word2 (i := 1088) (j := 70) rfl rfl (by norm_num) (by norm_num),
      word2 (i := 70) (j := 1088) rfl rfl (by norm_num) (by norm_num)] at this
  have c2 : S7.getD 2172 1 * S7.getD 134 1 = S7.getD 134 1 * S7.getD 2172 1 := by
    have := E [2178, 140] [140, 2178] (by simp [eqs7])
    rwa [word2 (i := 1089) (j := 70) rfl rfl (by norm_num) (by norm_num),
      word2 (i := 70) (j := 1089) rfl rfl (by norm_num) (by norm_num)] at this
  have c3 : S7.getD 2164 1 * S7.getD 132 1 = S7.getD 132 1 * S7.getD 2164 1 := by
    have := E [2170, 138] [138, 2170] (by simp [eqs7])
    rwa [word2 (i := 1085) (j := 69) rfl rfl (by norm_num) (by norm_num),
      word2 (i := 69) (j := 1085) rfl rfl (by norm_num) (by norm_num)] at this
  have c4 : S7.getD 2166 1 * S7.getD 132 1 = S7.getD 132 1 * S7.getD 2166 1 := by
    have := E [2172, 138] [138, 2172] (by simp [eqs7])
    rwa [word2 (i := 1086) (j := 69) rfl rfl (by norm_num) (by norm_num),
      word2 (i := 69) (j := 1086) rfl rfl (by norm_num) (by norm_num)] at this
  have c5 : S7.getD 2168 1 * S7.getD 132 1 = S7.getD 132 1 * S7.getD 2168 1 := by
    have := E [2174, 138] [138, 2174] (by simp [eqs7])
    rwa [word2 (i := 1087) (j := 69) rfl rfl (by norm_num) (by norm_num),
      word2 (i := 69) (j := 1087) rfl rfl (by norm_num) (by norm_num)] at this
  have p4 : S7.getD 2410 1 ^ 4 = 1 := by
    have := E [2416, 2416, 2416, 2416] [] (by simp [eqs7])
    rwa [show [2416, 2416, 2416, 2416] = List.replicate 4 2416 from rfl, wordPow] at this
  have p2 : S7.getD 2410 1 ^ 2 ≠ 1 := by
    rwa [show [2416, 2416] = List.replicate 2 2416 from rfl, wordPow] at hne
  have r1 : eqRows 781 (mLetters Ws7)[2 * 1203]! (mLetters Ws7)[0]! = true :=
    eqRows_of_good ((good7 (k := 2406) (by norm_num)).congr e1) (good7 (k := 0) (by norm_num))
  have r2 : eqRows 781 (mLetters Ws7)[2 * 1204]! (mLetters Ws7)[2]! = true :=
    eqRows_of_good ((good7 (k := 2408) (by norm_num)).congr e2) (good7 (k := 2) (by norm_num))
  have r3 : eqRows 781 (mulW (mLetters Ws7)[2 * 1085]! (mLetters Ws7)[2 * 67]!)
      (mulW (mLetters Ws7)[2 * 67]! (mLetters Ws7)[2 * 1085]!) = true :=
    eqRows_of_good
      (((good7 (k := 2170) (by norm_num)).mulW (good7 (k := 134) (by norm_num))).congr c1)
      ((good7 (k := 134) (by norm_num)).mulW (good7 (k := 2170) (by norm_num)))
  have r4 : eqRows 781 (mulW (mLetters Ws7)[2 * 1086]! (mLetters Ws7)[2 * 67]!)
      (mulW (mLetters Ws7)[2 * 67]! (mLetters Ws7)[2 * 1086]!) = true :=
    eqRows_of_good
      (((good7 (k := 2172) (by norm_num)).mulW (good7 (k := 134) (by norm_num))).congr c2)
      ((good7 (k := 134) (by norm_num)).mulW (good7 (k := 2172) (by norm_num)))
  have r5 : eqRows 781 (mulW (mLetters Ws7)[2 * 1082]! (mLetters Ws7)[2 * 66]!)
      (mulW (mLetters Ws7)[2 * 66]! (mLetters Ws7)[2 * 1082]!) = true :=
    eqRows_of_good
      (((good7 (k := 2164) (by norm_num)).mulW (good7 (k := 132) (by norm_num))).congr c3)
      ((good7 (k := 132) (by norm_num)).mulW (good7 (k := 2164) (by norm_num)))
  have r6 : eqRows 781 (mulW (mLetters Ws7)[2 * 1083]! (mLetters Ws7)[2 * 66]!)
      (mulW (mLetters Ws7)[2 * 66]! (mLetters Ws7)[2 * 1083]!) = true :=
    eqRows_of_good
      (((good7 (k := 2166) (by norm_num)).mulW (good7 (k := 132) (by norm_num))).congr c4)
      ((good7 (k := 132) (by norm_num)).mulW (good7 (k := 2166) (by norm_num)))
  have r7 : eqRows 781 (mulW (mLetters Ws7)[2 * 1084]! (mLetters Ws7)[2 * 66]!)
      (mulW (mLetters Ws7)[2 * 66]! (mLetters Ws7)[2 * 1084]!) = true :=
    eqRows_of_good
      (((good7 (k := 2168) (by norm_num)).mulW (good7 (k := 132) (by norm_num))).congr c5)
      ((good7 (k := 132) (by norm_num)).mulW (good7 (k := 2168) (by norm_num)))
  have r8 : eqRows 781 (powW 781 (mLetters Ws7)[2 * 1205]! 4) (idW 781) = true :=
    eqRows_of_good ((good_powW (good7 (k := 2410) (by norm_num)) 4).congr p4) good_idW
  have r9 : eqRows 781 (powW 781 (mLetters Ws7)[2 * 1205]! 2) (idW 781) = false :=
    eqRows_false_of_good (good_powW (good7 (k := 2410) (by norm_num)) 2) good_idW p2
  unfold fi7OK
  simp only [words_eq, extra7_eq, conj_eq]
  simp only [Bool.and_eq_true, and_assoc]
  refine ⟨slp_ws7, by simp [w7_len], by simp [e7_len], by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    r1, r2, r3, r4, r5, r6, r7, r8, by rw [r9]; rfl⟩

end CertificateChecks.KernelF24S

end
