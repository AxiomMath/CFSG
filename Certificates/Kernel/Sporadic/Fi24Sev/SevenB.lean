module

public import Certificates.Kernel.Sporadic.Fi24Sev.Seven
public import Certificates.Kernel.Sporadic.Fi24Sev.SlB
public import Certificates.Kernel.Sporadic.Fi24Sev.CjB
public import Certificates.Kernel.Sporadic.Fi24Sev.RelB
public import CFSG.Certificates.Kernel.Spor.Fi24SevBSound
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.FixCount

public section

namespace CFSG.KD.Fi24Sev.SevenB

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
open CFSG.Sporadic.Fi24 (J gs)
open CFSG.Perm CFSG.Perm.Native CFSG.Sporadic.Th CFSG.KC CFSG.KC.Fi24ThreeO CFSG.KC.Fi24Sev
  CFSG.KC.Fi24SevB CFSG.KS.Fi24ThreeO CFSG.KS.Fi24Sev CFSG.KS.Fi24SevB CFSG.KD.Fi24Net
  CFSG.KD.Fi24Kit CFSG.KD.Fi24ThreeO.Group CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24SevenNative
  CFSG.KD.Fi24Sev.Words

attribute [local instance] CFSG.Sporadic.Fi24.rAction


noncomputable abbrev sev (j : ℕ) : J :=
  CFSG.Sporadic.Fi23.slpG CFSG.Sporadic.Fi24.genG fi24SevenData.words j

local notation "SL" => CFSG.KD.Fi24SevB.sl

theorem sl_split : SL = CFSG.KD.Fi24SevB.slQ 0 ++ (CFSG.KD.Fi24SevB.slQ 1 ++
    (CFSG.KD.Fi24SevB.slQ 2 ++ CFSG.KD.Fi24SevB.slQ 3)) := by decide +kernel

theorem sl_codes : ∀ e ∈ SL, ∀ l ∈ e.2.2, l < 26 := by decide +kernel

theorem sl_words : ∀ e ∈ SL, e.1 < 1087 ∧ CFSG.KD.F24S.W7.getD e.1 [] = e.2.1 := by decide +kernel

theorem sl_spec : ∀ e ∈ SL,
    (∀ z ∈ e.2.1, 2 ≤ z ∧ (z ≤ 5 ∨ (z / 2 - 3 < e.1 ∧ ∃ e' ∈ SL, e'.1 = z / 2 - 3))) ∧
      ∀ b ∈ cb, cP NW NT (expU SL e.2.1) b = cP NW NT e.2.2 b := by
  intro e he
  rw [sl_split] at he
  simp only [List.mem_append] at he
  rcases he with h | h | h | h
  · exact slIn_spec CFSG.KD.Fi24SevB.Ck.slc0 e h
  · exact slIn_spec CFSG.KD.Fi24SevB.Ck.slc1 e h
  · exact slIn_spec CFSG.KD.Fi24SevB.Ck.slc2 e h
  · exact slIn_spec CFSG.KD.Fi24SevB.Ck.slc3 e h

theorem words_eq (hB : Bridge) : ∀ e ∈ SL, wordElt e.2.2 = sev e.1 :=
  wordElt_eq_slpG hB sl_spec sl_codes sl_words

theorem findU_eq (hB : Bridge) {k : ℕ} (hk : ∃ e ∈ SL, e.1 = k) : wordElt (findU SL k) = sev k := by
  obtain ⟨e, he, h1, h2⟩ := findU_spec hk
  rw [h2, words_eq hB e he, h1]

theorem findU_lt {k : ℕ} (hk : ∃ e ∈ SL, e.1 = k) : ∀ l ∈ findU SL k, l < 26 := by
  obtain ⟨e, he, -, h2⟩ := findU_spec hk
  rw [h2]
  exact sl_codes e he

theorem wordElt_pw (u : List ℕ) : ∀ n, wordElt (pw u n) = wordElt u ^ n
  | 0 => rfl
  | n + 1 => by
    change wordElt (u ++ pw u n) = _
    rw [wordElt_append, wordElt_pw u n, pow_succ']

theorem pw_lt {u : List ℕ} (hu : ∀ l ∈ u, l < 26) : ∀ n, ∀ l ∈ pw u n, l < 26
  | 0 => fun _ h => absurd h List.not_mem_nil
  | n + 1 => fun l hl => by
    change l ∈ u ++ pw u n at hl
    rcases List.mem_append.1 hl with h | h
    · exact hu l h
    · exact pw_lt hu n l h

theorem cP_pw (u : List ℕ) : ∀ (n x : ℕ), cP NW NT (pw u n) x = (cP NW NT u)^[n] x
  | 0, _ => rfl
  | n + 1, x => by
    change cP NW NT (u ++ pw u n) x = _
    rw [cP_append, cP_pw u n x, Function.iterate_succ_apply']

theorem app_lt {u v : List ℕ} (hu : ∀ l ∈ u, l < 26) (hv : ∀ l ∈ v, l < 26) : ∀ l ∈ u ++ v, l < 26 :=
  fun l hl => (List.mem_append.1 hl).elim (hu l) (hv l)

theorem nil_lt : ∀ l ∈ ([] : List ℕ), l < 26 := fun _ h => absurd h List.not_mem_nil

theorem eq_of_eqOK (hB : Bridge) {ps : List (List ℕ × List ℕ)} (h : eqOK NW NT ps = true)
    {u v : List ℕ} (hp : (u, v) ∈ ps) (hu : ∀ l ∈ u, l < 26) (hv : ∀ l ∈ v, l < 26) :
    wordElt u = wordElt v :=
  wordElt_eq_of_cb hB hu hv (eqOK_spec h (u, v) hp)

theorem ne_of_neOK (hB : Bridge) {ps : List (List ℕ × List ℕ)} (h : neOK NW NT ps = true)
    {u v : List ℕ} (hp : (u, v) ∈ ps) (hu : ∀ l ∈ u, l < 26) (hv : ∀ l ∈ v, l < 26) :
    wordElt u ≠ wordElt v := by
  obtain ⟨b, hb, hne⟩ := neOK_spec h (u, v) hp
  intro e
  have hb' : b < 306936 := by
    simp only [cb, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hb
    rcases hb with h | h | h | h | h | h <;> rw [h] <;> norm_num
  have e1 := word_val hB u hu ⟨b, hb'⟩
  have e2 := word_val hB v hv ⟨b, hb'⟩
  rw [e] at e1
  exact hne (e1.symm.trans e2)

theorem hasX : ∃ e ∈ SL, e.1 = 64 := by decide +kernel
theorem hasY : ∃ e ∈ SL, e.1 = 66 := by decide +kernel
theorem hasC : ∃ e ∈ SL, e.1 = 67 := by decide +kernel

theorem X_eq (hB : Bridge) : wordElt CFSG.KD.Fi24SevB.X = sev 64 := findU_eq hB hasX
theorem Y_eq (hB : Bridge) : wordElt CFSG.KD.Fi24SevB.Y = sev 66 := findU_eq hB hasY
theorem C_eq (hB : Bridge) : wordElt CFSG.KD.Fi24SevB.C = sev 67 := findU_eq hB hasC

theorem X_lt : ∀ l ∈ CFSG.KD.Fi24SevB.X, l < 26 := findU_lt hasX
theorem Y_lt : ∀ l ∈ CFSG.KD.Fi24SevB.Y, l < 26 := findU_lt hasY
theorem C_lt : ∀ l ∈ CFSG.KD.Fi24SevB.C, l < 26 := findU_lt hasC

theorem cube_facts (hB : Bridge) :
    sev 64 ^ 7 = 1 ∧ sev 66 ^ 7 = 1 ∧ sev 67 = sev 64 * sev 66 * sev 64 ^ 6 * sev 66 ^ 6 ∧
      sev 67 * sev 64 = sev 64 * sev 67 ∧ sev 67 * sev 66 = sev 66 * sev 67 ∧ sev 67 ≠ 1 := by
  have hq := CFSG.KD.Fi24SevB.Ck.qEq_t
  have hn := CFSG.KD.Fi24SevB.Ck.qNe_t
  unfold CFSG.KD.Fi24SevB.qEq at hq
  unfold CFSG.KD.Fi24SevB.qNe at hn
  have e1 := eq_of_eqOK hB hq (List.mem_cons_self) (pw_lt X_lt 7) nil_lt
  have e2 := eq_of_eqOK hB hq (List.mem_cons_of_mem _ List.mem_cons_self) C_lt
    (app_lt X_lt (app_lt Y_lt (app_lt (pw_lt X_lt 6) (pw_lt Y_lt 6))))
  have e3 := eq_of_eqOK hB hq (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    (app_lt C_lt X_lt) (app_lt X_lt C_lt)
  have e4 := eq_of_eqOK hB hq
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    (app_lt C_lt Y_lt) (app_lt Y_lt C_lt)
  have n1 := ne_of_neOK hB hn List.mem_cons_self C_lt nil_lt
  simp only [wordElt_pw, wordElt_append, X_eq hB, Y_eq hB, C_eq hB, wordElt_nil] at e1 e2 e3 e4 n1
  have hy7 : sev 66 ^ 7 = 1 := by
    have h := (relOK_spec CFSG.KD.Fi24Sev.Ck.relA_t).1
    have hw := CFSG.KD.Fi24Sev.Cent.sideA.1
    obtain ⟨e, he, h1, h2⟩ := CFSG.KD.Fi24Sev.Seven.sl_y
    rw [← h1]
    change (CFSG.Sporadic.Fi23.slpG CFSG.Sporadic.Fi24.genG fi24SevenData.words e.1) ^ 7 = 1
    rw [← CFSG.KD.Fi24Sev.Seven.words_eq hB e he, h2]
    have hp : wordElt (pw CFSG.KD.Fi24Sev.wrA 7) = wordElt [] := wordElt_eq_of_cb hB (pw_lt hw 7) nil_lt
      (fun b hb => by rw [cP_pw]; exact h b hb)
    rw [wordElt_pw] at hp
    exact hp
  exact ⟨e1, hy7, by rw [e2]; group, e3, e4, n1⟩

noncomputable abbrev M7 (t : ℕ) : J := ((fi24SevenData.conj[t]!).2.map (pairG sev)).prod

noncomputable abbrev cube7 (t : ℕ) : J := sev 64 ^ (t / 49) * sev 66 ^ (t / 7 % 7) * sev 67 ^ (t % 7)

theorem cj_data : ∀ c ∈ CFSG.KD.Fi24SevB.cj, c.1 < 343 ∧
    CFSG.KD.F24S.C7.getD c.1 (0, []) = (c.2.1, c.2.2.1) ∧ ∀ l ∈ c.2.2.2, l < 26 := by decide +kernel

theorem cj_ts : CFSG.KD.Fi24SevB.cj.map Prod.fst = [3, 21, 49, 56, 63, 70, 77, 84, 91] := by
  decide +kernel

theorem cj_split : CFSG.KD.Fi24SevB.cj =
    (CFSG.KD.Fi24SevB.cj.drop (0 * 3)).take 3 ++ ((CFSG.KD.Fi24SevB.cj.drop (1 * 3)).take 3 ++
      (CFSG.KD.Fi24SevB.cj.drop (2 * 3)).take 3) := by decide +kernel

theorem mW_eq (hB : Bridge) : ∀ (w : List ℕ), (∀ l ∈ w, ∃ e ∈ SL, e.1 = l / 2) →
    wordElt (mW SL w) = (w.map (pairG sev)).prod ∧ ∀ l ∈ mW SL w, l < 26
  | [], _ => ⟨rfl, nil_lt⟩
  | l :: w, hw => by
    obtain ⟨ih1, ih2⟩ := mW_eq hB w (fun l' h => hw l' (List.mem_cons_of_mem l h))
    have hk := hw l List.mem_cons_self
    change wordElt (lIf (Nat.beq (Nat.land l 1) 0) (findU SL (Nat.shiftRight l 1))
      (invC (findU SL (Nat.shiftRight l 1))) ++ mW SL w) = _ ∧ ∀ x ∈ lIf (Nat.beq (Nat.land l 1) 0)
      (findU SL (Nat.shiftRight l 1)) (invC (findU SL (Nat.shiftRight l 1))) ++ mW SL w, x < 26
    have hsh : Nat.shiftRight l 1 = l / 2 := by simp [Nat.shiftRight_eq_div_pow]
    have hland : Nat.land l 1 = l % 2 := Nat.and_one_is_mod l
    rw [hsh, hland, List.map_cons, List.prod_cons]
    by_cases hev : l % 2 = 0
    · rw [beq_of hev, lIf_true]
      refine ⟨by rw [wordElt_append, ih1, findU_eq hB hk]; simp [pairG, hev], app_lt (findU_lt hk) ih2⟩
    · rw [beq_ne hev, lIf_false]
      have hp : pairG sev l = (sev (l / 2))⁻¹ := by simp [pairG, hev]
      refine ⟨?_, app_lt (CFSG.KD.Fi24ThreeO.invC_lt (findU_lt hk)) ih2⟩
      rw [wordElt_append, ih1, wordElt_invC hB (findU_lt hk), findU_eq hB hk, hp]

theorem cubeW_eq (hB : Bridge) (t : ℕ) :
    wordElt (cubeW SL t) = cube7 t ∧ ∀ l ∈ cubeW SL t, l < 26 := by
  unfold cubeW
  refine ⟨?_, app_lt (pw_lt X_lt _) (app_lt (pw_lt Y_lt _) (pw_lt C_lt _))⟩
  rw [wordElt_append, wordElt_append, wordElt_pw, wordElt_pw, wordElt_pw]
  change wordElt CFSG.KD.Fi24SevB.X ^ _ * (wordElt CFSG.KD.Fi24SevB.Y ^ _ *
    wordElt CFSG.KD.Fi24SevB.C ^ _) = _
  rw [X_eq hB, Y_eq hB, C_eq hB, ← mul_assoc]
  rfl

theorem conj_facts (hB : Bridge) {t : ℕ} (ht : t ∈ [3, 21, 49, 56, 63, 70, 77, 84, 91]) :
    M7 t * cube7 t = (if (fi24SevenData.conj[t]!).1 == 0 then sev 66 else sev 67) * M7 t := by
  rw [← cj_ts, List.mem_map] at ht
  obtain ⟨c, hc, rfl⟩ := ht
  have hok : cjOK NW NT SL c = true := by
    have hc' := hc
    rw [cj_split] at hc'
    simp only [List.mem_append] at hc'
    rcases hc' with h | h | h
    · exact allL_spec CFSG.KD.Fi24SevB.Ck.cjc0 c h
    · exact allL_spec CFSG.KD.Fi24SevB.Ck.cjc1 c h
    · exact allL_spec CFSG.KD.Fi24SevB.Ck.cjc2 c h
  obtain ⟨h1, h2, h3⟩ := cjOK_spec hok
  obtain ⟨hlt, hC7, hm⟩ := cj_data c hc
  have hconj : fi24SevenData.conj[c.1]! = (c.2.1, c.2.2.1) := by
    rw [CertificateChecks.KernelF24S.conj_eq, ← hC7,
      getElem!_pos _ c.1 (by simp [CertificateChecks.KernelF24S.c7_len]; omega)]
    simp only [List.getElem_toArray]
    rw [List.getD_eq_getElem _ _ (by rw [CertificateChecks.KernelF24S.c7_len]; omega)]
  obtain ⟨em, emlt⟩ := mW_eq hB c.2.2.1 h1
  have hM : M7 c.1 = wordElt c.2.2.2 := by
    rw [M7, hconj, ← em]
    exact wordElt_eq_of_cb hB emlt hm h2
  obtain ⟨ec, eclt⟩ := cubeW_eq hB c.1
  have hR : ∀ l ∈ lIf (Nat.beq c.2.1 0) (findU SL 66) (findU SL 67), l < 26 := by
    cases Nat.beq c.2.1 0
    · exact findU_lt hasC
    · exact findU_lt hasY
  have e3 := wordElt_eq_of_cb hB (app_lt hm eclt) (app_lt hR hm) h3
  rw [wordElt_append, wordElt_append, ec, ← hM] at e3
  have hr : (fi24SevenData.conj[c.1]!).1 = c.2.1 := by rw [hconj]
  rw [e3, hr]
  by_cases h0 : c.2.1 = 0
  · rw [beq_of h0, lIf_true, findU_eq hB hasY, if_pos (by rw [h0]; rfl)]
  · rw [beq_ne h0, lIf_false, findU_eq hB hasC, if_neg (by
      intro h
      exact h0 (beq_iff_eq.1 h))]

open CFSG.KD.Fi24SevB (uW vW uvW uv2W u4W u2W u3W)

theorem elt_lt : (∀ l ∈ uW, l < 26) ∧ (∀ l ∈ vW, l < 26) ∧ (∀ l ∈ uvW, l < 26) ∧
    (∀ l ∈ uv2W, l < 26) ∧ (∀ l ∈ u4W, l < 26) ∧ (∀ l ∈ u2W, l < 26) ∧ (∀ l ∈ u3W, l < 26) := by
  decide +kernel

theorem card_fixS_word (hB : Bridge) {w : List ℕ} (hw : ∀ l ∈ w, l < 26) :
    (CFSG.HardMathSupport.Solomon.Coordinator.YS08.fixS (wordElt w) : Finset (Fin 306936)).card =
      ((Finset.range 306936).filter fun x => cP NW NT w x = x).card := by
  refine Finset.card_bij (fun a _ => a.val) (fun a ha => ?_) (fun a _ b _ h => Fin.ext h)
    (fun b hb => ?_)
  · rw [CFSG.HardMathSupport.Solomon.Coordinator.YS08.mem_fixS] at ha
    rw [Finset.mem_filter, Finset.mem_range, ← word_val hB w hw, ha]
    exact ⟨a.isLt, rfl⟩
  · rw [Finset.mem_filter, Finset.mem_range] at hb
    refine ⟨⟨b, hb.1⟩, ?_, rfl⟩
    rw [CFSG.HardMathSupport.Solomon.Coordinator.YS08.mem_fixS]
    apply Fin.ext
    rw [word_val hB w hw]
    exact hb.2

theorem fix_count (hB : Bridge) {w : List ℕ} (hw : ∀ l ∈ w, l < 26) {n : ℕ}
    (h : fixK NW NT w n = true) :
    (CFSG.HardMathSupport.Solomon.Coordinator.YS08.fixS (wordElt w) : Finset (Fin 306936)).card = n := by
  rw [card_fixS_word hB hw]
  exact fixK_spec CFSG.KD.Fi24ThreeO.vn h

theorem elt_facts (hB : Bridge) :
    wordElt uW ^ 3 = 1 ∧ wordElt vW ^ 3 = 1 ∧ wordElt uW * wordElt vW = wordElt vW * wordElt uW ∧
      wordElt uW * sev 66 = sev 66 * wordElt uW ∧ wordElt vW * sev 66 = sev 66 * wordElt vW ∧
      wordElt uW ≠ 1 ∧ wordElt vW ≠ 1 ∧ wordElt vW ≠ wordElt uW ∧ wordElt vW ≠ wordElt uW * wordElt uW ∧
      wordElt u4W ^ 4 = 1 ∧ wordElt u4W ^ 2 ≠ 1 ∧ wordElt u4W * sev 66 = sev 66 * wordElt u4W ∧
      wordElt u2W ^ 2 = 1 ∧ wordElt u2W ≠ 1 ∧ wordElt u2W * sev 67 = sev 67 * wordElt u2W ∧
      wordElt u2W * sev 64 = sev 64 ^ 6 * wordElt u2W ∧
      wordElt u2W * sev 66 = sev 66 ^ 6 * (sev 67 ^ 6 * wordElt u2W) ∧
      wordElt u3W ^ 3 = 1 ∧ wordElt u3W ≠ 1 ∧ wordElt u3W * sev 67 = sev 67 * wordElt u3W ∧
      wordElt u3W * sev 64 = sev 64 ^ 4 * wordElt u3W ∧
      wordElt u3W * sev 66 = sev 66 ^ 2 * (sev 67 ^ 4 * wordElt u3W) := by
  obtain ⟨hu, hv, huv, huv2, hu4, hu2, hu3⟩ := elt_lt
  have hE := CFSG.KD.Fi24SevB.Ck.eEq_t
  have hN := CFSG.KD.Fi24SevB.Ck.eNe_t
  unfold CFSG.KD.Fi24SevB.eEq at hE
  unfold CFSG.KD.Fi24SevB.eNe at hN
  have e1 := eq_of_eqOK hB hE (by simp) (pw_lt hu 3) nil_lt
  have e2 := eq_of_eqOK hB hE (by simp) (pw_lt hv 3) nil_lt
  have e3 := eq_of_eqOK hB hE (by simp) (app_lt hu hv) (app_lt hv hu)
  have e6 := eq_of_eqOK hB hE (by simp) (app_lt hu Y_lt) (app_lt Y_lt hu)
  have e7 := eq_of_eqOK hB hE (by simp) (app_lt hv Y_lt) (app_lt Y_lt hv)
  have e8 := eq_of_eqOK hB hE (by simp) (pw_lt hu4 4) nil_lt
  have e9 := eq_of_eqOK hB hE (by simp) (app_lt hu4 Y_lt) (app_lt Y_lt hu4)
  have e10 := eq_of_eqOK hB hE (by simp) (pw_lt hu2 2) nil_lt
  have e11 := eq_of_eqOK hB hE (by simp) (app_lt hu2 C_lt) (app_lt C_lt hu2)
  have e12 := eq_of_eqOK hB hE (by simp) (pw_lt hu3 3) nil_lt
  have e13 := eq_of_eqOK hB hE (by simp) (app_lt hu3 C_lt) (app_lt C_lt hu3)
  have e14 := eq_of_eqOK hB hE (by simp) (app_lt hu2 X_lt) (app_lt (pw_lt X_lt 6) hu2)
  have e15 := eq_of_eqOK hB hE (by simp) (app_lt hu2 Y_lt) (app_lt (pw_lt Y_lt 6) (app_lt (pw_lt C_lt 6) hu2))
  have e16 := eq_of_eqOK hB hE (by simp) (app_lt hu3 X_lt) (app_lt (pw_lt X_lt 4) hu3)
  have e17 := eq_of_eqOK hB hE (by simp) (app_lt hu3 Y_lt) (app_lt (pw_lt Y_lt 2) (app_lt (pw_lt C_lt 4) hu3))
  have n1 := ne_of_neOK hB hN (by simp) hu nil_lt
  have n2 := ne_of_neOK hB hN (by simp) hv nil_lt
  have n3 := ne_of_neOK hB hN (by simp) hv hu
  have n4 := ne_of_neOK hB hN (by simp) hv (app_lt hu hu)
  have n5 := ne_of_neOK hB hN (by simp) (pw_lt hu4 2) nil_lt
  have n6 := ne_of_neOK hB hN (by simp) hu2 nil_lt
  have n7 := ne_of_neOK hB hN (by simp) hu3 nil_lt
  simp only [wordElt_pw, wordElt_append, X_eq hB, Y_eq hB, C_eq hB, wordElt_nil] at e1 e2 e3 e6 e7 e8
  simp only [wordElt_pw, wordElt_append, X_eq hB, Y_eq hB, C_eq hB, wordElt_nil] at e9 e10 e11 e12 e13
  simp only [wordElt_pw, wordElt_append, X_eq hB, Y_eq hB, C_eq hB, wordElt_nil] at e14 e15 e16 e17
  simp only [wordElt_pw, wordElt_append, wordElt_nil] at n1 n2 n3 n4 n5 n6 n7
  exact ⟨e1, e2, e3, e6, e7, n1, n2, n3, n4, e8, n5, e9, e10, n6, e11, e14, e15, e12, n7, e13, e16, e17⟩

theorem fix_facts (hB : Bridge) :
    (CFSG.HardMathSupport.Solomon.Coordinator.YS08.fixS (wordElt uW) : Finset (Fin 306936)).card = 0 ∧
    (CFSG.HardMathSupport.Solomon.Coordinator.YS08.fixS (wordElt vW) : Finset (Fin 306936)).card = 0 ∧
    (CFSG.HardMathSupport.Solomon.Coordinator.YS08.fixS (wordElt uW * wordElt vW) :
      Finset (Fin 306936)).card = 3240 ∧
    (CFSG.HardMathSupport.Solomon.Coordinator.YS08.fixS (wordElt uW * wordElt vW * wordElt vW) :
      Finset (Fin 306936)).card = 3240 ∧
    (CFSG.HardMathSupport.Solomon.Coordinator.YS08.fixS (wordElt u3W) : Finset (Fin 306936)).card = 378 ∧
    (CFSG.HardMathSupport.Solomon.Coordinator.YS08.fixS (sev 66) : Finset (Fin 306936)).card = 21 ∧
    (CFSG.HardMathSupport.Solomon.Coordinator.YS08.fixS (sev 67) : Finset (Fin 306936)).card = 0 := by
  obtain ⟨hu, hv, huv, huv2, -, -, hu3⟩ := elt_lt
  have hE := CFSG.KD.Fi24SevB.Ck.eEq_t
  unfold CFSG.KD.Fi24SevB.eEq at hE
  have e4 := eq_of_eqOK hB hE (u := uvW) (v := uW ++ vW) (by simp) huv (app_lt hu hv)
  have e5 := eq_of_eqOK hB hE (u := uv2W) (v := uW ++ (vW ++ vW)) (by simp) huv2
    (app_lt hu (app_lt hv hv))
  rw [wordElt_append] at e4
  rw [wordElt_append, wordElt_append, ← mul_assoc] at e5
  rw [← e5, ← e4, ← Y_eq hB, ← C_eq hB]
  exact ⟨fix_count hB hu CFSG.KD.Fi24SevB.Ck.fU_t, fix_count hB hv CFSG.KD.Fi24SevB.Ck.fV_t,
    fix_count hB huv CFSG.KD.Fi24SevB.Ck.fUV_t, fix_count hB huv2 CFSG.KD.Fi24SevB.Ck.fUV2_t,
    fix_count hB hu3 CFSG.KD.Fi24SevB.Ck.fU3_t, fix_count hB Y_lt CFSG.KD.Fi24SevB.Ck.fY_t,
    fix_count hB C_lt CFSG.KD.Fi24SevB.Ck.fC_t⟩

end CFSG.KD.Fi24Sev.SevenB

end
