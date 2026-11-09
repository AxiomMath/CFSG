module

public import Certificates.Kernel.Sporadic.Fi24Sev.SevenB
public import Certificates.Kernel.Sporadic.Fi7Perm.Sl0
public import Certificates.Kernel.Sporadic.Fi7Perm.Sl1
public import Certificates.Kernel.Sporadic.Fi7Perm.Sl2
public import Certificates.Kernel.Sporadic.Fi7Perm.Sl3
import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.Fi7GenGroup

public section

namespace CFSG.KD.Fi7Perm.Final

open CFSG.HardMathSupport.Dickson.I271.Fi7
open CFSG.Sporadic.Fi24 (J gs)
open CFSG.Perm CFSG.Perm.Native CFSG.Sporadic.Th CFSG.KC CFSG.KC.Fi24ThreeO CFSG.KC.Fi24Sev
  CFSG.KC.Fi24SevB CFSG.KS.Fi24ThreeO CFSG.KS.Fi24Sev CFSG.KS.Fi24SevB CFSG.KD.Fi24Net
  CFSG.KD.Fi24Kit CFSG.KD.Fi24ThreeO.Group CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24SevenNative
  CFSG.KD.Fi24Sev.Words CFSG.KD.Fi24Sev.SevenB CFSG.KC.SlpM
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three

attribute [local instance] CFSG.Sporadic.Fi24.rAction

local notation "SL" => CFSG.KD.Fi7Perm.sl

local notation "WE" => CFSG.KC.SlpM.appL CFSG.KD.F24S.W7 CFSG.KD.F24S.E7

#kc_forall_tree CFSG.KD.Fi7Perm.Ck.slcAll (fun i => CFSG.KD.Fi7Perm.slc i = true) 182
  CFSG.KD.Fi7Perm.Ck.slc

theorem sl_split : SL = (List.range 182).flatMap CFSG.KD.Fi7Perm.slQ := by decide +kernel

theorem sl_codes : ∀ e ∈ SL, ∀ l ∈ e.2.2, l < 26 := by decide +kernel

theorem sl_words : ∀ e ∈ SL, e.1 < 1206 ∧ (WE).getD e.1 [] = e.2.1 := by decide +kernel

theorem sl_spec : ∀ e ∈ SL,
    (∀ z ∈ e.2.1, 2 ≤ z ∧ (z ≤ 5 ∨ (z / 2 - 3 < e.1 ∧ ∃ e' ∈ SL, e'.1 = z / 2 - 3))) ∧
      ∀ b ∈ cb, cP NW NT (expU SL e.2.1) b = cP NW NT e.2.2 b := by
  intro e he
  rw [sl_split, List.mem_flatMap] at he
  obtain ⟨i, hi, h⟩ := he
  cases hq : Nat.beq i 180 with
  | true =>
    rw [Nat.eq_of_beq_eq_true hq] at h
    exact slIn_spec CFSG.KD.Fi7Perm.Ck.sl180 e h
  | false =>
    have hc := CFSG.KD.Fi7Perm.Ck.slcAll i (List.mem_range.1 hi)
    unfold CFSG.KD.Fi7Perm.slc at hc
    rw [hq] at hc
    dsimp only at hc
    rw [slInB_eq, brec_same] at hc
    exact slIn_spec hc e h

theorem we_len : (WE).length = 1206 := by
  rw [CFSG.KC.SlpM.appL_eq, List.length_append, CertificateChecks.KernelF24S.w7_len,
    CertificateChecks.KernelF24S.e7_len]

theorem words_get {n : ℕ} (hn : n < 1206) :
    (fi24SevenData.words ++ fi7Extra ())[n]! = decW ((WE).getD n []) := by
  rw [CertificateChecks.KernelF24S.words_eq, CertificateChecks.KernelF24S.extra7_eq,
    CertificateChecks.KernelF24S.layer_words, getElem!_pos _ n (by simp [we_len]; omega)]
  simp only [List.getElem_toArray, List.getElem_map]
  rw [List.getD_eq_getElem _ _ (by rw [we_len]; omega)]

theorem words_eq (hB : Bridge) : ∀ e ∈ SL, wordElt e.2.2 = g17 e.1 := by
  have key : ∀ n, ∀ e ∈ SL, e.1 = n → wordElt e.2.2 = g17 n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro e he hen
      obtain ⟨hz, hag⟩ := sl_spec e he
      obtain ⟨hn, hw⟩ := sl_words e he
      rw [← wordElt_eq_of_cb hB (expU_lt sl_codes _) (sl_codes e he) hag, wordElt_expU, g17,
        CFSG.Sporadic.Fi23.slpG_eq]
      rw [hen] at hn hw
      rw [words_get hn, hw]
      unfold wordG decW
      rw [List.map_map]
      congr 1
      refine List.map_congr_left fun z hzm => ?_
      obtain ⟨hz2, hz'⟩ := hz z hzm
      simp only [Function.comp]
      have habs : (decC z).natAbs = z / 2 := by
        unfold decC
        split_ifs
        · rw [Int.natAbs_neg, Int.natAbs_natCast]
        · rw [Int.natAbs_natCast]
      by_cases h5 : z ≤ 5
      · rw [letU_small h5, genG_letter z hz2 h5, if_pos (by rw [habs]; omega)]
      · obtain ⟨hlt, e', he', he'k⟩ := hz'.resolve_left h5
        rw [hen] at hlt
        obtain ⟨e'', he'', he''k, hfu⟩ := findU_spec ⟨e', he', he'k⟩
        have hIH := ih _ hlt e'' he'' he''k
        rw [if_neg (by rw [habs]; omega), habs, if_pos hlt]
        unfold letU
        rw [ble_ne h5, lIf_false]
        have hsh : Nat.sub (Nat.shiftRight z 1) 3 = z / 2 - 3 := by
          simp [Nat.shiftRight_eq_div_pow]
        have hland : Nat.land z 1 = z % 2 := Nat.and_one_is_mod z
        rw [hsh, hfu, hland]
        by_cases hev : z % 2 = 0
        · have hd : decC z = ((z / 2 : ℕ) : ℤ) := by unfold decC; rw [if_neg (by omega)]
          rw [beq_of hev, lIf_true, hIH, g17,
            if_pos (by rw [hd]; exact_mod_cast (by omega : 0 < z / 2))]
        · have hd : decC z = -((z / 2 : ℕ) : ℤ) := by unfold decC; rw [if_pos (by omega)]
          rw [beq_ne hev, lIf_false, wordElt_invC hB (sl_codes e'' he''), hIH, g17,
            if_neg (by rw [hd]; omega)]
  exact fun e he => key e.1 e he rfl

theorem has_roots : ∀ k ∈ [0, 1, 66, 67, 1082, 1083, 1084, 1085, 1086, 1203, 1204, 1205],
    ∃ e ∈ SL, e.1 = k := by decide +kernel

theorem U_eq (hB : Bridge) {k : ℕ}
    (hk : k ∈ [0, 1, 66, 67, 1082, 1083, 1084, 1085, 1086, 1203, 1204, 1205]) :
    wordElt (CFSG.KD.Fi7Perm.U k) = g17 k := by
  obtain ⟨e, he, h1, h2⟩ := findU_spec (has_roots k hk)
  change wordElt (findU SL k) = _
  rw [h2, words_eq hB e he, h1]

theorem U_lt {k : ℕ} (hk : k ∈ [0, 1, 66, 67, 1082, 1083, 1084, 1085, 1086, 1203, 1204, 1205]) :
    ∀ l ∈ CFSG.KD.Fi7Perm.U k, l < 26 := by
  obtain ⟨e, he, -, h2⟩ := findU_spec (has_roots k hk)
  change ∀ l ∈ findU SL k, l < 26
  rw [h2]
  exact sl_codes e he

theorem layout : fi7Layout () = true := by
  unfold fi7Layout
  simp only [CertificateChecks.KernelF24S.words_eq, CertificateChecks.KernelF24S.extra7_eq,
    CertificateChecks.KernelF24S.conj_eq]
  simp only [Bool.and_eq_true, and_assoc]
  refine ⟨by simp [CertificateChecks.KernelF24S.w7_len], by simp [CertificateChecks.KernelF24S.e7_len],
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

theorem comm_of (hB : Bridge) {i k : ℕ}
    (hi : i ∈ [0, 1, 66, 67, 1082, 1083, 1084, 1085, 1086, 1203, 1204, 1205])
    (hk : k ∈ [0, 1, 66, 67, 1082, 1083, 1084, 1085, 1086, 1203, 1204, 1205])
    (hp : (CFSG.KD.Fi7Perm.U i ++ CFSG.KD.Fi7Perm.U k, CFSG.KD.Fi7Perm.U k ++ CFSG.KD.Fi7Perm.U i) ∈
      [(CFSG.KD.Fi7Perm.U 1085 ++ CFSG.KD.Fi7Perm.U 67, CFSG.KD.Fi7Perm.U 67 ++ CFSG.KD.Fi7Perm.U 1085),
        (CFSG.KD.Fi7Perm.U 1086 ++ CFSG.KD.Fi7Perm.U 67, CFSG.KD.Fi7Perm.U 67 ++ CFSG.KD.Fi7Perm.U 1086),
        (CFSG.KD.Fi7Perm.U 1082 ++ CFSG.KD.Fi7Perm.U 66, CFSG.KD.Fi7Perm.U 66 ++ CFSG.KD.Fi7Perm.U 1082),
        (CFSG.KD.Fi7Perm.U 1083 ++ CFSG.KD.Fi7Perm.U 66, CFSG.KD.Fi7Perm.U 66 ++ CFSG.KD.Fi7Perm.U 1083),
        (CFSG.KD.Fi7Perm.U 1084 ++ CFSG.KD.Fi7Perm.U 66, CFSG.KD.Fi7Perm.U 66 ++ CFSG.KD.Fi7Perm.U 1084),
        (pw (CFSG.KD.Fi7Perm.U 1205) 4, [])]) :
    g17 i * g17 k = g17 k * g17 i := by
  have hq := CFSG.KD.Fi7Perm.Ck.fEq_t
  unfold CFSG.KD.Fi7Perm.fEq at hq
  have e := eq_of_eqOK hB hq (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp))
    (app_lt (U_lt hi) (U_lt hk)) (app_lt (U_lt hk) (U_lt hi))
  rwa [wordElt_append, wordElt_append, U_eq hB hi, U_eq hB hk] at e

theorem fi7Group (hB : Bridge) : Fi7Group := by
  have hq := CFSG.KD.Fi7Perm.Ck.fEq_t
  have hn := CFSG.KD.Fi7Perm.Ck.fNe_t
  unfold CFSG.KD.Fi7Perm.fEq at hq
  unfold CFSG.KD.Fi7Perm.fNe at hn
  have e1 := eq_of_eqOK hB hq List.mem_cons_self (U_lt (k := 1203) (by simp)) (U_lt (k := 0) (by simp))
  have e2 := eq_of_eqOK hB hq (List.mem_cons_of_mem _ List.mem_cons_self)
    (U_lt (k := 1204) (by simp)) (U_lt (k := 1) (by simp))
  have e8 := eq_of_eqOK hB hq (u := pw (CFSG.KD.Fi7Perm.U 1205) 4) (v := [])
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))))
    (pw_lt (U_lt (k := 1205) (by simp)) 4) nil_lt
  have n1 := ne_of_neOK hB hn List.mem_cons_self (pw_lt (U_lt (k := 1205) (by simp)) 2) nil_lt
  rw [U_eq hB (by simp), U_eq hB (by simp)] at e1 e2
  rw [wordElt_pw, U_eq hB (by simp), wordElt_nil] at e8 n1
  exact
    { layout := layout
      wa := e1
      wb := e2
      comm85 := comm_of hB (by simp) (by simp) (by simp)
      comm86 := comm_of hB (by simp) (by simp) (by simp)
      comm82 := comm_of hB (by simp) (by simp) (by simp)
      comm83 := comm_of hB (by simp) (by simp) (by simp)
      comm84 := comm_of hB (by simp) (by simp) (by simp)
      pow4 := e8
      pow2 := n1 }

end CFSG.KD.Fi7Perm.Final

end
