module

public import Certificates.Kernel.Griess13.GlueData
public import Certificates.Kernel.Griess13.Checks
public import CFSG.Certificates.Kernel.Griess13.GlueSound

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelG13

open CFSG.KC.G13 CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KC.M1F2 CertificateChecks.KernelCo1Cover
  CFSG.Monster.GMS.Griess13.Co1Data CFSG.Sporadic.SmallF2.Native
open scoped Matrix

theorem parse2_eq : parseSLP slpMax2 = slp2 := by
  rw [Slp2.eq, charsEq_sound slp2_text, parseSLP_slpC]

theorem parseAB_eq : parseSLP slpWordsAB = slpAB := by
  rw [SlpAB.eq, charsEq_sound slpAB_text, parseSLP_slpC]

theorem prHout_eq : prHout = GD.H.map toPR := by
  rw [prHout, parse2_eq, prA_eq, prB_eq]
  change slp2.evalPR ([pk R0 R0, pk R1 G.B2].map toPR) = _
  rw [evalPR_toPR, h_ok]

theorem prG_eq : prG = toPR GD.G := by
  rw [prG, prHout_eq, toPR_word, g_ok]

theorem prX_eq (k : Fin 3) : prX k = toPR (GD.X.getD k.val 0) := by
  rw [prX, prWN_eq, x_ok]

theorem prY_eq (k : Fin 3) : prY k = toPR (GD.Y.getD k.val 0) := by
  rw [prY, prWN_eq, y_ok]

theorem prAB_eq : prAB = GD.AB.map toPR := by
  rw [prAB, parseAB_eq, prN1_eq, prN2_eq, prG_eq]
  change slpAB.evalPR ([G.N1, G.N2, GD.G].map toPR) = _
  rw [evalPR_toPR, ab_ok]

theorem tmatPay_eq (i : Nat) : tmatPay i = String.ofList (tmatC i) := by
  rw [← String.toList_inj, String.toList_ofList, tmatPay]
  change ("T\n" ++ ((tmatBits.drop (576 * i)).take 576).copy).toList = _
  rw [String.toList_append, String.Slice.toList_copy_take, String.toList_copy_drop, TB.eq]
  simp only [String.toList_ofList, tmatC, List.cons_append, List.nil_append]
  rfl

theorem trows_eq {i : Nat} (hi : i < 8) : trows i = unpackR 24 (GD.T.getD i 0) := by
  rw [trows, tmatPay_eq]
  exact bind_sound (tm_ok i hi)

theorem gCheck_true : gCheck = true := by
  simp only [gCheck, prG_eq, prX_eq, prY_eq, toPR_pow, toPR_one, toPR_mul, toPR_inv, toPR_eq]
  decide +kernel

theorem freeCheckK : ∀ i : Fin 8, ∀ j : Fin 8,
    ((unpackR 24 (GD.T.getD i.val 0))[freePos.getD j.val 0 / 24]?.getD 0).testBit
      (freePos.getD j.val 0 % 24) = decide (i = j) := by
  decide +kernel

theorem freeCheck_true : freeCheck = true := by
  simp only [freeCheck, List.all_eq_true, beq_iff_eq]
  intro i _ j _
  rw [trows_eq i.isLt]
  exact freeCheckK i j

theorem freePos_lt : ∀ j : Fin 8, freePos.getD j.val 0 < 576 := by decide

theorem oneCheck_true : oneCheck = true := by
  rw [oneCheck, trows_eq (by norm_num), idRows_eq, eqRows_unpackR]
  decide +kernel

theorem commuteK : ∀ i : Fin 8, ∀ k : Fin 3,
    eqK (mulWK (GD.T.getD i.val 0) (GD.X.getD k.val 0)) (mulWK (GD.X.getD k.val 0) (GD.T.getD i.val 0))
      = true := by
  decide +kernel

theorem commuteCheck_true : commuteCheck = true := by
  simp only [commuteCheck, List.all_eq_true]
  intro i _ k _
  rw [trows_eq i.isLt, prX_eq]
  change eqRows (mulRows 24 (unpackR 24 _) (unpackR 24 _)) (mulRows 24 (unpackR 24 _) (unpackR 24 _)) = true
  rw [mulWK_unpack, mulWK_unpack, eqRows_unpackR]
  exact commuteK i k

theorem xRows_eq : xRows = GD.X.map (unpackR 24) := by
  rw [xRows, prX_eq, prX_eq, prX_eq]
  rfl

theorem el_all : ∀ r < 1728, eqMaskK (GD.X.getD (r / 576) 0) (r % 576 / 24) (r % 24) = GD.E.getD r 0 := by
  intro r hr
  have step : ∀ (o : Nat), (∀ s < 216, elK (o + s) = GD.E.getD (o + s) 0) → o ≤ r → r < o + 216 →
      elK r = GD.E.getD r 0 := by
    intro o ho h1 h2
    have e := ho (r - o) (by omega)
    rwa [Nat.add_sub_cancel' h1] at e
  by_cases h0 : r < 216
  · exact el0 r h0
  by_cases h1 : r < 432
  · exact step 216 el1 (by omega) (by omega)
  by_cases h2 : r < 648
  · exact step 432 el2 (by omega) (by omega)
  by_cases h3 : r < 864
  · exact step 648 el3 (by omega) (by omega)
  by_cases h4 : r < 1080
  · exact step 864 el4 (by omega) (by omega)
  by_cases h5 : r < 1296
  · exact step 1080 el5 (by omega) (by omega)
  by_cases h6 : r < 1512
  · exact step 1296 el6 (by omega) (by omega)
  exact step 1512 el7 (by omega) (by omega)

theorem spanCheck_true : spanCheckWith (eqsOf xRows) (fmaskOf freePos) certTab = true := by
  rw [xRows_eq, eqsOf_map_unpackR (by decide) el_len el_all, spanCheckWith_toArray]
  exact span_ok

theorem freePos_surj : ∀ a ∈ freePos, ∃ j : Fin 8, freePos.getD j.val 0 = a := by decide

theorem seventh_aux : ∀ c : Fin 8 → ZMod 2,
    eqRows (powRows 24 (mulRows 24 prG.r (comboRows c)) 7) (idRows 24) = true →
      eqRows (comboRows c) (idRows 24) = true := by
  intro c
  rw [comboRows_eq (fun i hi => trows_eq hi), prG_eq]
  change eqRows (powRows 24 (mulRows 24 (unpackR 24 _) _) 7) _ = true → _
  rw [mulWK_unpack, powRows_unpackR, idRows_eq, eqRows_unpackR, eqRows_unpackR]
  exact seventh_ok c

theorem abCheck_true : abCheck = true := by
  simp only [abCheck, prAB_eq, getD_toPR, prA_eq, prB_eq, toPR_eq]
  decide +kernel

open Certificates in
open CFSG.Monster.GMS.Griess13.Co1Data in
open scoped Matrix in
open CFSG.Sporadic.SmallF2.Native (mulRows idRows powRows rowsOfPayload ofBits) in
theorem facts10033 :
    (gCheck = true)
    ∧ (freeCheck = true)
    ∧ (∀ j : Fin 8, freePos.getD j.val 0 < 576)
    ∧ (oneCheck = true)
    ∧ (commuteCheck = true)
    ∧ (spanCheckWith (eqsOf xRows) (fmaskOf freePos) certTab = true)
    ∧ (∀ a ∈ freePos, ∃ j : Fin 8, freePos.getD j.val 0 = a)
    ∧ (∀ c : Fin 8 → ZMod 2,
      eqRows (powRows 24 (mulRows 24 prG.r (comboRows c)) 7) (idRows 24) = true →
        eqRows (comboRows c) (idRows 24) = true)
    ∧ (abCheck = true) :=
  ⟨gCheck_true, freeCheck_true, freePos_lt, oneCheck_true, commuteCheck_true, spanCheck_true,
    freePos_surj, seventh_aux, abCheck_true⟩

end CertificateChecks.KernelG13

end
