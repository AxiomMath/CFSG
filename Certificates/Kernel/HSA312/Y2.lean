module

public import Certificates.Kernel.HSA312.Y1
public import Certificates.Kernel.HSA312.CY2
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 100000

public section

namespace CFSG.KD.HSA312

open CFSG.KC.Enum CFSG.KS CFSG.KC.LQT.PcW CFSG.KC.HSA312
open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.HS
open CFSG.QuasithinUnique.K1.SporadicPerm (hsB compArr applyTab ptsOf img)
open CFSG.Quasithin.A312S CFSG.Quasithin.A312S.HS
open CFSG.Sporadic.HS.Native (hsData)

theorem hL2K_eq : hsL2K = CFSG.Quasithin.A312Hs.hsLettersK 2 := rfl

theorem rL2 : ∀ l < hsL2K.length, Rep 1100 11 (CFSG.KD.LQT.H4089.L2c l) hsL2K[l]! := by
  rw [hL2K_eq, len2]
  exact hL2K

theorem rW : RepL 1100 11 Ws hsWK := by
  unfold hsWK
  rw [n_eq]
  exact repL_words hn' hw' hid rL2 (by rw [hL2K_eq, len2]; decide) rfl wW

theorem rW3 : RepL 1100 11 W3s (hsWK.map fun e => powTab 1100 e 3) :=
  rW.pow hn' hw' hid 3 rfl w3P

theorem rV : RepL 1100 11 Vs hsVTabsK.toList := by
  unfold hsVTabsK
  rw [n_eq, List.toList_toArray]
  exact repL_words hn' hw' hid rL2 (by rw [hL2K_eq, len2]; decide) rfl vW

theorem rL2s : RepL 1100 11 L2s hsL2K.toArray.toList := by
  rw [List.toList_toArray]
  refine RepL.of_get (by rw [hL2K_eq, len2]; rfl) fun j hj => ?_
  have hj4 : j < 4 := by rwa [hL2K_eq, len2] at hj
  have e : L2s.getD j 0 = CFSG.KD.LQT.H4089.L2c j := by
    unfold L2s
    rw [List.getD_eq_getElem _ _ (by simpa using hj4)]
    simp
  rw [e]
  exact rL2 j hj

noncomputable abbrev Rt : List (Array Nat) := hsQuot2.map (quotGt 1100 hsL2K)

theorem lenQ : hsQuot2.length = 2 := rfl

theorem lenK : hsKer.length = 4 := rfl

theorem lenKs : Ks.length = 4 := rfl

theorem lenRt : Rt.length = 2 := rfl

theorem rR : ∀ i < 2, Rep 1100 11 (R i) Rt[i]! := by
  intro i hi
  have hiQ : i < hsQuot2.length := by rw [lenQ]; exact hi
  have hiR : i < Rt.length := by rw [lenRt]; exact hi
  have hl : ∀ x ∈ hsQuot2, ∀ l ∈ x.w, l < hsL2K.length := by rw [hL2K_eq, len2]; decide
  have hx : hsQuot2.getD i default ∈ hsQuot2 := by
    rw [List.getD_eq_getElem hsQuot2 default hiQ]
    exact List.getElem_mem _
  have e : qtW 1100 11 (mask 11) I CFSG.KD.LQT.H4089.L2c (hsQuot2.getD i default).w
      (hsQuot2.getD i default).k = R i :=
    Nat.eq_of_beq_eq_true (List.all_eq_true.1 rQ i (List.mem_range.2 hiQ))
  have h := rep_qt hn' hw' hid (hsQuot2.getD i default) (rep_letters rL2 (hl _ hx))
  rw [e] at h
  have e2 : Rt[i]! = quotGt 1100 hsL2K (hsQuot2.getD i default) := by
    rw [getElem!_pos Rt i hiR, List.getElem_map, List.getD_eq_getElem hsQuot2 default hiQ]
  rw [e2]
  exact h

theorem rRt : ∀ l < 2, Rep 1100 11 (R l) (Rt.toArray.getD l #[]) := fun l hl => by
  rw [getD_toArray (by rw [lenRt]; exact hl)]
  exact rR l hl

theorem rK : RepL 1100 11 Ks (hsKer.map (kerGt 1100 Rt)) := by
  refine RepL.of_get rfl fun j hj => ?_
  have hj4 : j < 4 := by simpa [lenK] using hj
  have hjK : j < hsKer.length := by rw [lenK]; exact hj4
  have hu : ∀ c ∈ hsKer, ∀ l ∈ c.u, l < 2 := by decide
  have hc : hsKer.getD j default ∈ hsKer := by
    rw [List.getD_eq_getElem hsKer default hjK]
    exact List.getElem_mem _
  have e : powS 1100 11 (mask 11) I (wordPB 1100 11 (mask 11) R (hsKer.getD j default).u I)
      (hsKer.getD j default).k = Ks.getD j 0 :=
    Nat.eq_of_beq_eq_true (List.all_eq_true.1 kG j (List.mem_range.2 hjK))
  have h1 := rep_word hn' hw' hid (hsKer.getD j default).u fun l hl => rRt l (hu _ hc l hl)
  rw [← wordTabA_foldr] at h1
  have h2 := rep_pow hn' hw' hid h1 (hsKer.getD j default).k
  rw [e] at h2
  have e2 : (hsKer.map (kerGt 1100 Rt))[j]! = kerGt 1100 Rt (hsKer.getD j default) := by
    rw [getElem!_pos _ j hj, List.getElem_map, List.getD_eq_getElem hsKer default hjK]
  rw [e2]
  exact h2

theorem rK' {j : Nat} (hj : j < hsKer.length) : Rep 1100 11 (Ks.getD j 0) (kerGt 1100 Rt hsKer[j]) := by
  have hk := rK.2 j (by rw [lenKs]; rw [lenK] at hj; exact hj)
  rwa [List.getD_eq_getElem _ #[] (by simpa using hj), List.getElem_map] at hk

theorem rKi : RepL 1100 11 Kis (hsKer.map (kerGi 1100 Rt)) := by
  refine RepL.of_get rfl fun j hj => ?_
  have hjK : j < hsKer.length := by simpa using hj
  have e : powS 1100 11 (mask 11) I (Ks.getD j 0) (2 ^ (hsKer.getD j default).e - 1) =
      Kis.getD j 0 := Nat.eq_of_beq_eq_true (List.all_eq_true.1 kI j (List.mem_range.2 hjK))
  have h2 := rep_pow hn' hw' hid (rK' hjK) (2 ^ (hsKer.getD j default).e - 1)
  rw [e, List.getD_eq_getElem hsKer default hjK] at h2
  rw [getElem!_pos _ j hj, List.getElem_map]
  exact h2

theorem y2 : A312HS2K := by
  have hs := sizes2
  simp only [Bool.and_eq_true, beq_iff_eq] at hs
  unfold A312HS2K
  refine ⟨by rw [hL2K_eq, len2], ?_, ?_, ?_, ?_⟩
  · rw [n_eq]
    exact e8_sound hn' hw' hid rV rfl rL2s e8
  · unfold KerOK
    rw [n_eq, hB]
    obtain ⟨hKn, -⟩ := baseEnum_sound rK rKi enumK
    have hB3 : ∀ x ∈ ([0, 1, 2] : List Nat), x < 1100 := by decide
    refine ⟨by rw [hL2K_eq, len2]; decide, fun i hi b hb => ?_, by decide, fun c hc b hb => ?_,
      fun c hc i hi => ?_, hKn, hs.1⟩
    · have hi2 : i < 2 := hi
      have h := List.all_eq_true.1 (List.all_eq_true.1 rOrd i (List.mem_range.2 hi)) b hb
      rw [beq_iff_eq] at h
      have hx : hsQuot2[i]!.m = (hsQuot2.getD i default).m := by
        rw [getElem!_pos hsQuot2 i hi, List.getD_eq_getElem hsQuot2 default hi]
      have hb' : b < 1100 := hB3 b hb
      rw [img_rep (rep_pow hn' hw' hid (rR i hi2) _) hb', hx]
      exact h
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hc
      have h := List.all_eq_true.1 (List.all_eq_true.1 kOrd j (List.mem_range.2 hj)) b hb
      rw [beq_iff_eq] at h
      have hb' : b < 1100 := hB3 b hb
      rw [img_rep (rep_pow hn' hw' hid (rK' hj) _) hb']
      rwa [List.getD_eq_getElem hsKer default hj] at h
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hc
      have hk := rK' hj
      have hv := rV.2 i (by change i < 3; exact hi)
      have hk' : Ks.getD j 0 ∈ Ks := by
        rw [List.getD_eq_getElem Ks 0 (by rw [lenKs]; rw [lenK] at hj; exact hj)]
        exact List.getElem_mem _
      have hv' : Vs.getD i 0 ∈ Vs := by
        rw [List.getD_eq_getElem Vs 0 (by change i < 3; exact hi)]
        exact List.getElem_mem _
      have e : hsVTabsK.toList.getD i #[] = hsVTabsK.getD i #[] := by
        simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
      rw [e] at hv
      exact comp_eq hn' hw' hk hv hv hk (List.all_eq_true.1 (List.all_eq_true.1 kV _ hk') _ hv')
  · rw [HSK.Om_get (j := 2) (by decide), List.all_eq_true]
    intro t ht
    obtain ⟨c, hc, hr⟩ := rW.mem' ht
    exact fix_of hr (all_mem fixW c hc)
  · unfold Z4CubedOK
    rw [n_eq, hB]
    obtain ⟨hWn, -⟩ := baseEnum_sound rW rW3 enumW
    refine ⟨rfl, fun t ht => ?_, fun t ht u hu => ?_, hWn, hs.2⟩
    · obtain ⟨c, hc, hr⟩ := rW.mem' ht
      exact rep_eq (rep_pow hn' hw' hid hr 4) hid (eq_of_beq (all_mem w4 c hc))
    · obtain ⟨c, hc, hr⟩ := rW.mem' ht
      obtain ⟨d, hd, hs'⟩ := rW.mem' hu
      exact comp_eq hn' hw' hr hs' hs' hr (all_mem (all_mem wc c hc) d hd)

end CFSG.KD.HSA312

end
