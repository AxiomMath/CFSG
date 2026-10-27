module

public import Certificates.Kernel.GH74.J2CentF

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelGH74.J2CentE

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KS.GH74
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier.Native
open CFSG.GH74.Generic.S45.EvSpor CertificateChecks.KernelGH74
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.J2Cn

theorem conj_word {w r : List Nat} {ci : Nat} (hw : ∀ l ∈ w, l < 8) (hr : ∀ l ∈ r, l < 8)
    (hci : cK ci = true) (hi : iK (wK w) ci = true) :
    conjT 315 (evalWord 315 j2CG w) (invT 315 (evalWord 315 j2CG w)) (evalWord 315 j2CG r) =
      tabT (unpack 315 9 (cjK (wK w) ci (wK r))) ∧
      canonK 315 9 (mask 9) (315 * 9) (cjK (wK w) ci (wK r)) = true := by
  obtain ⟨tw, cw⟩ := word_tab hw
  obtain ⟨tr, cr⟩ := word_tab hr
  rw [tw, tr, invT_unpack (by norm_num) hi, conjT_unpack cw hci cr]
  exact ⟨rfl, CFSG.KC.BfsPin.canonK_pcomp (CFSG.KC.BfsPin.canonK_pcomp cw cr) hci⟩

theorem orb_tabs {L : List (List Nat)} {r : List Nat} {m : Nat} {GI C : Nat → Nat}
    (hL : L.length = m) (hw : ∀ w ∈ L, ∀ l ∈ w, l < 8) (hr : ∀ l ∈ r, l < 8) (h0 : GI 0 = tK)
    (hk : ∀ k < m, cK (C k) = true ∧ iK (wK (L.getD k [])) (C k) = true ∧
      GI (k + 1) = cjK (wK (L.getD k [])) (C k) (wK r)) :
    TabsOK 315 9 (m + 1) GI (j2TA :: conjOrbit r L).toArray := by
  refine ⟨by simp [conjOrbit, hL], fun j hj => ?_⟩
  rcases j with _ | k
  · rw [h0]
    exact ⟨by rw [← tA_tab]; rfl, tK_canon⟩
  · have hk' : k < m := by omega
    obtain ⟨c1, c2, c3⟩ := hk k hk'
    have hkL : k < L.length := by omega
    have e : (j2TA :: conjOrbit r L).toArray[k + 1]! = (conjOrbit r L).toArray[k]! := by
      rw [getElem!_pos _ (k + 1) (by simp [conjOrbit]; omega),
        getElem!_pos _ k (by simp [conjOrbit]; omega)]
      simp
    rw [e]
    unfold conjOrbit
    rw [getElem!_map_toArray _ _ [] hkL, c3]
    exact conj_word (hw _ (getD_mem hkL)) hr c1 c2

theorem o1_tabs : TabsOK 315 9 11 J2O1.GI (j2TA :: conjOrbit j2Orb1Root j2Orb1Conj).toArray :=
  orb_tabs (m := 10) rfl words_o1.1 words_o1.2 gens.2.1.1 gens.2.2.1

theorem o2_tabs : TabsOK 315 9 21 J2O2.GI (j2TA :: conjOrbit j2Orb2Root j2Orb2Conj).toArray :=
  orb_tabs (m := 20) rfl words_o2.1 words_o2.2 gens.2.1.2 gens.2.2.2.1

theorem pf_tabs : TabsOK 315 9 3 J2PF.GI j2PerfComm.toArray := by
  refine ⟨rfl, fun k hk => ?_⟩
  obtain ⟨c1, c2, c3, c4, c5⟩ := gens.2.2.2.2.2.2.1 k hk
  have hkL : k < j2PerfPairs.length := by change k < 3; exact hk
  have hp := words_pf _ (getD_mem (d := ([], [])) hkL)
  obtain ⟨ta, ca⟩ := word_tab hp.1
  obtain ⟨tb, cb⟩ := word_tab hp.2
  have ecm : cmK (wK (j2PerfPairs.getD k ([], [])).1) (wK (j2PerfPairs.getD k ([], [])).2)
      (J2PFW (2 * k)) (J2PFW (2 * k + 1)) = pcomp 315 9 (mask 9)
        (pcomp 315 9 (mask 9) (wK (j2PerfPairs.getD k ([], [])).1) (wK (j2PerfPairs.getD k ([], [])).2))
        (pcomp 315 9 (mask 9) (J2PFW (2 * k)) (J2PFW (2 * k + 1))) := rfl
  unfold j2PerfComm
  rw [getElem!_map_toArray _ _ ([], []) hkL, c5, ecm]
  unfold commutatorT
  rw [ta, tb, invT_unpack (by norm_num) c3, invT_unpack (by norm_num) c4, compT_unpack ca cb,
    compT_unpack c1 c2, compT_unpack (CFSG.KC.BfsPin.canonK_pcomp ca cb)
      (CFSG.KC.BfsPin.canonK_pcomp c1 c2)]
  exact ⟨rfl, CFSG.KC.BfsPin.canonK_pcomp (CFSG.KC.BfsPin.canonK_pcomp ca cb)
    (CFSG.KC.BfsPin.canonK_pcomp c1 c2)⟩

theorem s1_tabs : TabsOK 315 9 6 J2S1.GI j2S1Gens.toArray := by
  refine ⟨rfl, fun j hj => ?_⟩
  rw [(gens.2.2.2.2.2.2.2.2.1 j hj).1]
  rcases Nat.lt_or_ge j 4 with h | h
  · have e : j2S1Gens.toArray[j]! = j2EGens.toArray[j]! := by
      rw [getElem!_pos _ j (by simp [j2S1Gens, j2EGens, j2EWords]; omega),
        getElem!_pos _ j (by simp [j2EGens, j2EWords]; omega)]
      simp [j2S1Gens, List.getElem_append_left (by simp [j2EGens, j2EWords]; omega : j < j2EGens.length)]
    rw [e, show nIf(Nat.blt j 4, J2E.GI j, F (Nat.add 28 j)) = J2E.GI j by
      rw [Eq.mpr Nat.blt_eq h]]
    exact e_tabs.2 j h
  · have hb : Nat.blt j 4 = false := by
      cases e : Nat.blt j 4
      · rfl
      · have := Eq.mp Nat.blt_eq e
        omega
    rw [show nIf(Nat.blt j 4, J2E.GI j, F (Nat.add 28 j)) = F (28 + j) by rw [hb]; rfl]
    refine ⟨?_, Fc (by omega)⟩
    rw [← tabF (by omega)]
    obtain rfl | rfl : j = 4 ∨ j = 5 := by omega
    · rfl
    · rfl

theorem s1c {j : Nat} (hj : j < 6) : canonK 315 9 (mask 9) (315 * 9) (J2S1.GI j) = true :=
  (s1_tabs.2 j hj).2

private theorem toArray_map_getElem! {α β : Type} [Inhabited α] [Inhabited β] (f : α → β)
    (L : List α) {j : Nat} (hj : j < L.length) : (L.map f).toArray[j]! = f L.toArray[j]! := by
  rw [getElem!_pos _ j (by simpa using hj), getElem!_pos _ j (by simpa using hj)]
  simp

theorem s2_tabs : TabsOK 315 9 6 J2S2.GI j2S2Gens.toArray := by
  refine ⟨rfl, fun j hj => ⟨?_, ?_⟩⟩
  · rw [(gens.2.2.2.2.2.2.2.2.2 j hj).1]
    unfold j2S2Gens
    have hl : j < j2S1Gens.length := by change j < 6; exact hj
    rw [toArray_map_getElem! _ _ hl, (s1_tabs.2 j hj).1, cg_get (by norm_num : 3 < 4),
      tabF (by norm_num : 32 + 3 < 42),
      invT_unpack (by norm_num) (Finv (by norm_num : 32 + 3 < 42)),
      conjT_unpack (Fc (by norm_num)) (Ic (by norm_num)) (s1c hj)]
    rfl
  · rw [(gens.2.2.2.2.2.2.2.2.2 j hj).1]
    exact CFSG.KC.BfsPin.canonK_pcomp (CFSG.KC.BfsPin.canonK_pcomp (Fc (by norm_num)) (s1c hj))
      (Ic (by norm_num))

end CertificateChecks.KernelGH74.J2CentE

end
