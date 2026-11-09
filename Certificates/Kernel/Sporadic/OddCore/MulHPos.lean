module

public import Certificates.Kernel.Sporadic.OddCore.MulHGlue
public import CFSG.Certificates.Kernel.Spor.PcompFacts

public section

namespace CFSG.KS.MulH

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.BfsPin
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native

theorem pg_pg_invEqK {n w g gi : Nat} (h : invEqK n w (mask w) (n * w) g gi = true) :
    ∀ x < n, pg w (mask w) g (pg w (mask w) gi x) = x := by
  unfold invEqK CFSG.KC.Enum.permOK at h
  simp only [bAnd_iff] at h
  obtain ⟨-, -, ha⟩ := h
  have hpr : ∀ i < n, pg w (mask w) g i < n ∧ pg w (mask w) gi (pg w (mask w) g i) = i := by
    intro i hi
    have := allN_spec ha i hi
    rw [CFSG.KS.PF.strictB_eqP] at this
    simp only [bAnd_iff] at this
    exact ⟨by simpa [Nat.blt_eq] using this.1, Nat.eq_of_beq_eq_true this.2⟩
  have hsurj := Finset.surj_on_of_inj_on_of_card_le (s := Finset.range n) (t := Finset.range n)
    (fun a _ => pg w (mask w) g a) (fun a ha => by simpa using (hpr a (by simpa using ha)).1)
    (fun a₁ a₂ h₁ h₂ e => by
      have e1 := (hpr a₁ (by simpa using h₁)).2
      have e2 := (hpr a₂ (by simpa using h₂)).2
      have e' : pg w (mask w) g a₁ = pg w (mask w) g a₂ := e
      rw [e'] at e1
      omega) le_rfl
  intro x hx
  obtain ⟨i, hi, e⟩ := hsurj x (by simpa using hx)
  rw [e, (hpr i (by simpa using hi)).2]

theorem pcomp_pcomp_invEqK {n w t g gi : Nat} (ht : canonK n w (mask w) (n * w) t = true)
    (hgi : canonK n w (mask w) (n * w) gi = true) (h : invEqK n w (mask w) (n * w) g gi = true) :
    pcomp n w (mask w) (pcomp n w (mask w) t g) gi = t := by
  obtain ⟨hn, hw, ht0, -⟩ := CFSG.KS.PF.canon_facts ht
  obtain ⟨-, -, -, hgr⟩ := CFSG.KS.PF.canon_facts hgi
  have hn32 : n < 2 ^ 32 := by omega
  have hw0 := CFSG.KS.PF.w_pos hw
  refine CFSG.KS.PF.eq_of_fields hw0 (CFSG.KS.PF.pcomp_shr _ _ hn32 hw0) ht0 fun x hx => ?_
  rw [CFSG.KS.PF.pg_pcomp hn32 hx, CFSG.KS.PF.pg_pcomp hn32 (hgr x hx), pg_pg_invEqK h x hx]

theorem pidn_pcomp_canon {n w t : Nat} (ht : canonK n w (mask w) (n * w) t = true) :
    pcomp n w (mask w) (pidn n w) t = t := by
  obtain ⟨hn, hw, ht0, htr⟩ := CFSG.KS.PF.canon_facts ht
  have hn32 : n < 2 ^ 32 := by omega
  have hw0 := CFSG.KS.PF.w_pos hw
  refine CFSG.KS.PF.eq_of_fields hw0 (CFSG.KS.PF.pcomp_shr _ _ hn32 hw0) ht0 fun i hi => ?_
  rw [CFSG.KS.PF.pg_pcomp hn32 hi, CFSG.KS.PF.pg_pidn hn hw (htr i hi)]

theorem exists_pcomp_invEqK {n w cnt g gi : Nat} {T P : Nat → Nat}
    (hT : ∀ i < cnt, canonK n w (mask w) (n * w) (T i) = true)
    (hd : ∀ a < cnt, ∀ b < cnt, T a = T b → a = b)
    (hgi : canonK n w (mask w) (n * w) gi = true) (h : invEqK n w (mask w) (n * w) g gi = true)
    (hP : ∀ i < cnt, P i < cnt ∧ T (P i) = pcomp n w (mask w) (T i) g) :
    ∀ b < cnt, ∃ a < cnt, T a = pcomp n w (mask w) (T b) gi := by
  have hsurj := Finset.surj_on_of_inj_on_of_card_le (s := Finset.range cnt) (t := Finset.range cnt)
    (fun a _ => P a) (fun a ha => by simpa using (hP a (by simpa using ha)).1)
    (fun a₁ a₂ h₁ h₂ e => by
      have h₁' : a₁ < cnt := by simpa using h₁
      have h₂' : a₂ < cnt := by simpa using h₂
      have e' : P a₁ = P a₂ := e
      have hq := congrArg (fun x => pcomp n w (mask w) (T x) gi) e'
      simp only [(hP a₁ h₁').2, (hP a₂ h₂').2, pcomp_pcomp_invEqK (hT a₁ h₁') hgi h,
        pcomp_pcomp_invEqK (hT a₂ h₂') hgi h] at hq
      exact hd a₁ h₁' a₂ h₂' hq) le_rfl
  intro b hb
  obtain ⟨a, ha, e⟩ := hsurj b (by simpa using hb)
  have ha' : a < cnt := by simpa using ha
  refine ⟨a, ha', ?_⟩
  have e' : b = P a := e
  rw [e', (hP a ha').2, pcomp_pcomp_invEqK (hT a ha') hgi h]

theorem closedOK_of_ex {n w cnt K : Nat} {T PL S : Nat → Nat} {gs : Array Table}
    (hT : ∀ i < cnt, canonK n w (mask w) (n * w) (T i) = true) (hgs : TabsOK n w K S gs)
    (hf : ∀ i < cnt, ∀ j < K, ∃ q < cnt, T q = pcomp n w (mask w) (T i) (S j)) :
    closedOK n gs (hRec n w cnt T PL).1 = true := by
  unfold closedOK
  rw [Array.all_eq_true]
  intro i hi
  have hi' : i < cnt := by simpa [hRec] using hi
  rw [Array.all_eq_true]
  intro j hj
  have hj' : j < K := by rw [← hgs.1]; exact hj
  obtain ⟨hgj, hcj⟩ := hgs.2 j hj'
  obtain ⟨q, hq, he⟩ := hf i hi' j hj'
  have hx : (hRec n w cnt T PL).1[i] = tabT (unpack n w (T i)) := by simp [hRec]
  rw [hx, ← getElem!_pos gs j hj, hgj, compT_unpack (hT i hi') hcj, ← he]
  exact memT_of hq (tblEq_self (hT _ hq))

theorem enumOK_of_pos {n w k cnt cap m : Nat} {G GI GJ T PL POS SRT SRI HS HSI : Nat → Nat}
    {gs : List Table} (hn : szOK n w = true) (hG : ∀ j < k, G j = pidn n w)
    (hg : TabsOK n w k GI gs.toArray)
    (hgj : ∀ j < k, invEqK n w (mask w) (n * w) (GI j) (GJ j) = true ∧
      canonK n w (mask w) (n * w) (GJ j) = true)
    (hh : penumHdK (pidn n w) cnt cap T PL = true)
    (hp : ∀ i < cnt, penumPtK n w (mask w) (n * w) true G GI k cnt T PL POS SRT SRI i = true)
    (hs : ∀ i < cnt, hsortPtK n w (mask w) cnt T HS HSI i = true)
    (hm : cnt = m) : CFSG.Sporadic.SmallOddCore.enumOK n cap m gs = true := by
  obtain ⟨e, ht, hd⟩ := mulH_sound hn hG hg hh hp hs
  have hT : ∀ i < cnt, canonK n w (mask w) (n * w) (T i) = true :=
    fun i hi => penumPt_canon (hp i hi)
  have hfw : ∀ j < k, ∀ i < cnt, r32 POS (i * k + j) < cnt ∧
      T (r32 POS (i * k + j)) = pcomp n w (mask w) (T i) (GI j) := by
    intro j hj i hi
    obtain ⟨h1, h2, -⟩ := (penumPt_specH (hp i hi)).2.2.1 j hj
    refine ⟨h1, ?_⟩
    rw [h2]
    change pcomp n w (mask w) (pcomp n w (mask w) (G j) (T i)) (GI j) = _
    rw [hG j hj, pidn_pcomp_canon (hT i hi)]
  have hdist : ∀ a < cnt, ∀ b < cnt, T a = T b → a = b :=
    inj_of_sortH fun i hi => (penumPt_specH (hp i hi)).2.2.2
  have hcl : ∀ i < cnt, ∀ j < k + k, ∃ q < cnt,
      T q = pcomp n w (mask w) (T i) (bothK k GI GJ j) := by
    intro i hi j hj
    by_cases h : j < k
    · rw [bothK_lt h]
      exact ⟨_, (hfw j h i hi).1, (hfw j h i hi).2⟩
    · have hjk : j - k < k := by omega
      rw [bothK_ge (by omega)]
      exact exists_pcomp_invEqK (P := fun i => r32 POS (i * k + (j - k))) hT hdist (hgj _ hjk).2
        (hgj _ hjk).1 (hfw _ hjk) i hi
  unfold CFSG.Sporadic.SmallOddCore.enumOK
  simp only [Bool.and_eq_true]
  rw [e]
  refine ⟨⟨⟨⟨?_, ht⟩, closedOK_of_ex hT (TabsOK_both hg hgj) hcl⟩, hd⟩, ?_⟩
  · rw [List.all_eq_true]
    intro g hgm
    obtain ⟨j, hj, rfl, hc⟩ := TabsOK_list hg hgm
    rw [invT_unpack (lt_of_canonK (hgj j hj).2) (hgj j hj).1]
    exact invOK_unpack hc (hgj j hj).2 (hgj j hj).1
  · rw [hRec_size, hm]
    exact beq_self_eq_true m

end CFSG.KS.MulH

end
