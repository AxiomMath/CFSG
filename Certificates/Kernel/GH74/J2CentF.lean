module

public import Certificates.Kernel.GH74.J2CentE
public import Certificates.Kernel.Sporadic.OddCore.J2CnF
public import Certificates.Kernel.Sporadic.OddCore.M12SylF

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelGH74.J2CentE

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KS.GH74
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier.Native
open CFSG.GH74.Generic.S45.EvSpor CertificateChecks.KernelGH74
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.J2Cn

theorem getElem!_map_toArray {α β : Type} [Inhabited β] (f : α → β) (L : List α) (d : α) {j : Nat}
    (hj : j < L.length) : (L.map f).toArray[j]! = f (L.getD j d) := by
  rw [getElem!_pos _ j (by simpa using hj), List.getD_eq_getElem _ _ hj]
  simp

theorem memK_iff {cnt : Nat} {T : Nat → Nat} {x : Nat} :
    memK cnt T x = true ↔ ∃ i < cnt, T i = x := by
  induction cnt with
  | zero => simp [memK]
  | succ c ih =>
    change bIf(Nat.beq (T c) x, true, memK c T x) = true ↔ _
    cases e : Nat.beq (T c) x
    · change memK c T x = true ↔ _
      rw [ih]
      constructor
      · rintro ⟨i, hi, h⟩
        exact ⟨i, by omega, h⟩
      · rintro ⟨i, hi, h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact ⟨i, hi, h⟩
        · rw [h, Nat.beq_refl] at e
          exact Bool.noConfusion e
    · exact ⟨fun _ => ⟨c, by omega, Nat.eq_of_beq_eq_true e⟩, fun _ => rfl⟩

theorem memT_hRec {cnt : Nat} {T PL : Nat → Nat} {x : Nat}
    (hT : ∀ i < cnt, canonK 315 9 (mask 9) (315 * 9) (T i) = true)
    (hx : canonK 315 9 (mask 9) (315 * 9) x = true) :
    memT 315 (hRec 315 9 cnt T PL).1 (tabT (unpack 315 9 x)) = memK cnt T x := by
  apply Bool.eq_iff_iff.2
  rw [memK_iff]
  unfold memT
  rw [Array.any_eq_true]
  constructor
  · rintro ⟨i, hi, h⟩
    have hi' : i < cnt := by simpa [hRec] using hi
    have e : (hRec 315 9 cnt T PL).1[i] = tabT (unpack 315 9 (T i)) := by simp [hRec]
    rw [e, tblEq_unpack hx (hT i hi')] at h
    exact ⟨i, hi', (Nat.eq_of_beq_eq_true h).symm⟩
  · rintro ⟨i, hi, h⟩
    have hi' : i < (hRec 315 9 cnt T PL).1.size := by simpa [hRec] using hi
    refine ⟨i, hi', ?_⟩
    have e : (hRec 315 9 cnt T PL).1[i] = tabT (unpack 315 9 (T i)) := by simp [hRec]
    rw [e, h]
    exact tblEq_self hx

theorem memL_iff {L : List Nat} {x : Nat} : memL L x = true ↔ x ∈ L := by
  induction L with
  | nil => simp [memL]
  | cons y L ih =>
    change bIf(Nat.beq y x, true, memL L x) = true ↔ _
    cases e : Nat.beq y x
    · change memL L x = true ↔ _
      rw [ih, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (h | h)
        · rw [h, Nat.beq_refl] at e
          exact Bool.noConfusion e
        · exact h
    · exact ⟨fun _ => List.mem_cons.2 (Or.inl (Nat.eq_of_beq_eq_true e).symm), fun _ => rfl⟩

theorem memT_list {L : List Nat} {x : Nat} (hL : ∀ y ∈ L, canonK 315 9 (mask 9) (315 * 9) y = true)
    (hx : canonK 315 9 (mask 9) (315 * 9) x = true) :
    memT 315 (L.map fun y => tabT (unpack 315 9 y)).toArray (tabT (unpack 315 9 x)) = memL L x := by
  apply Bool.eq_iff_iff.2
  rw [memL_iff]
  unfold memT
  rw [List.any_toArray, List.any_eq_true]
  constructor
  · rintro ⟨t, ht, h⟩
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ht
    rw [tblEq_unpack hx (hL y hy)] at h
    rwa [Nat.eq_of_beq_eq_true h]
  · intro h
    exact ⟨_, List.mem_map.2 ⟨x, h, rfl⟩, tblEq_self hx⟩

theorem bOr_eq (a b : Bool) : bOr a b = (a || b) := by cases a <;> rfl

theorem bIf_not' (b : Bool) : bIf(b, false, true) = !b := by cases b <;> rfl

theorem bIf_true_right' (c t : Bool) : bIf(c, t, true) = (!c || t) := by cases c <;> rfl

theorem cg_size : j2CG.size = 4 := rfl

theorem cg_get {l : Nat} (hl : l < 4) : j2CG[l]! = j2CentTbl (32 + l) := by
  interval_cases l <;> rfl

theorem lt_lo {l : Nat} (hl : l < 4) : lt l = F (32 + l) := by
  unfold lt
  rw [Eq.mpr Nat.blt_eq hl]
  rfl

theorem lt_hi {l : Nat} (hl : 4 ≤ l) : lt l = I (28 + l) := by
  have hb : Nat.blt l 4 = false := by
    cases e : Nat.blt l 4
    · rfl
    · have := Eq.mp Nat.blt_eq e
      omega
  unfold lt
  rw [hb]
  rfl

theorem letter_ok {l : Nat} (hl : l < 8) :
    (if l < j2CG.size then j2CG[l]! else invT 315 j2CG[l - j2CG.size]!) = tabT (unpack 315 9 (lt l)) ∧
      canonK 315 9 (mask 9) (315 * 9) (lt l) = true := by
  rw [cg_size]
  rcases Nat.lt_or_ge l 4 with h | h
  · rw [if_pos h, cg_get h, lt_lo h, tabF (by omega)]
    exact ⟨rfl, Fc (by omega)⟩
  · rw [if_neg (by omega), cg_get (by omega), lt_hi h, invF (by omega),
      show 32 + (l - 4) = 28 + l by omega]
    exact ⟨rfl, Ic (by omega)⟩

theorem word_tab {w : List Nat} (hw : ∀ l ∈ w, l < 8) :
    evalWord 315 j2CG w = tabT (unpack 315 9 (wK w)) ∧
      canonK 315 9 (mask 9) (315 * 9) (wK w) = true := by
  unfold evalWord wK
  rw [hid]
  exact KernelSpor.M12Syl.evalWord_foldl w _ hidc fun l hl => letter_ok (hw l hl)

theorem gens : (∀ j < 4, J2E.GI j = wK (j2EWords.getD j []) ∧ J2E.G j = pidn 315 9 ∧
      cK (J2EI j) = true ∧ iK (J2E.GI j) (J2EI j) = true) ∧
    (J2O1.GI 0 = tK ∧ J2O2.GI 0 = tK) ∧
    (∀ k < 10, cK (J2O1C k) = true ∧ iK (wK (j2Orb1Conj.getD k [])) (J2O1C k) = true ∧
      J2O1.GI (k + 1) = cjK (wK (j2Orb1Conj.getD k [])) (J2O1C k) (wK j2Orb1Root)) ∧
    (∀ k < 20, cK (J2O2C k) = true ∧ iK (wK (j2Orb2Conj.getD k [])) (J2O2C k) = true ∧
      J2O2.GI (k + 1) = cjK (wK (j2Orb2Conj.getD k [])) (J2O2C k) (wK j2Orb2Root)) ∧
    (∀ j < 11, J2O1.G j = pidn 315 9 ∧ cK (J2O1I j) = true ∧ iK (J2O1.GI j) (J2O1I j) = true) ∧
    (∀ j < 21, J2O2.G j = pidn 315 9 ∧ cK (J2O2I j) = true ∧ iK (J2O2.GI j) (J2O2I j) = true) ∧
    (∀ k < 3, cK (J2PFW (2 * k)) = true ∧ cK (J2PFW (2 * k + 1)) = true ∧
      iK (wK (j2PerfPairs.getD k ([], [])).1) (J2PFW (2 * k)) = true ∧
      iK (wK (j2PerfPairs.getD k ([], [])).2) (J2PFW (2 * k + 1)) = true ∧
      J2PF.GI k = cmK (wK (j2PerfPairs.getD k ([], [])).1) (wK (j2PerfPairs.getD k ([], [])).2)
        (J2PFW (2 * k)) (J2PFW (2 * k + 1))) ∧
    (∀ j < 3, J2PF.G j = pidn 315 9 ∧ cK (J2PFI j) = true ∧ iK (J2PF.GI j) (J2PFI j) = true) ∧
    (∀ j < 6, J2S1.GI j = nIf(Nat.blt j 4, J2E.GI j, F (Nat.add 28 j)) ∧ J2S1.G j = pidn 315 9 ∧
      cK (J2S1I j) = true ∧ iK (J2S1.GI j) (J2S1I j) = true) ∧
    (∀ j < 6, J2S2.GI j = cjK (F 35) (I 35) (J2S1.GI j) ∧ J2S2.G j = pidn 315 9 ∧
      cK (J2S2I j) = true ∧ iK (J2S2.GI j) (J2S2I j) = true) := by
  have h := gens_ok
  simp only [bAnd_iff] at h
  obtain ⟨a1, ⟨a2, a3⟩, a4, a5, a6, a7, a8, a9, a10, a11⟩ := h
  refine ⟨fun j hj => ?_, ⟨Nat.eq_of_beq_eq_true a2, Nat.eq_of_beq_eq_true a3⟩, fun k hk => ?_,
    fun k hk => ?_, fun j hj => ?_, fun j hj => ?_, fun k hk => ?_, fun j hj => ?_, fun j hj => ?_,
    fun j hj => ?_⟩
  · have := allN_spec a1 j hj
    simp only [bAnd_iff] at this
    exact ⟨Nat.eq_of_beq_eq_true this.1, Nat.eq_of_beq_eq_true this.2.1, this.2.2.1, this.2.2.2⟩
  · have := allN_spec a4 k hk
    simp only [bAnd_iff] at this
    exact ⟨this.1, this.2.1, Nat.eq_of_beq_eq_true this.2.2⟩
  · have := allN_spec a5 k hk
    simp only [bAnd_iff] at this
    exact ⟨this.1, this.2.1, Nat.eq_of_beq_eq_true this.2.2⟩
  · have := allN_spec a6 j hj
    simp only [bAnd_iff] at this
    exact ⟨Nat.eq_of_beq_eq_true this.1, this.2.1, this.2.2⟩
  · have := allN_spec a7 j hj
    simp only [bAnd_iff] at this
    exact ⟨Nat.eq_of_beq_eq_true this.1, this.2.1, this.2.2⟩
  · have := allN_spec a8 k hk
    simp only [bAnd_iff] at this
    exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1, Nat.eq_of_beq_eq_true this.2.2.2.2⟩
  · have := allN_spec a9 j hj
    simp only [bAnd_iff] at this
    exact ⟨Nat.eq_of_beq_eq_true this.1, this.2.1, this.2.2⟩
  · have := allN_spec a10 j hj
    simp only [bAnd_iff] at this
    exact ⟨Nat.eq_of_beq_eq_true this.1, Nat.eq_of_beq_eq_true this.2.1, this.2.2.1, this.2.2.2⟩
  · have := allN_spec a11 j hj
    simp only [bAnd_iff] at this
    exact ⟨Nat.eq_of_beq_eq_true this.1, Nat.eq_of_beq_eq_true this.2.1, this.2.2.1, this.2.2.2⟩

theorem sizes : J2E.cnt = 32 ∧ J2O1.cnt = 32 ∧ J2O2.cnt = 32 ∧ J2PF.cnt = 1920 ∧ J2S1.cnt = 128 ∧
    J2S2.cnt = 128 ∧ penumHdK idK J2E.cnt 3000 J2E.T J2E.PL = true ∧
    penumHdK idK J2O1.cnt 3000 J2O1.T J2O1.PL = true ∧ penumHdK idK J2O2.cnt 3000 J2O2.T J2O2.PL = true ∧
    penumHdK idK J2PF.cnt 3000 J2PF.T J2PF.PL = true ∧ penumHdK idK J2S1.cnt 3000 J2S1.T J2S1.PL = true ∧
    penumHdK idK J2S2.cnt 3000 J2S2.T J2S2.PL = true := by
  have h := sizes_ok
  simp only [bAnd_iff] at h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := h
  exact ⟨Nat.eq_of_beq_eq_true a1, Nat.eq_of_beq_eq_true a2, Nat.eq_of_beq_eq_true a3,
    Nat.eq_of_beq_eq_true a4, Nat.eq_of_beq_eq_true a5, Nat.eq_of_beq_eq_true a6, a7, a8, a9, a10,
    a11, a12⟩

theorem words_e : ∀ w ∈ j2EWords, ∀ l ∈ w, l < 8 := by decide
theorem words_o1 : (∀ w ∈ j2Orb1Conj, ∀ l ∈ w, l < 8) ∧ ∀ l ∈ j2Orb1Root, l < 8 := by decide
theorem words_o2 : (∀ w ∈ j2Orb2Conj, ∀ l ∈ w, l < 8) ∧ ∀ l ∈ j2Orb2Root, l < 8 := by decide
theorem words_pf : ∀ p ∈ j2PerfPairs, (∀ l ∈ p.1, l < 8) ∧ ∀ l ∈ p.2, l < 8 := by decide

theorem getD_mem {α : Type} {L : List α} {d : α} {j : Nat} (hj : j < L.length) : L.getD j d ∈ L := by
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

theorem eW {j : Nat} (hj : j < 4) : ∀ l ∈ j2EWords.getD j [], l < 8 :=
  words_e _ (getD_mem (by change j < 4; exact hj))

theorem eg_canon {j : Nat} (hj : j < 4) : canonK 315 9 (mask 9) (315 * 9) (J2E.GI j) = true := by
  rw [(gens.1 j hj).1]
  exact (word_tab (eW hj)).2

theorem e_tabs : TabsOK 315 9 4 J2E.GI j2EGens.toArray := by
  refine ⟨rfl, fun j hj => ⟨?_, eg_canon hj⟩⟩
  unfold j2EGens
  rw [getElem!_map_toArray _ _ [] (by change j < 4; exact hj), (gens.1 j hj).1]
  exact (word_tab (eW hj)).1

theorem tK_canon : canonK 315 9 (mask 9) (315 * 9) tK = true := Fc (by norm_num)

theorem tA_tab : j2TA = tabT (unpack 315 9 tK) := tabF (by norm_num : 31 < 42)

end CertificateChecks.KernelGH74.J2CentE

end
