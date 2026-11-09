module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.Fi24Seven.Text
public import Certificates.Data.Kernel.Spor.SlpPlan
public import CFSG.Certificates.Kernel.Spor.Fi24SlpSound
public import CFSG.Certificates.Kernel.Spor.SlpTextSound

public section

set_option maxRecDepth 400000

namespace CFSG.KD.F24S

open CFSG.KC.SlpM CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K

theorem len7 : Nat.beq (lenL W7) 1087 = true := by quickRfl

theorem lenE7 : Nat.beq (lenL E7) 119 = true := by quickRfl

theorem lenEK : Nat.beq (lenL EK) 2733 = true := by quickRfl

theorem lenC7 : Nat.beq (lenL C7) 343 = true := by quickRfl

@[expose] noncomputable def pureDataC (p : PureSec) : Bool :=
  secC (WL 2) (pureGens p.lam) p.lo p.hi && secC (WL 2) [p.ix, p.iy] p.hi p.hi2 &&
    decide (p.lo ≤ p.ix) && decide (p.ix < p.hi) && decide (p.lo ≤ p.iy) && decide (p.iy < p.hi) &&
    decide (p.hi ≤ p.oX) && decide (p.oX < p.hi2) && decide (p.hi ≤ p.oY) &&
    decide (p.oY < p.hi2) && decide (p.hi ≤ p.oh) && decide (p.oh < p.hi2) && decide (p.hi2 ≤ 3820)

@[expose] noncomputable def mixedDataC (m : MixedSec) : Bool :=
  secC (WL 2) m.gs m.lo m.hi && decide (m.lo ≤ m.ia) && decide (m.ia < m.hi) &&
    decide (m.lo ≤ m.ib) && decide (m.ib < m.hi) && decide (m.hi ≤ 3820)

open CFSG.KC.Ord in
@[expose] noncomputable def secTest (gs : List Nat) (lo i : Nat) (c : Nat) : Bool :=
  (fun a => andB (Nat.ble (nat_lit 3) a) (orB (memN (Nat.sub a (nat_lit 3)) gs)
      (andB (Nat.ble lo (Nat.sub a (nat_lit 3))) (Nat.blt (Nat.sub a (nat_lit 3)) i))))
    (Nat.shiftRight c (nat_lit 1))

open CFSG.KC.Ord in
@[expose] noncomputable def secOne (gs : List Nat) (lo hi : Nat) (W : List (List Nat)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun w _ ih j => andB (orB (Nat.blt j lo) (orB (Nat.ble hi j) (allL w (secTest gs lo j))))
      (ih (Nat.succ j))) W

open CFSG.KC.Ord in
theorem secAndB {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

open CFSG.KC.Ord in
theorem secOrB {a b : Bool} (h : orB a b = true) : a = true ∨ b = true := by
  cases a <;> cases b <;> simp_all [orB]

theorem secAllLt {n : Nat} {f : Nat → Bool} (h : ∀ k < n, f k = true) : allLt n f = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change CFSG.KC.Ord.andB (allLt n f) (f n) = true
    rw [ih (fun k hk => h k (by omega)), h n (by omega)]
    rfl

theorem secAllLI {α : Type} {f : α → Bool} : ∀ {l : List α}, (∀ a ∈ l, f a = true) →
    allL l f = true
  | [], _ => rfl
  | a :: l, h => by
    change CFSG.KC.Ord.andB (f a) (allL l f) = true
    rw [h a List.mem_cons_self, secAllLI (fun b hb => h b (List.mem_cons_of_mem a hb))]
    rfl

theorem secAllLE {α : Type} {f : α → Bool} : ∀ {l : List α}, allL l f = true → ∀ a ∈ l, f a = true
  | [], _, _, ha => absurd ha List.not_mem_nil
  | b :: l, h, a, ha => by
    obtain ⟨h1, h2⟩ := secAndB h
    rcases List.mem_cons.1 ha with rfl | ha
    · exact h1
    · exact secAllLE h2 a ha

theorem secOne_spec (gs : List Nat) (lo hi : Nat) : ∀ (W : List (List Nat)) (j : Nat),
    secOne gs lo hi W j = true → ∀ k, lo ≤ j + k → j + k < hi →
      allL (nthW W k) (secTest gs lo (j + k)) = true
  | [], _, _, _, _, _ => rfl
  | w :: W, j, h, k, h1, h2 => by
    obtain ⟨hg, hr⟩ := secAndB h
    cases k with
    | zero =>
      change allL w (secTest gs lo (j + 0)) = true
      rw [Nat.add_zero] at h1 h2 ⊢
      rcases secOrB hg with e | e
      · rw [Nat.blt_eq] at e; omega
      rcases secOrB e with e | e
      · rw [Nat.ble_eq] at e; omega
      exact e
    | succ k =>
      change allL (nthW W k) _ = true
      have := secOne_spec gs lo hi W (Nat.succ j) hr k (by omega) (by omega)
      rwa [show Nat.succ j + k = j + (k + 1) by omega] at this

theorem secC_of_secOne {W : List (List Nat)} {gs : List Nat} {lo hi : Nat}
    (h : secOne gs lo hi W 0 = true) : secC W gs lo hi = true := by
  unfold secC
  refine secAllLt fun r hr => ?_
  change r < hi - lo at hr
  have := secOne_spec gs lo hi W 0 h (lo + r) (by omega) (by omega)
  rw [Nat.zero_add] at this
  exact this

@[expose] noncomputable def pureDataQ (p : PureSec) : Bool :=
  secOne (pureGens p.lam) p.lo p.hi (WL 2) 0 && secOne [p.ix, p.iy] p.hi p.hi2 (WL 2) 0 &&
    decide (p.lo ≤ p.ix) && decide (p.ix < p.hi) && decide (p.lo ≤ p.iy) && decide (p.iy < p.hi) &&
    decide (p.hi ≤ p.oX) && decide (p.oX < p.hi2) && decide (p.hi ≤ p.oY) &&
    decide (p.oY < p.hi2) && decide (p.hi ≤ p.oh) && decide (p.oh < p.hi2) && decide (p.hi2 ≤ 3820)

@[expose] noncomputable def mixedDataQ (m : MixedSec) : Bool :=
  secOne m.gs m.lo m.hi (WL 2) 0 && decide (m.lo ≤ m.ia) && decide (m.ia < m.hi) &&
    decide (m.lo ≤ m.ib) && decide (m.ib < m.hi) && decide (m.hi ≤ 3820)

theorem pureDataQ_ok : allL pureSecs pureDataQ = true := by quickRfl

theorem mixedDataQ_ok : allL mixedSecs mixedDataQ = true := by quickRfl

theorem pureDataC_of {p : PureSec} (h : pureDataQ p = true) : pureDataC p = true := by
  unfold pureDataQ at h
  unfold pureDataC
  cases h1 : secOne (pureGens p.lam) p.lo p.hi (WL 2) 0 <;>
    cases h2 : secOne [p.ix, p.iy] p.hi p.hi2 (WL 2) 0
  · rw [h1] at h; simp at h
  · rw [h1] at h; simp at h
  · rw [h1, h2] at h; simp at h
  · rw [secC_of_secOne h1, secC_of_secOne h2]
    rw [h1, h2] at h
    exact h

theorem mixedDataC_of {m : MixedSec} (h : mixedDataQ m = true) : mixedDataC m = true := by
  unfold mixedDataQ at h
  unfold mixedDataC
  cases h1 : secOne m.gs m.lo m.hi (WL 2) 0
  · rw [h1] at h; simp at h
  · rw [secC_of_secOne h1]
    rw [h1] at h
    exact h

theorem pureDataC_ok : allL pureSecs pureDataC = true :=
  secAllLI fun p hp => pureDataC_of (secAllLE pureDataQ_ok p hp)

theorem mixedDataC_ok : allL mixedSecs mixedDataC = true :=
  secAllLI fun m hm => mixedDataC_of (secAllLE mixedDataQ_ok m hm)

end CFSG.KD.F24S

namespace CertificateChecks.KernelF24S

open CFSG.KC.SlpM CFSG.KD.F24S CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24SevenNative
  CFSG.HardMathSupport.Dickson.I271.Fi7 CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K

theorem w7_len : W7.length = 1087 := by
  have := Nat.eq_of_beq_eq_true len7
  rwa [lenL_eq] at this

theorem e7_len : E7.length = 119 := by
  have := Nat.eq_of_beq_eq_true lenE7
  rwa [lenL_eq] at this

theorem ek_len : EK.length = 2733 := by
  have := Nat.eq_of_beq_eq_true lenEK
  rwa [lenL_eq] at this

theorem c7_len : C7.length = 343 := by
  have := Nat.eq_of_beq_eq_true lenC7
  rwa [lenL_eq] at this

theorem words_eq : fi24SevenData.words = (W7.map decW).toArray := by
  change parseIntLists words7 = _
  rw [words7_txt]
  exact parseIntLists_wordsC (List.ne_nil_of_length_pos (by rw [w7_len]; omega))

theorem conj_eq : fi24SevenData.conj = C7.toArray := by
  change parsePairs conj7 = _
  rw [conj7_txt]
  exact parsePairs_pairsC (List.ne_nil_of_length_pos (by rw [c7_len]; omega))

theorem extra7_eq : fi7Extra () = (E7.map decW).toArray := by
  change parseIntLists fi7ExtraStr = _
  rw [fi7Extra_txt]
  exact parseIntLists_wordsC (List.ne_nil_of_length_pos (by rw [e7_len]; omega))

theorem extraK_eq : CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K.fi24kExtra () = (EK.map decW).toArray := by
  change parseIntLists CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K.fi24kExtraStr = _
  rw [fi24kExtra_txt]
  exact parseIntLists_wordsC (List.ne_nil_of_length_pos (by rw [ek_len]; omega))

theorem layer_words (E : List (List Nat)) :
    (W7.map decW).toArray ++ (E.map decW).toArray = ((appL W7 E).map decW).toArray := by
  rw [appL_eq, List.map_append, List.append_toArray]

theorem nthW_eq (W : List (List Nat)) (j : Nat) : nthW W j = W.getD j [] := by
  induction W generalizing j with
  | nil => rfl
  | cons w W ih =>
    cases j with
    | zero => rfl
    | succ j => change nthW W j = _; rw [ih]; rfl

theorem decW_get (W : List (List Nat)) (i : Nat) : (W.map decW).toArray[i]! = decW (nthW W i) := by
  rw [nthW_eq]
  by_cases h : i < W.length
  · rw [getElem!_pos _ i (by simpa using h), List.getElem_toArray, List.getElem_map,
      List.getD_eq_getElem _ _ h]
  · rw [getElem!_neg _ i (by simpa using h), List.getD_eq_default _ _ (by omega)]
    rfl

theorem memN_spec {n : Nat} : ∀ {l : List Nat}, memN n l = true → n ∈ l
  | [], h => by simp [memN] at h
  | m :: l, h => by
    rcases (orB_iff _ _).1 h with h1 | h1
    · rw [Nat.eq_of_beq_eq_true h1]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (memN_spec h1)

theorem secOK_of_secC {W : List (List Nat)} {gs : List Nat} {lo hi : Nat}
    (h : secC W gs lo hi = true) : secOK (W.map decW).toArray gs lo hi = true := by
  unfold secOK
  rw [List.all_eq_true]
  intro r hr
  rw [List.mem_range] at hr
  have h1 := allL_spec (allLt_spec h r hr)
  rw [List.all_eq_true]
  intro z hz
  rw [decW_get] at hz
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hz
  have h2 := h1 c hc
  have hs : Nat.shiftRight c 1 = c / 2 := by change c >>> 1 = _; rw [Nat.shiftRight_eq_div_pow]
  dsimp only at h2
  rw [hs] at h2
  obtain ⟨a1, a2⟩ := (andB_iff _ _).1 h2
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, decC_natAbs]
  refine ⟨Nat.le_of_ble_eq_true a1, ?_⟩
  rcases (orB_iff _ _).1 a2 with e | e
  · exact Or.inl (List.contains_iff_mem.2 (memN_spec e))
  · obtain ⟨b1, b2⟩ := (andB_iff _ _).1 e
    exact Or.inr ⟨Nat.le_of_ble_eq_true b1, blt_true b2⟩

set_option maxHeartbeats 0 in
theorem header_ok : headerOK (EK.map decW).toArray = true := by
  unfold headerOK
  simp only [conj_eq]
  decide +kernel

end CertificateChecks.KernelF24S

end
