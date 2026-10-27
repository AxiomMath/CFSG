module

public import Certificates.Kernel.Sp43K.Members
public import Certificates.Kernel.Sp43K.Three
public import Certificates.Kernel.Sp43K.Facts
public import Certificates.Kernel.Sp43K.Count
public import CFSG.Certificates.Kernel.Sp43KGrp
public import CFSG.Certificates.Kernel.Sp43KCard

public section

namespace CFSG.KD.Sp43K

open CFSG.KC.Sp43K CFSG.Sp43

theorem lstOne_of_chunks {a b n P D m : ℕ} {L : List (ℕ × ℕ × ℕ × ℕ)} (hn : n ≤ 128 * m)
    (h : ∀ k < m, lstK a b n P D (128 * k) (min (128 * k + 128) n)
      ((L.drop (128 * k)).take 128) = true) :
    ∀ i < n, lstOne a b n P D i (L.getD i (0, 0, 0, 0)) = true := by
  intro i hi
  have hk : i / 128 < m := by omega
  obtain ⟨-, -, hall⟩ := lstK_spec (h _ hk)
  have h1 : 128 * (i / 128) ≤ i := Nat.mul_div_le i 128
  have h2 : i < min (128 * (i / 128) + 128) n := by omega
  have e := (hall i h1 h2).2
  have e2 : ((L.drop (128 * (i / 128))).take 128).getD (i - 128 * (i / 128)) (0, 0, 0, 0) =
      L.getD i (0, 0, 0, 0) := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt
      (by omega), List.getElem?_drop, Nat.add_sub_cancel' h1]
  rwa [e2] at e

theorem memC_all : ∀ j < 24, memC j = true := by
  intro j hj
  interval_cases j
  exacts [ch1322001m_0, ch1322001m_1, ch1322001m_2, ch1322001m_3, ch1322001m_4, ch1322001m_5,
    ch1322001m_6, ch1322001m_7, ch1322001m_8, ch1322001m_9, ch1322001m_10, ch1322001m_11,
    ch1322001m_12, ch1322001m_13, ch1322001m_14, ch1322001m_15, ch1322001m_16, ch1322001m_17,
    ch1322001m_18, ch1322001m_19, ch1322001m_20, ch1322001m_21, ch1322001m_22, ch1322001m_23]

private theorem jobs_cover : ∀ i < 5, ∀ k < (ords.getD i 0 + 127) / 128,
    ∃ j < 24, jobs.getD j (0, 0) = (i, 128 * k) := by
  decide

private theorem memC_part {j i s : ℕ} (h : memC j = true) (e : jobs.getD j (0, 0) = (i, s)) :
    memPart i s = true := by
  unfold memC at h
  rwa [e] at h

theorem spC_spec {i : ℕ} (h : spC i = true) : spT (gA i) = true ∧ spT (gB i) = true ∧
    spT (ns.getD i ((0, 0), (0, 0))).1.1 = true ∧ spT (ns.getD i ((0, 0), (0, 0))).1.2 = true ∧
    spT (ns.getD i ((0, 0), (0, 0))).2.1 = true ∧ spT (ns.getD i ((0, 0), (0, 0))).2.2 = true ∧
    List.rec (motive := fun _ => Bool) true
      (fun c _ ih => spT c.1 && spT c.2.2.1 && spT c.2.2.2.1 && ih) (cs i) = true := by
  unfold spC at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem spC_all : ∀ i < 5, spC i = true := by
  intro i hi
  interval_cases i
  exacts [ch1322001sp_0, ch1322001sp_1, ch1322001sp_2, ch1322001sp_3, ch1322001sp_4]

theorem ords_pos : ∀ i < 5, 0 < ords.getD i 0 := by decide

theorem lst_member {i : ℕ} (hi : i < 5) :
    InG (gA i) ∧ InG (gB i) ∧
    (∀ t < ords.getD i 0, okT (fldT (mP i) t) = true ∧ InG (fldT (mP i) t)) ∧
      (∀ t < ords.getD i 0, ∀ t' < ords.getD i 0, fldT (mP i) t = fldT (mP i) t' → t = t') ∧
      (∀ x, x ∈ sub2T (gA i) (gB i) ↔ ∃ t < ords.getD i 0, ofT (fldT (mP i) t) = x) ∧
      Nat.card (sub2T (gA i) (gB i)) = ords.getD i 0 := by
  have hch : ∀ k < (ords.getD i 0 + 127) / 128,
      lstK (gA i) (gB i) (ords.getD i 0) (mP i) (mD i) (128 * k)
        (min (128 * k + 128) (ords.getD i 0)) (((mR i).drop (128 * k)).take 128) = true := by
    intro k hk
    obtain ⟨j, hj, e⟩ := jobs_cover i hi k hk
    have h := memC_part (memC_all j hj) e
    unfold memPart at h
    exact h
  have hpos := ords_pos i hi
  obtain ⟨ha, hb, -⟩ := lstK_spec (hch 0 (by omega))
  obtain ⟨sa, sb, -⟩ := spC_spec (spC_all i hi)
  have hA := inG_of_spT ha sa
  have hB := inG_of_spT hb sb
  exact ⟨hA, hB, lst_spec hA hB hpos (lstOne_of_chunks (m := (ords.getD i 0 + 127) / 128)
    (by omega) hch)⟩

theorem sp5C_spec : spT G5.1 = true ∧ spT G5.2.1 = true ∧ spT G5.2.2.1 = true ∧
    spT G5.2.2.2 = true ∧ spT p0.1 = true ∧ spT p0.2 = true ∧ spT h4.1 = true ∧
    spT h4.2.1 = true ∧ spT h4.2.2.1 = true ∧ spT h4.2.2.2.1 = true ∧ spT h4.2.2.2.2 = true ∧
    spT b.1 = true ∧ spT b.2.1 = true ∧ spT b.2.2.1 = true ∧ spT b.2.2.2 = true ∧
    spT m1.1 = true := by
  have h := ch1322001sp50
  unfold sp5C at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩,
    h14⟩, h15⟩, h16⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

theorem p0C_spec : lstK p0.1 p0.2 81 p0P p0D 0 81 p0R = true ∧ p0T.length = 81 ∧
    inGo p0P nT TP p0T 0 = true := by
  have h := ch1322001p00
  unfold p0C at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, h2, h3⟩

theorem lst_p0 : InG p0.1 ∧ InG p0.2 ∧
    (∀ t < 81, okT (fldT p0P t) = true ∧ InG (fldT p0P t)) ∧
      (∀ t < 81, ∀ t' < 81, fldT p0P t = fldT p0P t' → t = t') ∧
      (∀ x, x ∈ sub2T p0.1 p0.2 ↔ ∃ t < 81, ofT (fldT p0P t) = x) ∧
      Nat.card (sub2T p0.1 p0.2) = 81 := by
  obtain ⟨ha, hb, hall⟩ := lstK_spec p0C_spec.1
  have hA := inG_of_spT ha sp5C_spec.2.2.2.2.1
  have hB := inG_of_spT hb sp5C_spec.2.2.2.2.2.1
  refine ⟨hA, hB, lst_spec (R := fun i => p0R.getD (i - 0) (0, 0, 0, 0)) hA hB (by norm_num)
    fun i hi => (hall i (Nat.zero_le i) hi).2⟩

theorem card_G : Nat.card G = 51840 := by
  have hx : cnt2 xCond = 2160 := by
    have h : cxC = true := ch1322001cx0
    unfold cxC cntK at h
    exact beq_iff_eq.1 h
  have hh : cnt2 hCond = 24 := by
    have h : chC = true := ch1322001ch0
    unfold chC cntK at h
    exact beq_iff_eq.1 h
  have hle := card_G_le_of_cnt hx hh
  have h81 : 81 ∣ Nat.card G := by
    rw [← lst_p0.2.2.2.2.2]
    exact Subgroup.card_subgroup_dvd_card _
  have h1920 : 1920 ∣ Nat.card G := by
    have e : ords.getD 4 0 = 1920 := rfl
    rw [← e, ← (lst_member (i := 4) (by norm_num)).2.2.2.2.2]
    exact Subgroup.card_subgroup_dvd_card _
  have hl : 51840 ∣ Nat.card G := by
    have e : Nat.lcm 81 1920 = 51840 := by norm_num
    have := Nat.lcm_dvd h81 h1920
    rwa [e] at this
  have hpos : 0 < Nat.card G := Nat.card_pos
  obtain ⟨q, hq⟩ := hl
  have : q = 1 := by
    rcases q with _ | _ | q
    · omega
    · rfl
    · omega
  rw [hq, this, mul_one]

end CFSG.KD.Sp43K

end
