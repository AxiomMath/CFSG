module

public import Certificates.Kernel.RuSz.Checks
public import Certificates.Kernel.SporSch.Ru.Pair

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelRuSz

open CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.RuInv CFSG.KC.Misc.RuBase CFSG.KC.Misc.RuPair CFSG.KS.MoveK
  CertificateChecks.KernelSporSch CFSG.EvenSporadicStandard.Induction.RuSz
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native

theorem band_eq (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem tblEq_of {S T : Table} {f g : Nat → Nat} (hS : TR 4060 S f) (hT : TR 4060 T g)
    (h : ∀ i < 4060, f i = g i) : tblEq 4060 S T = true := by
  unfold tblEq
  rw [allIn_iff]
  intro i hi
  rw [hS.2 i hi, hT.2 i hi, h i hi, beq_self_eq_true]

theorem tblEq_false {S T : Table} {f g : Nat → Nat} (hS : TR 4060 S f) (hT : TR 4060 T g)
    (h : difK f g 4060 = true) : tblEq 4060 S T = false := by
  obtain ⟨w, hw, hne⟩ := difK_spec h
  rw [Bool.eq_false_iff]
  intro e
  unfold tblEq at e
  have := (allIn_iff.1 e) w hw
  rw [hS.2 w hw, hT.2 w hw, beq_iff_eq] at this
  exact hne this

theorem hn : (4060 : Nat) < 2 ^ 32 := by decide

theorem trS : TR 4060 sTab (apP SP) ∧ ∀ x < 4060, apP SP x < 4060 :=
  tr_word RuPair.lgens sWord (by rw [RuPair.lsz]; decide)

theorem trT : TR 4060 tTab (apP TP) ∧ ∀ x < 4060, apP TP x < 4060 :=
  tr_word RuPair.lgens tWord (by rw [RuPair.lsz]; decide)

theorem trB : TR 4060 bTab (apP BP) ∧ ∀ x < 4060, apP BP x < 4060 :=
  tr_word RuPair.lgens bWord (by rw [RuPair.lsz]; decide)

theorem pkS : RuG.pk SP (invP SP) = true := by
  have h := inv_ok
  rw [invOK'.eq_1, band_eq, Bool.and_eq_true] at h
  exact h.1

theorem pkT : RuG.pk TP (invP TP) = true := by
  have h := inv_ok
  rw [invOK'.eq_1, band_eq, Bool.and_eq_true] at h
  exact h.2

theorem bS : Bij 4060 (apP SP) (apP (invP SP)) := RuPair.bij_of_pk pkS

theorem bT : Bij 4060 (apP TP) (apP (invP TP)) := RuPair.bij_of_pk pkT

theorem trSI : TR 4060 sInv (apP (invP SP)) := tr_invT hn trS.1 bS

theorem trTI : TR 4060 tInv (apP (invP TP)) := tr_invT hn trT.1 bT

theorem tr_letter (l : Nat × Bool) :
    TR 4060 (CFSG.Sporadic.Bridge.TwoGen.Native.letterTab sTab sInv tTab tInv l)
      (apP (letST SP (invP SP) TP (invP TP) l)) ∧
      ∀ x < 4060, apP (letST SP (invP SP) TP (invP TP) l) x < 4060 := by
  obtain ⟨i, b⟩ := l
  unfold CFSG.Sporadic.Bridge.TwoGen.Native.letterTab letST
  by_cases hi : i = 0
  · subst hi
    cases b
    · exact ⟨trSI, bS.2.1⟩
    · exact ⟨trS.1, trS.2⟩
  · have e : Nat.beq i 0 = false := by
      rw [Bool.eq_false_iff]
      intro h
      exact hi (Nat.eq_of_beq_eq_true h)
    simp only [hi, ↓reduceIte]
    rw [e]
    cases b
    · exact ⟨trTI, bT.2.1⟩
    · exact ⟨trT.1, trT.2⟩

theorem tr_wordST : ∀ v : List (Nat × Bool),
    TR 4060 (CFSG.Sporadic.Bridge.TwoGen.Native.wordTab 4060 sTab sInv tTab tInv v)
      (apP (wordST SP (invP SP) TP (invP TP) v)) ∧
      ∀ x < 4060, apP (wordST SP (invP SP) TP (invP TP) v) x < 4060
  | [] => by
    have e1 : CFSG.Sporadic.Bridge.TwoGen.Native.wordTab 4060 sTab sInv tTab tInv [] =
        idT 4060 := rfl
    have e2 : wordST SP (invP SP) TP (invP TP) [] = idP := rfl
    rw [e1, e2]
    exact ⟨⟨(tr_idT hn).1, fun x hx => by rw [(tr_idT hn).2 x hx, apP_idP hx]⟩,
      fun x hx => by rw [apP_idP hx]; exact hx⟩
  | l :: v => by
    obtain ⟨h1, h2⟩ := tr_wordST v
    obtain ⟨l1, l2⟩ := tr_letter l
    have e : wordST SP (invP SP) TP (invP TP) (l :: v) =
        mulP (letST SP (invP SP) TP (invP TP) l) (wordST SP (invP SP) TP (invP TP) v) := by
      change strictN _ _ = _
      rw [Raw.Orb.strictN_eq]
      rfl
    have ew : CFSG.Sporadic.Bridge.TwoGen.Native.wordTab 4060 sTab sInv tTab tInv (l :: v) =
        compT 4060 (CFSG.Sporadic.Bridge.TwoGen.Native.letterTab sTab sInv tTab tInv l)
          (CFSG.Sporadic.Bridge.TwoGen.Native.wordTab 4060 sTab sInv tTab tInv v) := rfl
    have hc := tr_compT l1 h1 h2
    rw [ew, e]
    exact ⟨⟨hc.1, fun x hx => by rw [hc.2 x hx, apP_mulP hx]⟩,
      fun x hx => by rw [apP_mulP hx]; exact l2 _ (h2 x hx)⟩

theorem tr_kTab (w : String) :
    TR 4060 (kTab w) (apP (wordST SP (invP SP) TP (invP TP) (parseW w))) :=
  (tr_wordST (parseW w)).1

theorem inv_part : ruSzInvOK = true := by
  unfold ruSzInvOK
  rw [invOK_of trS.1 trSI bS, invOK_of trT.1 trTI bT]
  rfl

theorem rel_part : ruSzRelsOK = true := by
  have h := rel_ok
  rw [relOK.eq_1, Raw.Orb.strictB_eq, Raw.Orb.strictB_eq, Raw.Orb.strictB_eq,
    Raw.Orb.strictB_eq, List.all_eq_true] at h
  unfold ruSzRelsOK
  rw [List.all_eq_true]
  intro v hv
  have e := Nat.eq_of_beq_eq_true (h v hv)
  refine tblEq_of (tr_wordST v).1 (tr_idT hn) fun i hi => ?_
  rw [e, apP_idP hi]

theorem nt_part : ruSzNontriv = true := by
  have h := nt_ok
  rw [ntOK.eq_1, Raw.Orb.strictB_eq] at h
  unfold ruSzNontriv
  rw [tblEq_false trS.1 (tr_idT hn) h]
  rfl

theorem norm_part : ruSzNormOK = true := by
  have h := norm_ok
  rw [normOK.eq_1, Raw.Orb.strictB_eq, Raw.Orb.strictB_eq, Raw.Orb.strictB_eq,
    Raw.Orb.strictB_eq, List.all_eq_true] at h
  unfold ruSzNormOK
  rw [List.all_eq_true]
  intro c hc
  have hc1 : c.1 < CFSG.EvenSporadicStandard.TwoRu.HypOne.lGens.size := by
    rw [RuPair.lsz]
    have : ∀ d ∈ normWords, d.1 < 3 := by decide
    exact this c hc
  obtain ⟨g1, g2, g3⟩ := RuPair.lgens c.1 hc1
  have e := Nat.eq_of_beq_eq_true (h c hc)
  have hx : TR 4060 (if c.2.1 then tTab else sTab) (apP (if c.2.1 then TP else SP)) ∧
      ∀ x < 4060, apP (if c.2.1 then TP else SP) x < 4060 := by
    cases c.2.1
    · exact trS
    · exact trT
  have hk := tr_compT (tr_compT g1 hx.1 hx.2) g2 g3.2.1
  unfold conjTab
  refine tblEq_of hk (tr_kTab c.2.2) fun i hi => ?_
  rw [← e, apP_mulP hi, apP_mulP (g3.2.1 i hi)]

theorem cent_part : ruSzCentOK = true := by
  have h := cent_ok
  rw [centOK.eq_1, Raw.Orb.strictB_eq, Raw.Orb.strictB_eq, Raw.Orb.strictB_eq, band_eq, band_eq,
    band_eq, band_eq, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨hBB, hB1, hBA, hBS, hBT⟩ := h
  have tA : TR 4060 (CFSG.EvenSporadicStandard.TwoRu.HypOne.tblOfArr CFSG.Sporadic.RuSchreier.ruA0A)
      (apP RuG.A0) := by
    rw [RuG.a0_eq]
    exact RuPair.tr_unpack _
  have eBB := Nat.eq_of_beq_eq_true hBB
  have eBS := Nat.eq_of_beq_eq_true hBS
  have eBT := Nat.eq_of_beq_eq_true hBT
  unfold ruSzCentOK
  rw [tblEq_of (tr_compT trB.1 trB.1 trB.2) (tr_idT hn) fun i hi => by
      rw [← apP_mulP hi, eBB, apP_idP hi],
    tblEq_false trB.1 (tr_idT hn) hB1, tblEq_false trB.1 tA hBA,
    tblEq_of (tr_compT trB.1 trS.1 trS.2) (tr_compT trS.1 trB.1 trB.2) fun i hi => by
      rw [← apP_mulP hi, ← apP_mulP hi, eBS],
    tblEq_of (tr_compT trB.1 trT.1 trT.2) (tr_compT trT.1 trB.1 trB.2) fun i hi => by
      rw [← apP_mulP hi, ← apP_mulP hi, eBT]]
  rfl

theorem fix_part : ruSzFixOK = true := by
  have h := fix_ok
  rw [fixOK.eq_1, Raw.Orb.strictB_eq, Raw.Orb.strictB_eq, Raw.Orb.strictB_eq,
    Raw.Orb.strictB_eq, Raw.Orb.strictB_eq, Raw.Orb.strictB_eq, Raw.Orb.strictB_eq, band_eq,
    band_eq, band_eq, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨h0, h1, h2, hf⟩ := h
  have t0 := tr_kTab (hWords.getD 0 "")
  have t1 := tr_kTab (hWords.getD 1 "")
  have t2 := tr_kTab (hWords.getD 2 "")
  have eh : hWords.map kTab = [kTab (hWords.getD 0 ""), kTab (hWords.getD 1 ""),
      kTab (hWords.getD 2 "")] := rfl
  unfold ruSzFixOK
  simp only [eh, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [t0.2 0 (by norm_num)]
    exact Nat.eq_of_beq_eq_true h0
  · rw [t1.2 0 (by norm_num)]
    exact Nat.eq_of_beq_eq_true h1
  · rw [t2.2 0 (by norm_num)]
    exact Nat.eq_of_beq_eq_true h2
  · rw [beq_iff_eq] at hf
    rw [← hf]
    apply List.filter_congr
    intro x hx
    have hx' : x < 4060 := List.mem_range.1 hx
    rw [t0.2 x hx', t1.2 x hx', t2.2 x hx', band_eq, band_eq]
    rfl

theorem pt_part : ruSzPtsOK = true := by
  have h := pt_ok
  rw [ptOK.eq_1, Raw.Orb.strictB_eq, Raw.Orb.strictB_eq, Raw.Orb.strictB_eq,
    Raw.Orb.strictB_eq, List.all_eq_true] at h
  unfold ruSzPtsOK
  rw [List.all_eq_true]
  intro c hc
  rw [(tr_kTab c.2).2 0 (by norm_num), beq_iff_eq]
  exact Nat.eq_of_beq_eq_true (h c hc)

theorem ruSz_check : ruSzCheck = true := by
  unfold ruSzCheck
  rw [inv_part, rel_part, nt_part, norm_part, cent_part, fix_part, pt_part]
  rfl

end CertificateChecks.KernelRuSz

end
