module

public import Certificates.Kernel.RuTwoB.Checks
public import Certificates.Kernel.RuSz.Final
public import Std.Tactic.BVDecide.Normalize.Bool

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelRuTwoB

open CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.RuInv CFSG.KC.Misc.RuBase CFSG.KC.Misc.RuPair CFSG.KS.MoveK
  CertificateChecks.KernelSporSch CFSG.EvenSporadicStandard.RuStd.S2
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CertificateChecks.KernelRuSz

theorem apPowW_eq {n : Nat} {T : Table} {f : Nat → Nat} (hT : TR n T f) (hf : ∀ x < n, f x < n) :
    ∀ e, ∀ i < n, apPowW [T] e i = f^[e] i ∧ f^[e] i < n
  | 0 => fun i hi => ⟨rfl, hi⟩
  | e + 1 => fun i hi => by
    obtain ⟨h1, h2⟩ := apPowW_eq hT hf e i hi
    have e1 : apPowW [T] (e + 1) i = ap T (apPowW [T] e i) := rfl
    rw [e1, h1, hT.2 _ h2, Function.iterate_succ_apply']
    exact ⟨rfl, hf _ h2⟩

theorem powFixW_iff {n : Nat} {T : Table} {f : Nat → Nat} (hT : TR n T f)
    (hf : ∀ x < n, f x < n) (e : Nat) : powFixW n [T] e = true ↔ ∀ i < n, f^[e] i = i := by
  unfold powFixW
  rw [allIn_iff]
  refine forall_congr' fun i => forall_congr' fun hi => ?_
  rw [(apPowW_eq hT hf e i hi).1, beq_iff_eq]

theorem ordTest_of {n m : Nat} {T : Table} {f : Nat → Nat} (hT : TR n T f)
    (hf : ∀ x < n, f x < n) (hm : ∀ i < n, f^[m] i = i) (hne : ∃ i < n, f i ≠ i)
    (hd : divParts m = [1]) : ordTest n m T = true := by
  unfold ordTest ordW
  rw [hd, Bool.and_eq_true, (powFixW_iff hT hf m)]
  refine ⟨hm, ?_⟩
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.not_eq_true']
  rw [Bool.eq_false_iff, Ne, powFixW_iff hT hf 1]
  obtain ⟨i, hi, hne⟩ := hne
  exact fun h => hne (h i hi)

theorem divParts_five : divParts 5 = [1] := by decide

theorem divParts_two : divParts 2 = [1] := by decide

theorem trG : TR 4060 (twoBTab twoBWordG) (apP GP) ∧ ∀ x < 4060, apP GP x < 4060 :=
  tr_word RuPair.lgens twoBWordG (by rw [RuPair.lsz]; decide)

theorem trH : TR 4060 (twoBTab twoBWordH) (apP HP) ∧ ∀ x < 4060, apP HP x < 4060 :=
  tr_word RuPair.lgens twoBWordH (by rw [RuPair.lsz]; decide)

theorem trU : TR 4060 (twoBTab twoBWordU) (apP UP) ∧ ∀ x < 4060, apP UP x < 4060 :=
  tr_word RuPair.lgens twoBWordU (by rw [RuPair.lsz]; decide)

theorem pkG : RuG.pk GP (invP GP) = true := by
  have h := ch24942_inv
  rw [invOK24942.eq_1, band_eq, Bool.and_eq_true] at h
  exact h.1

theorem pkH : RuG.pk HP (invP HP) = true := by
  have h := ch24942_inv
  rw [invOK24942.eq_1, band_eq, Bool.and_eq_true] at h
  exact h.2

theorem bG : Bij 4060 (apP GP) (apP (invP GP)) := RuPair.bij_of_pk pkG

theorem bH : Bij 4060 (apP HP) (apP (invP HP)) := RuPair.bij_of_pk pkH

theorem trGI : TR 4060 (invT 4060 (twoBTab twoBWordG)) (apP (invP GP)) := tr_invT hn trG.1 bG

theorem trHI : TR 4060 (invT 4060 (twoBTab twoBWordH)) (apP (invP HP)) := tr_invT hn trH.1 bH

theorem trC : TR 4060 twoBComm (apP CP) ∧ ∀ x < 4060, apP CP x < 4060 := by
  have h1 := tr_compT trG.1 trH.1 trH.2
  have h2 := tr_compT h1 trGI fun x hx => bG.2.1 x hx
  have h3 := tr_compT h2 trHI fun x hx => bH.2.1 x hx
  unfold twoBComm
  refine ⟨⟨h3.1, fun x hx => ?_⟩, fun x hx => ?_⟩
  · rw [h3.2 x hx, CP, apP_mulP hx, apP_mulP (bH.2.1 x hx), apP_mulP (bG.2.1 _ (bH.2.1 x hx))]
  · rw [CP, apP_mulP hx, apP_mulP (bH.2.1 x hx), apP_mulP (bG.2.1 _ (bH.2.1 x hx))]
    exact trG.2 _ (trH.2 _ (bG.2.1 _ (bH.2.1 x hx)))

theorem comm_part : ordTest 4060 5 twoBComm = true := by
  have h := ch24942_comm
  rw [commOK24942.eq_1, Raw.Orb.strictB_eq, Raw.Orb.strictB_eq, band_eq, Bool.and_eq_true] at h
  obtain ⟨h5, hd⟩ := h
  have e5 := Nat.eq_of_beq_eq_true h5
  refine ordTest_of trC.1 trC.2 (fun i hi => ?_) (difK_spec hd) divParts_five
  have := congrArg (fun p => apP p i) e5
  rw [apP_idP hi, apP_mulP hi, apP_mulP hi, apP_mulP hi, apP_mulP (trC.2 _ (trC.2 _ hi))] at this
  simpa only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id] using this

theorem u_facts : Nat.beq (mulP UP UP) idP = true ∧ difK (apP UP) (fun i => i) 4060 = true ∧
    difK (apP UP) (apP RuG.A0) 4060 = true ∧
    Nat.beq (mulP UP (RuW.LG 0)) (mulP (RuW.LG 0) UP) = true ∧
    Nat.beq (mulP UP (RuW.LG 1)) (mulP (RuW.LG 1) UP) = true ∧
    Nat.beq (mulP UP (RuW.LG 2)) (mulP (RuW.LG 2) UP) = true := by
  have h := ch24942_u
  rw [uOK24942.eq_1, Raw.Orb.strictB_eq, band_eq, band_eq, band_eq, band_eq, band_eq,
    Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true] at h
  exact h

theorem u_part : ordTest 4060 2 (twoBTab twoBWordU) = true := by
  have e2 := Nat.eq_of_beq_eq_true u_facts.1
  refine ordTest_of trU.1 trU.2 (fun i hi => ?_) (difK_spec u_facts.2.1) divParts_two
  have := congrArg (fun p => apP p i) e2
  rw [apP_idP hi, apP_mulP hi] at this
  simpa only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id] using this

theorem a0_part : tblEq 4060 (twoBTab twoBWordU)
    (CFSG.EvenSporadicStandard.TwoRu.HypOne.tblOfArr CFSG.Sporadic.RuSchreier.ruA0A) = false := by
  have tA : TR 4060 (CFSG.EvenSporadicStandard.TwoRu.HypOne.tblOfArr CFSG.Sporadic.RuSchreier.ruA0A)
      (apP RuG.A0) := by
    rw [RuG.a0_eq]
    exact RuPair.tr_unpack _
  exact tblEq_false trU.1 tA u_facts.2.2.1

theorem cent_one {k : Nat} (hk : k < 3)
    (h : Nat.beq (mulP UP (RuW.LG k)) (mulP (RuW.LG k) UP) = true) :
    commT 4060 (twoBTab twoBWordU) CFSG.EvenSporadicStandard.TwoRu.HypOne.lGens[k]! = true := by
  have hk' : k < CFSG.EvenSporadicStandard.TwoRu.HypOne.lGens.size := by rw [RuPair.lsz]; exact hk
  obtain ⟨g1, -, g3⟩ := RuPair.lgens k hk'
  have e := Nat.eq_of_beq_eq_true h
  unfold commT
  exact tblEq_of (tr_compT trU.1 g1 g3.1) (tr_compT g1 trU.1 trU.2) fun i hi => by
    rw [← apP_mulP hi, ← apP_mulP hi, e]

theorem ruTwoB_check : ruTwoBCheck = true := by
  unfold ruTwoBCheck
  rw [invOK_of trG.1 trGI bG, invOK_of trH.1 trHI bH, comm_part, u_part, a0_part]
  simp only [Bool.true_and, Bool.not_false]
  rw [RuPair.lsz]
  unfold CFSG.Monster.B.Co2.Native.allLt
  change Nat.all (0 + 1 + 1 + 1) _ = true
  simp only [Nat.all_succ, Nat.all_zero, Bool.true_and, Bool.and_eq_true, Nat.zero_add,
    Nat.reduceAdd]
  exact ⟨⟨cent_one (by decide) u_facts.2.2.2.1, cent_one (by decide) u_facts.2.2.2.2.1⟩,
    cent_one (by decide) u_facts.2.2.2.2.2⟩

end CertificateChecks.KernelRuTwoB

end
