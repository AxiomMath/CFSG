
module

public import Certificates.Kernel.Ly3085.DischargeBase
public import Certificates.Kernel.Ly3085.FiberCount
public import Certificates.Kernel.Ly3085.HEnum

@[expose] public section

noncomputable section

namespace CertificateChecks.KernelLy.Omega

open CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier CFSG.Sporadic.LySchreier.Native
open CFSG.Sporadic.Ly.Omega CFSG.KS.LyOm CFSG.KC.LyOm CFSG.KC.LL CFSG.KC.Loop
open CertificateChecks.KernelSporSch
open Matrix MulAction

theorem wta_eq : CFSG.KD.LyOm.WTA = (List.replicate 4 [2, 2, 3, 3, 3, 1, 2, 2, 1, 1]).flatten := by
  decide +kernel

theorem wtb_eq : CFSG.KD.LyOm.WTB = (List.replicate 2 [0, 2, 3, 3, 2, 3, 3, 2, 2, 1]).flatten := by
  decide +kernel

theorem lyTA_eq [LySeed] : lyTA = wordJ CFSG.KD.LyOm.WTA := by
  rw [wta_eq]
  rfl

theorem lyTB_eq [LySeed] : lyTB = wordJ CFSG.KD.LyOm.WTB := by
  rw [wtb_eq]
  rfl

theorem wta_lt : ∀ l ∈ CFSG.KD.LyOm.WTA, l < 4 := by decide +kernel

theorem wtb_lt : ∀ l ∈ CFSG.KD.LyOm.WTB, l < 4 := by decide +kernel

theorem cls_of_sClass {X : ℕ} (hX : LCanon 11 7 7 X) :
    (sClass CFSG.KD.LyOm.SC X = 1 → cls 0 (smM X)) ∧
    (sClass CFSG.KD.LyOm.SC X = 65536 → cls 1 (smM X)) ∧
    (sClass CFSG.KD.LyOm.SC X = 4294967296 → cls 2 (smM X)) ∧
    (sClass CFSG.KD.LyOm.SC X = 281474976710656 → cls 3 (smM X)) := by
  rw [sClass_cls hX]
  norm_num only
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · split_ifs at h with h0 h1 h2 h3 <;> first | omega | exact h0
  · split_ifs at h with h0 h1 h2 h3 <;> first | omega | exact h1
  · split_ifs at h with h0 h1 h2 h3 <;> first | omega | exact h2
  · split_ifs at h with h0 h1 h2 h3 <;> first | omega | exact h3

theorem class_facts
    [LySeed] :
    cls 0 (restr7 lyt) ∧ cls 1 (restr7 lyYB) ∧ cls 2 (restr7 lyTA) ∧ cls 3 (restr7 lyTB) := by
  have hc := CFSG.KD.LyOm.clsC
  have eG : CFSG.KD.LyOm.GR = CFSG.KD.LyY.GR := rfl
  generalize hR : CFSG.KD.LyOm.RTl = Rv at hc
  generalize hY : sWord CFSG.KD.LyOm.SC CFSG.KD.LyOm.GR CFSG.KD.LyOm.SC.ONE CFSG.KD.LyOm.WYB = Yv
    at hc
  generalize hA : sWord CFSG.KD.LyOm.SC CFSG.KD.LyOm.GR CFSG.KD.LyOm.SC.ONE CFSG.KD.LyOm.WTA = Av
    at hc
  generalize hB : sWord CFSG.KD.LyOm.SC CFSG.KD.LyOm.GR CFSG.KD.LyOm.SC.ONE CFSG.KD.LyOm.WTB = Bv
    at hc
  obtain ⟨c0, hc⟩ := bAnd_true hc
  obtain ⟨c1, hc⟩ := bAnd_true hc
  obtain ⟨c2, c3⟩ := bAnd_true hc
  have hrt := CFSG.KD.LyOm.clsRT
  generalize hR' : CFSG.KD.LyOm.RTl = Rv' at hrt
  obtain ⟨hR1, hrt⟩ := bAnd_true hrt
  obtain ⟨hR2, -⟩ := bAnd_true hrt
  subst hR'
  have cRT : LCanon 11 7 7 CFSG.KD.LyOm.RTl := sVld_sound hSC hR1
  have eRT : smM CFSG.KD.LyOm.RTl = restr7 lyt := by
    rw [smM_eq_mat7 (ra := LySv.RT) (recAnd (p := fun t => Nat.beq (CFSG.KC.LyOm.sEnt
      CFSG.KD.LyOm.RTl (Nat.div t 7) (Nat.mod t 7)) (LySv.RT[t]!)) 49 hR2), ← LySvF.rt_eq,
      ← LySvF.v_eq, ← LyBSF.b4_eq]
    exact mat7_restrArr repM_tArr
  obtain ⟨cY, eY⟩ := restr7_wordJ wyb_lt
  obtain ⟨cA, eA⟩ := restr7_wordJ wta_lt
  obtain ⟨cB, eB⟩ := restr7_wordJ wtb_lt
  rw [← eG] at cY eY cA eA cB eB
  rw [hY] at cY eY
  rw [hA] at cA eA
  rw [hB] at cB eB
  rw [hR] at cRT eRT
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← eRT]
    exact (cls_of_sClass cRT).1 (beq_eq c0)
  · rw [lyYB_eq, ← eY]
    exact (cls_of_sClass cY).2.1 (by rw [beq_eq c1]; rfl)
  · rw [lyTA_eq, ← eA]
    exact (cls_of_sClass cA).2.2.1 (by rw [beq_eq c2]; rfl)
  · rw [lyTB_eq, ← eB]
    exact (cls_of_sClass cB).2.2.2 (by rw [beq_eq c3]; rfl)

open Classical in
theorem card_fix_finset {G X : Type*} [Group G] [MulAction G X] (g : G) (p : X) (S : Finset X)
    (hS : (S : Set X) = orbit G p) :
    Nat.card {y : orbit G p // g • y = y} = (S.filter fun y => g • y = y).card := by
  have e : {y : orbit G p // g • y = y} ≃ ((S.filter fun y => g • y = y : Finset X) : Set X) :=
    { toFun := fun y => ⟨y.1.1, by
        rw [Finset.coe_filter]
        refine ⟨?_, congrArg Subtype.val y.2⟩
        rw [← Finset.mem_coe, hS]
        exact y.1.2⟩
      invFun := fun z => ⟨⟨z.1, by
          have := (Finset.mem_filter.1 z.2).1
          rw [← Finset.mem_coe, hS] at this
          exact this⟩, Subtype.ext (Finset.mem_filter.1 z.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_coe_set_eq, Set.ncard_coe_finset]

theorem orbit_stab [LySeed] {X : Type*} [MulAction lyH X] (p : X) :
    Nat.card (orbit lyH p) * Nat.card (stabilizer lyH p) = Nat.card lyH := by
  rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer, mul_comm, Subgroup.card_mul_index]

theorem fix_bound [LySeed] {p : LyOperator} {t : lyH} {s cnt k b : ℕ}
    (hs : Nat.card (stabilizer lyH p) = s) (hs0 : 0 < s)
    (hcnt : Nat.card {h : lyH // h ∈ stabilizer lyH p ∧ IsConj t h} ≤ cnt)
    (hc : Nat.card (Subgroup.centralizer ({t} : Set lyH)) ≤ k) (hk : k * cnt ≤ b * s) :
    Nat.card {y : orbit lyH p // t • y = y} ≤ b := by
  have e := card_fix_orbit p t
  rw [hs] at e
  have : Nat.card {y : orbit lyH p // t • y = y} * s ≤ b * s := by
    rw [e]
    exact (Nat.mul_le_mul hc hcnt).trans hk
  exact Nat.le_of_mul_le_mul_right this hs0

theorem conj_count_le
    [LySeed] {p : LyOperator} {K : Subgroup lyH}
    (hK : stabilizer lyH p ≤ K) (k : ℕ) {t : lyH} (ht : cls k (restr7 (t : J))) :
    Nat.card {h : lyH // h ∈ stabilizer lyH p ∧ IsConj t h} ≤
      Nat.card {h : lyH // h ∈ K ∧ cls k (restr7 (h : J))} :=
  Nat.card_le_card_of_injective (fun h => ⟨h.1, hK h.2.1, cls_of_isConj k h.2.2 ht⟩)
    fun a b e => by
      injection e with e'
      exact Subtype.ext e'

theorem stab_le_pair
    [LySeed] (p : LyOperator) :
    stabilizer lyH p ≤ stabilizer lyH (pairOp p) := by
  intro h hh
  rw [mem_stabilizer_iff] at hh ⊢
  rw [← pairOp_smulH, hh]

theorem px_facts
    [LySeed] :
    (LCanon 12 111 111 CFSG.KD.LyOm.PTT ∧ Tm * bigM CFSG.KD.LyOm.PTT * TIm = (mat lyt)ᵀ) ∧
    (LCanon 12 111 111 CFSG.KD.LyOm.PYB ∧ Tm * bigM CFSG.KD.LyOm.PYB * TIm = (mat lyYB)ᵀ) ∧
    (LCanon 12 111 111 CFSG.KD.LyOm.PTA ∧ Tm * bigM CFSG.KD.LyOm.PTA * TIm = (mat lyTA)ᵀ) ∧
    (LCanon 12 111 111 CFSG.KD.LyOm.PTB ∧ Tm * bigM CFSG.KD.LyOm.PTB * TIm = (mat lyTB)ᵀ) := by
  have hp := CFSG.KD.LyOm.clsP
  generalize hA : CFSG.KD.LyOm.PTA = A at hp
  generalize hB : CFSG.KD.LyOm.PTB = B at hp
  generalize hY : CFSG.KD.LyOm.PYB = Y at hp
  obtain ⟨a1, hp⟩ := bAnd_true hp
  obtain ⟨a2, a3⟩ := bAnd_true hp
  have eA : CFSG.KD.LyOm.PTA = CFSG.KD.LyOm.PW CFSG.KD.LyOm.WTA := by rw [hA]; exact beq_eq a1
  have eB : CFSG.KD.LyOm.PTB = CFSG.KD.LyOm.PW CFSG.KD.LyOm.WTB := by rw [hB]; exact beq_eq a2
  have eY : CFSG.KD.LyOm.PYB = CFSG.KD.LyOm.PW CFSG.KD.LyOm.WYB := by rw [hY]; exact beq_eq a3
  have ht := CFSG.KD.LyOm.clsT
  generalize hT : CFSG.KD.LyOm.PTT = T0 at ht
  generalize hTt : CFSG.KD.LyOm.TTt = Tt at ht
  obtain ⟨t1, t2⟩ := bAnd_true ht
  subst hT hTt
  obtain ⟨cTT, eTT⟩ := tt_mat
  obtain ⟨cTt, eTt⟩ := fTr_sound cTT
  rw [← beq_eq t2] at cTt eTt
  have cPT := vld_mem (X := CFSG.KD.LyOm.PTT) (by memL)
  have cT := vld_mem (X := CFSG.KD.LyOm.T) (by memL)
  have m1 := fmul cT cPT
  have m2 := fmul cTt cT
  have hTP : Tm * bigM CFSG.KD.LyOm.PTT = bigM CFSG.KD.LyOm.TTt * Tm := by
    change bigM CFSG.KD.LyOm.T * bigM CFSG.KD.LyOm.PTT =
      bigM CFSG.KD.LyOm.TTt * bigM CFSG.KD.LyOm.T
    rw [← m1.2, beq_eq t1, m2.2]
  refine ⟨⟨cPT, ?_⟩, ?_, ?_, ?_⟩
  · rw [hTP, Matrix.mul_assoc, t_facts.1, Matrix.mul_one, eTt, eTT]
  · rw [← hY, eY, lyYB_eq]
    exact pw_facts _ wyb_lt
  · rw [← hA, eA, lyTA_eq]
    exact pw_facts _ wta_lt
  · rw [← hB, eB, lyTB_eq]
    exact pw_facts _ wtb_lt

theorem o1_sum {XM : ℕ → ℕ} {T : ℕ → ℕ} {s : ℕ}
    (hall : ∀ g < 1, ∀ r < 306, Nat.beq (cFix CFSG.KD.LyO1.BC CFSG.KD.LyO1.KX CFSG.KD.LyO1.PT XM
      CFSG.KD.LyO1.n (Nat.add (Nat.mul g 306) r) 1) (T (Nat.add (Nat.mul g 306) r)) = true)
    (hs : Nat.beq (sumBelow 306 5 T) s = true) :
    ∑ b ∈ Finset.range 306, cFix CFSG.KD.LyOm.BC CFSG.KD.LyO1.KX CFSG.KD.LyO1.PT XM
      CFSG.KD.LyO1.n b 1 = s := by
  rw [← beq_eq hs, SpanC.sumBelow_eq 306 5 T (by norm_num)]
  refine Finset.sum_congr rfl fun b hb => ?_
  have := beq_eq (hall 0 (by norm_num) b (Finset.mem_range.1 hb))
  have e : Nat.add (Nat.mul 0 306) b = b := by change 0 * 306 + b = b; omega
  rw [e] at this
  exact this

end CertificateChecks.KernelLy.Omega

end

end
