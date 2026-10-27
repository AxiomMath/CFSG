
module

public import Certificates.Kernel.Misc.RuBigZ.RefK
public import Certificates.Kernel.Misc.RuBigZ.Ref
public import Certificates.Kernel.Misc.RuScan.Cand
public import CFSG.Certificates.Kernel.Misc.RuBigZSound

public section

namespace CertificateChecks.KernelMisc.RuBigZ

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KC.Misc.RuInv
  CFSG.KC.Misc.RuInv.P CFSG.KC.Misc.RuScan CFSG.KC.Misc.RuBigZ
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CertificateChecks.KernelSporSch CertificateChecks.KernelMisc.RuScan CFSG.Quasithin.KGC31
  CFSG.Quasithin.KGC31.Ru CFSG.Sporadic.RuSchreier CFSG.Sporadic.Schreier

@[expose] def rW (k : Nat) : List Int :=
  (basisEW ++ basis64W ++ basis3W ++ basis16W ++ basis32W).getD k []

@[expose] def qV (k : Nat) : List Int := (basisV32EW ++ basisV32pW).getD k []

@[expose] def tOf (k : Nat) : Nat :=
  [0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 4].getD k 0

@[expose] def iOf (k : Nat) : Nat :=
  [0, 1, 2, 0, 1, 2, 3, 4, 5, 0, 1, 2, 0, 1, 2, 3, 0, 1, 2, 3, 4].getD k 0

theorem rW_eq : ∀ k < 21, rW k = (refW (tOf k)).getD (iOf k) [] := by decide

theorem qV_eq : ∀ k < 10, 2 ≤ k → qV k = rW (qd k) := by decide

section Bind

theorem prep_R {k : Nat} (hk : k < 21) : PRep 4060 12 (R k) (wG (rW k)) := by
  have h := CFSG.KC.Misc.RuBase.allN_iff.1 ch7233rb_ok k hk
  rw [Nat.eq_of_beq_eq_true h, rW_eq k hk]
  have e : Nat.add 46 k = 46 + boff (tOf k) + iOf k := by interval_cases k <;> rfl
  rw [e]
  exact prep_xb (by interval_cases k <;> decide) (by interval_cases k <;> decide)

theorem ptR_R {k : Nat} (hk : k < 21) : PtR (apP (R k)) (wG (rW k)) := ptR_apP (prep_R hk)

theorem ptR_Rs {o r : Nat} {ws : List (List Int)} (hb : o + r ≤ 21)
    (hw : ∀ i < r, rW (o + i) = ws.getD i []) :
    ∀ i < r, PtR (apP (R (o + i))) (wG (ws.getD i [])) := fun i hi => by
  rw [← hw i hi]
  exact ptR_R (k := o + i) (by omega)

theorem prep_Q {k : Nat} (hk : k < 10) : PRep 4060 12 (Q k) (wG (qV k)) := by
  rcases Nat.lt_or_ge k 2 with h2 | h2
  · have h : wd6 (basisV32EW.getD k []) (Q k) = true := by
      interval_cases k
      · exact ch7233q_0
      · exact ch7233q_1
    have e : qV k = basisV32EW.getD k [] := by interval_cases k <;> rfl
    rw [e]
    exact (rep_word6 h).2
  · have h : Nat.beq (Q k) (R (qd k)) = true := by
      interval_cases k
      · exact ch7233q_2
      · exact ch7233q_3
      · exact ch7233q_4
      · exact ch7233q_5
      · exact ch7233q_6
      · exact ch7233q_7
      · exact ch7233q_8
      · exact ch7233q_9
    rw [Nat.eq_of_beq_eq_true h, qV_eq k hk h2]
    exact prep_R (by interval_cases k <;> decide)

theorem ptR_Qs {o r : Nat} {ws : List (List Int)} (hb : o + r ≤ 10)
    (hw : ∀ i < r, qV (o + i) = ws.getD i []) :
    ∀ i < r, PtR (apP (Q (o + i))) (wG (ws.getD i [])) := fun i hi => by
  rw [← hw i hi]
  exact ptR_apP (prep_Q (k := o + i) (by omega))

theorem prep_QW {k : Nat} (hk : k = 10 ∨ k = 12 ∨ k = 14 ∨ k = 16) :
    PRep 4060 12 (Q k) (wG (qW k)) ∧ PRep 4060 12 (Q (k + 1)) (wG (qW k))⁻¹ := by
  have hw : wd6 (qW k) (Q k) = true := by
    rcases hk with rfl | rfl | rfl | rfl
    · exact ch7233q_10
    · exact ch7233q_12
    · exact ch7233q_14
    · exact ch7233q_16
  have hi : invEqK 4060 12 (mask 12) (4060 * 12) (Q k) (Q (k + 1)) = true := by
    rcases hk with rfl | rfl | rfl | rfl
    · exact ch7233q_11
    · exact ch7233q_13
    · exact ch7233q_15
    · exact ch7233q_17
  have hp := (rep_word6 hw).2
  refine ⟨hp, prep_of' ?_ (rep_ruInv' (rep_unpack hp))⟩
  rw [ruInv]
  exact (invEqK_sound hi).1

theorem ptR_QW {k : Nat} (hk : k = 10 ∨ k = 12 ∨ k = 14 ∨ k = 16) :
    PtR (apP (Q k)) (wG (qW k)) ∧ PtR (apP (Q (k + 1))) (wG (qW k))⁻¹ :=
  ⟨ptR_apP (prep_QW hk).1, ptR_apP (prep_QW hk).2⟩

theorem ptR_pk6 {a b c d e f : Nat} {ga gb gc gd ge gf : Equiv.Perm (Fin 4060)}
    (ha : PRep 4060 12 a ga) (hb : PRep 4060 12 b gb) (hc : PRep 4060 12 c gc)
    (hd : PRep 4060 12 d gd) (he : PRep 4060 12 e ge) (hf : PRep 4060 12 f gf) :
    ∀ k < 6, PtR (pkA (gen6 a b c d e f) k) ([ga, gb, gc, gd, ge, gf].getD k 1) := by
  intro k hk
  interval_cases k
  · exact ptR_apP ha
  · exact ptR_apP hb
  · exact ptR_apP hc
  · exact ptR_apP hd
  · exact ptR_apP he
  · exact ptR_apP hf

theorem ptR_pk6I {a b c d e f : Nat} {ga gb gc gd ge gf : Equiv.Perm (Fin 4060)}
    (ha : PRep 4060 12 a ga⁻¹) (hb : PRep 4060 12 b gb⁻¹) (hc : PRep 4060 12 c gc⁻¹)
    (hd : PRep 4060 12 d gd⁻¹) (he : PRep 4060 12 e ge⁻¹) (hf : PRep 4060 12 f gf⁻¹) :
    ∀ k < 6, PtR (pkA (gen6 a b c d e f) k) ([ga, gb, gc, gd, ge, gf].getD k 1)⁻¹ := by
  intro k hk
  interval_cases k
  · exact ptR_apP ha
  · exact ptR_apP hb
  · exact ptR_apP hc
  · exact ptR_apP hd
  · exact ptR_apP he
  · exact ptR_apP hf

theorem ptR_pk2 {a b : Nat} {ga gb : Equiv.Perm (Fin 4060)} (ha : PRep 4060 12 a ga)
    (hb : PRep 4060 12 b gb) : ∀ k < 2, PtR (pkA (gen2 a b) k) ([ga, gb].getD k 1) := by
  intro k hk
  interval_cases k
  · exact ptR_apP ha
  · exact ptR_apP hb

theorem ptR_pk2I {a b : Nat} {ga gb : Equiv.Perm (Fin 4060)} (ha : PRep 4060 12 a ga⁻¹)
    (hb : PRep 4060 12 b gb⁻¹) : ∀ k < 2, PtR (pkA (gen2 a b) k) ([ga, gb].getD k 1)⁻¹ := by
  intro k hk
  interval_cases k
  · exact ptR_apP ha
  · exact ptR_apP hb

theorem prep_inv' {a : Array Nat} {P PI : Nat} {g : Equiv.Perm (Fin 4060)}
    (ha : a = unpack 4060 12 P) (hP : RuG.pk P PI = true) (h : Rep 4060 a g) :
    PRep 4060 12 PI g⁻¹ :=
  prep_of' (RuG.inv_of ha hP).1 (rep_ruInv' h)

theorem prep_C0 : PRep 4060 12 RuG.C0 ruC0 := prep_of' RuG.c0_eq rep_ruC0
theorem prep_C1 : PRep 4060 12 RuG.C1 ruC1 := prep_of' RuG.c1_eq rep_ruC1
theorem prep_C0I : PRep 4060 12 RuG.C0I ruC0⁻¹ := prep_inv' RuG.c0_eq RuG.pC0 rep_ruC0
theorem prep_C1I : PRep 4060 12 RuG.C1I ruC1⁻¹ := prep_inv' RuG.c1_eq RuG.pC1 rep_ruC1
theorem prep_Ns0 : PRep 4060 12 RuG.Ns0 ruNs0 := prep_of' RuG.ns0_eq rep_ruNs0
theorem prep_Ns1 : PRep 4060 12 RuG.Ns1 ruNs1 := prep_of' RuG.ns1_eq rep_ruNs1
theorem prep_Ns0I : PRep 4060 12 RuG.Ns0I ruNs0⁻¹ := prep_inv' RuG.ns0_eq RuG.pNs0 rep_ruNs0
theorem prep_Ns1I : PRep 4060 12 RuG.Ns1I ruNs1⁻¹ := prep_inv' RuG.ns1_eq RuG.pNs1 rep_ruNs1

theorem ptR_A6 : (∀ k < 6, PtR (A6 k) (g6G.getD k 1)) ∧ ∀ k < 6, PtR (A6I k) (g6G.getD k 1)⁻¹ :=
  ⟨ptR_pk6 (prep_of' RuG.a0_eq rep_ruA0) (prep_of' RuG.a1_eq rep_ruA1) prep_C0 prep_C1 prep_Ns0
      prep_Ns1,
    ptR_pk6I (prep_inv' RuG.a0_eq RuG.pA0 rep_ruA0) (prep_inv' RuG.a1_eq RuG.pA1 rep_ruA1)
      prep_C0I prep_C1I prep_Ns0I prep_Ns1I⟩

theorem mProd_top (v : Nat → Equiv.Perm (Fin 4060)) {m i : Nat} (hi : i < 4) (h1 : 2 ^ i ≤ m)
    (h2 : m < 2 * 2 ^ i) : mProd v 4 m = v i * mProd v 4 (m - 2 ^ i) := by
  interval_cases i
  all_goals norm_num at h1 h2
  all_goals interval_cases m
  all_goals simp [mProd, Nat.testBit_eq_decide_div_mod_eq]

theorem hiB_tab : ∀ m < 16, 1 ≤ m → hiB m < 4 ∧ 2 ^ hiB m ≤ m ∧ m < 2 * 2 ^ hiB m := by decide

theorem prep_RW : ∀ m < 16,
    PRep 4060 12 (R (21 + m)) (mProd (fun i => wG (basis16W.getD i [])) 4 m) := by
  have h := ch7233rw_ok
  unfold ch7233rw at h
  rw [CFSG.KC.Misc.RuBase.bAnd_eq', Bool.and_eq_true] at h
  obtain ⟨h0, h1⟩ := h
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · change PRep 4060 12 (R 21) (mProd (fun i => wG (basis16W.getD i [])) 4 0)
      rw [Nat.eq_of_beq_eq_true h0, show mProd (fun i => wG (basis16W.getD i [])) 4 0 = 1 by
        simp [mProd]]
      exact prep_idP
    · have hd := CFSG.KC.Misc.RuBase.allN_iff.1 h1 (m - 1) (by omega)
      have e : Nat.succ (m - 1) = m := by omega
      rw [sB] at hd
      beta_reduce at hd
      rw [e, sB] at hd
      beta_reduce at hd
      obtain ⟨hi4, hi2, hi3⟩ := hiB_tab m hm hpos
      obtain ⟨i, hi⟩ : ∃ i, hiB m = i := ⟨_, rfl⟩
      rw [hi] at hd hi4 hi2 hi3
      have ht := mProd_top (fun i => wG (basis16W.getD i [])) hi4 hi2 hi3
      change PRep 4060 12 (R (Nat.add 21 m)) _
      rw [Nat.eq_of_beq_eq_true hd, ht]
      have hR := prep_R (k := 12 + i) (by omega)
      have hw : rW (12 + i) = basis16W.getD i [] := by interval_cases i <;> rfl
      rw [hw] at hR
      have e2 : Nat.add 21 (Nat.sub m (Nat.shiftLeft 1 i)) = 21 + (m - 2 ^ i) := by
        rw [shl1]
        rfl
      change PRep 4060 12 (mulP (R (Nat.add 12 i)) (R (Nat.add 21 (Nat.sub m (Nat.shiftLeft 1 i)))))
        _
      rw [e2]
      exact prep_mulP hR (ih _ (by omega) (by omega))

theorem ptR_wF {w : List Int} (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 6) :
    PtR (wF w) (wG w) ∧ PtR (wFI w) (wG w)⁻¹ :=
  ptR_wAp ptR_A6.1 ptR_A6.2 w hw

end Bind

section Facts

theorem hbsJ : ∀ x ∈ ruJoinBase, x < 4 := by decide

theorem bF : BaseFaithful ruP ruJoinBase := ruJoin_baseFaithful

theorem wGv_mem (ws : List (List Int)) (i : Nat) : wG (ws.getD i []) ∈ ruP := wG_mem _

theorem comm_of_eb {r : Nat} {v : Nat → Equiv.Perm (Fin 4060)}
    (h : EBasis (fun i : Fin r => v i)) : ∀ i < r, ∀ j < r, Commute (v i) (v j) :=
  fun i hi j hj => h.comm ⟨i, hi⟩ ⟨j, hj⟩

theorem pE : ∀ i < 3, PtR (apP (R (0 + i))) (wG (basisEW.getD i [])) := ptR_Rs (by norm_num) (by decide)
theorem p64 : ∀ i < 6, PtR (apP (R (3 + i))) (wG (basis64W.getD i [])) :=
  ptR_Rs (by norm_num) (by decide)
theorem p3 : ∀ i < 3, PtR (apP (R (9 + i))) (wG (basis3W.getD i [])) := ptR_Rs (by norm_num) (by decide)
theorem p16 : ∀ i < 4, PtR (apP (R (12 + i))) (wG (basis16W.getD i [])) :=
  ptR_Rs (by norm_num) (by decide)
theorem p32 : ∀ i < 5, PtR (apP (R (16 + i))) (wG (basis32W.getD i [])) :=
  ptR_Rs (by norm_num) (by decide)
theorem pV32E : ∀ i < 5, PtR (apP (Q (0 + i))) (wG (basisV32EW.getD i [])) :=
  ptR_Qs (by norm_num) (by decide)
theorem pV32p : ∀ i < 5, PtR (apP (Q (5 + i))) (wG (basisV32pW.getD i [])) :=
  ptR_Qs (by norm_num) (by decide)

theorem ebasisK : EBasis vE ∧ EBasis v64 ∧ EBasis v3 ∧ EBasis v16 ∧ EBasis v32 ∧ EBasis vV32E ∧
    EBasis vV32p := by
  have h := ch7233eb_ok
  unfold ch7233eb at h
  simp only [CFSG.KC.Misc.RuBase.bAnd_eq', Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨ebB_sound bF hbsJ pE (wGv_mem _) h1, ebB_sound bF hbsJ p64 (wGv_mem _) h2,
    ebB_sound bF hbsJ p3 (wGv_mem _) h3, ebB_sound bF hbsJ p16 (wGv_mem _) h4,
    ebB_sound bF hbsJ p32 (wGv_mem _) h5, ebB_sound bF hbsJ pV32E (wGv_mem _) h6,
    ebB_sound bF hbsJ pV32p (wGv_mem _) h7⟩

theorem mem_of_inSp {o r : Nat} {P : Nat → Nat} {ws : List (List Int)}
    (hP : ∀ i < r, PtR (apP (P (o + i))) (wG (ws.getD i [])))
    (hv : EBasis (vOf ws r)) {f : Nat → Nat} {g : Equiv.Perm (Fin 4060)} (hg : g ∈ ruP)
    (hf : PtR f g) (h : inSp P o r (img4 f) = true) : g ∈ refSub (vOf ws r) := by
  obtain ⟨m, -, e⟩ := inSp_sound bF hbsJ hP (wGv_mem _) (comm_of_eb hv) hg hf h
  rw [refSub_eq hv, e]
  exact eElt_mem hv _

theorem inSp_of_mem {o r : Nat} {P : Nat → Nat} {ws : List (List Int)}
    (hP : ∀ i < r, PtR (apP (P (o + i))) (wG (ws.getD i [])))
    (hv : EBasis (vOf ws r)) {f : Nat → Nat} {g : Equiv.Perm (Fin 4060)}
    (hf : PtR f g) (h : g ∈ refSub (vOf ws r)) : inSp P o r (img4 f) = true := by
  rw [refSub_eq hv, mem_eSub_iff] at h
  obtain ⟨c, rfl⟩ := h
  obtain ⟨m, hm, rfl⟩ := exists_maskVec c
  rw [inSp_iff]
  refine ⟨m, hm, img4_eq_of_eq (ptR_mAp m hP) ?_⟩
  rw [mProd_eq_eElt m (comm_of_eb hv)]
  exact hf

theorem ptR_Z : PtR (apP RuG.Z) ruZ := ptR_apP (prep_of' RuG.z_eq rep_ruZ)

theorem ruZ_memK : ruZ ∈ uE ∧ ruZ ∈ u64 ∧ ruZ ∈ u3 ∧ ruZ ∈ u16 ∧ ruZ ∈ u32 := by
  have h := ch7233zs_ok
  unfold ch7233zs at h
  rw [sB] at h
  simp only [CFSG.KC.Misc.RuBase.bAnd_eq', Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have eb := ebasisK
  exact ⟨mem_of_inSp pE eb.1 ruZ_mem ptR_Z h1, mem_of_inSp p64 eb.2.1 ruZ_mem ptR_Z h2,
    mem_of_inSp p3 eb.2.2.1 ruZ_mem ptR_Z h3, mem_of_inSp p16 eb.2.2.2.1 ruZ_mem ptR_Z h4,
    mem_of_inSp p32 eb.2.2.2.2.1 ruZ_mem ptR_Z h5⟩

theorem uE_le_uV32EK : uE ≤ uV32E := by
  refine refSub_le_of_forall fun i => ?_
  have h := CFSG.KC.Misc.RuBase.allN_iff.1 ch7233ev_ok i i.2
  have hp := pE i i.2
  rw [Nat.zero_add] at hp
  exact mem_of_inSp pV32E ebasisK.2.2.2.2.2.1 (wG_mem _) hp h

theorem exists_mProd {r : Nat} {ws : List (List Int)} (hv : EBasis (vOf ws r))
    {g : Equiv.Perm (Fin 4060)} (hg : g ∈ refSub (vOf ws r)) :
    ∃ m < 2 ^ r, g = mProd (fun i => wG (ws.getD i [])) r m := by
  rw [refSub_eq hv, mem_eSub_iff] at hg
  obtain ⟨c, rfl⟩ := hg
  obtain ⟨m, hm, rfl⟩ := exists_maskVec c
  exact ⟨m, hm, (mProd_eq_eElt (v := fun i => wG (ws.getD i [])) m
    (comm_of_eb (v := fun i => wG (ws.getD i [])) hv)).symm⟩

theorem mProd_zero (v : Nat → Equiv.Perm (Fin 4060)) : ∀ r, mProd v r 0 = 1
  | 0 => rfl
  | r + 1 => by rw [mProd, mProd_zero v r]; simp

theorem ncard_fix {f : Nat → Nat} {g : Equiv.Perm (Fin 4060)} (hf : PtR f g) :
    (fixSet g).ncard = fixC f := by
  rw [fixC_eq, ← ncard_finSet (pointList_fix f), finSet_fix hf]

theorem ncard_fix_uEK {g : Equiv.Perm (Fin 4060)} (hg : g ∈ uE) (h1 : g ≠ 1) :
    (fixSet g).ncard = 92 := by
  obtain ⟨m, hm, rfl⟩ := exists_mProd ebasisK.1 hg
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact h1 (mProd_zero _ _)
  have h := CFSG.KC.Misc.RuBase.allN_iff.1 ch7233fe_ok (m - 1) (by omega)
  have e : Nat.succ (m - 1) = m := by omega
  rw [e] at h
  rw [ncard_fix (ptR_mAp m pE), Nat.eq_of_beq_eq_true h]

theorem ncard_fix_uV32EK {g : Equiv.Perm (Fin 4060)} (hg : g ∈ uV32E) (hE : g ∉ uE) :
    (fixSet g).ncard = 0 := by
  obtain ⟨m, hm, rfl⟩ := exists_mProd ebasisK.2.2.2.2.2.1 hg
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hE (by rw [mProd_zero]; exact Subgroup.one_mem _)
  have h := CFSG.KC.Misc.RuBase.allN_iff.1 ch7233fv_ok (m - 1) (by omega)
  have e : Nat.succ (m - 1) = m := by omega
  rw [sB] at h
  beta_reduce at h
  rw [e, CFSG.KC.Misc.RuBase.bIf_eq] at h
  have hP := ptR_mAp m pV32E
  split_ifs at h with hin
  · exact absurd (mem_of_inSp pE ebasisK.1 (mProd_mem bF hbsJ (wGv_mem _) m 5) hP hin) hE
  · rw [ncard_fix hP, Nat.eq_of_beq_eq_true h]

theorem mem_norm_of_normB {o r : Nat} {ws : List (List Int)}
    (hP : ∀ i < r, PtR (apP (R (o + i))) (wG (ws.getD i []))) (hv : EBasis (vOf ws r))
    {A AI : Nat → Nat} {a : Equiv.Perm (Fin 4060)} (ha : a ∈ ruP) (hA : PtR A a)
    (hAI : PtR AI a⁻¹) (h : normB R o r A AI = true) :
    a ∈ Subgroup.normalizer (refSub (vOf ws r) : Set (Equiv.Perm (Fin 4060))) := by
  refine mem_normalizer_of_forall fun i => ?_
  obtain ⟨m, -, e⟩ := normB_sound bF hbsJ hP (wGv_mem _) (comm_of_eb hv) ha hA hAI h i i.2
  rw [refSub_eq hv]
  change a * wG (ws.getD i []) * a⁻¹ ∈ _
  rw [e]
  exact eElt_mem hv _

theorem normB_of_mem {o r : Nat} {ws : List (List Int)}
    (hP : ∀ i < r, PtR (apP (R (o + i))) (wG (ws.getD i []))) (hv : EBasis (vOf ws r))
    {A AI : Nat → Nat} {a : Equiv.Perm (Fin 4060)} (hA : PtR A a) (hAI : PtR AI a⁻¹)
    (h : a ∈ Subgroup.normalizer (refSub (vOf ws r) : Set (Equiv.Perm (Fin 4060)))) :
    normB R o r A AI = true := by
  refine CFSG.KC.Misc.RuBase.allN_iff.2 fun i hi => ?_
  rw [sB]
  have h1 : a * vOf ws r ⟨i, hi⟩ * a⁻¹ ∈ refSub (vOf ws r) :=
    (Subgroup.mem_normalizer_iff.mp h _).mp (Subgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩)
  have hc : PtR (fun x => A (apP (R (o + i)) (AI x))) (a * wG (ws.getD i []) * a⁻¹) :=
    ptR_comp (f := fun y => A (apP (R (o + i)) y)) (f' := AI)
      (ptR_comp (f := A) (f' := apP (R (o + i))) hA (hP i hi)) hAI
  exact inSp_of_mem hP hv hc h1

theorem x16_mem_normK : x16 ∈ Subgroup.normalizer (u16 : Set (Equiv.Perm (Fin 4060))) :=
  mem_norm_of_normB p16 ebasisK.2.2.2.1 (wG_mem _) (ptR_QW (Or.inr (Or.inl rfl))).1
    (ptR_QW (Or.inr (Or.inl rfl))).2 ch7233nx_ok

theorem ruC_le_norm32K : ruC ≤ Subgroup.normalizer (u32 : Set (Equiv.Perm (Fin 4060))) := by
  have h := ch7233nc_ok
  unfold ch7233nc at h
  simp only [CFSG.KC.Misc.RuBase.bAnd_eq', Bool.and_eq_true] at h
  obtain ⟨h0, h1⟩ := h
  rw [ruC, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact mem_norm_of_normB p32 ebasisK.2.2.2.2.1 ruC0_mem (ptR_apP prep_C0) (ptR_apP prep_C0I) h0
  · exact mem_norm_of_normB p32 ebasisK.2.2.2.2.1 ruC1_mem (ptR_apP prep_C1) (ptR_apP prep_C1I) h1

theorem orderOf_of_ordB {p : Nat} (hp : p.Prime) {f : Nat → Nat} {g : Equiv.Perm (Fin 4060)}
    (hg : g ∈ ruP) (hf : PtR f g) (h : ordB f p = true) : orderOf g = p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨h1, h2⟩ := ordB_sound bF hbsJ hg hf h
  exact orderOf_eq_prime h1 h2

theorem orderOfK : orderOf xE = 7 ∧ orderOf x16 = 5 ∧ orderOf x32 = 5 := by
  have h := ch7233or_ok
  unfold ch7233or at h
  simp only [CFSG.KC.Misc.RuBase.bAnd_eq', Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨orderOf_of_ordB (by norm_num) (wG_mem _) (ptR_QW (Or.inl rfl)).1 h1,
    orderOf_of_ordB (by norm_num) (wG_mem _) (ptR_QW (Or.inr (Or.inl rfl))).1 h2,
    orderOf_of_ordB (by norm_num) (wG_mem _) (ptR_QW (Or.inr (Or.inr (Or.inl rfl)))).1 h3⟩

theorem conj_x16_not_normK :
    g16 * x16 * g16⁻¹ ∉ Subgroup.normalizer (u16 : Set (Equiv.Perm (Fin 4060))) := by
  intro h
  have hg : PtR (apP (Q 16)) g16 ∧ PtR (apP (Q 17)) g16⁻¹ :=
    ptR_QW (k := 16) (Or.inr (Or.inr (Or.inr rfl)))
  have hx : PtR (apP (Q 12)) x16 ∧ PtR (apP (Q 13)) x16⁻¹ := ptR_QW (k := 12) (Or.inr (Or.inl rfl))
  have hA := ptR_comp (ptR_comp hg.1 hx.1) hg.2
  have hAI := ptR_comp (ptR_comp hg.1 hx.2) hg.2
  have e : (g16 * x16 * g16⁻¹)⁻¹ = g16 * x16⁻¹ * g16⁻¹ := by group
  rw [← e] at hAI
  have h1 := normB_of_mem p16 ebasisK.2.2.2.1 hA hAI h
  have h2 := ch7233gx_ok
  unfold ch7233gx at h2
  rw [CFSG.KC.Misc.RuBase.bIf_eq, if_pos h1] at h2
  exact Bool.false_ne_true h2

theorem conj_k16_u32K : ∀ i, k16 * v32 i * k16⁻¹ ∈ uV32p := by
  intro i
  have h := CFSG.KC.Misc.RuBase.allN_iff.1 ch7233kv_ok i i.2
  rw [sB] at h
  have hk := ptR_wF (w := k16W) (by decide)
  exact mem_of_inSp pV32p ebasisK.2.2.2.2.2.2
    (ruP.mul_mem (ruP.mul_mem (wG_mem _) (wG_mem _)) (ruP.inv_mem (wG_mem _)))
    (ptR_comp (ptR_comp hk.1 (p32 i i.2)) hk.2) h

theorem cd_all : ∀ i < 20, ch7233cd_ i = true := by
  intro i hi
  interval_cases i
  · exact ch7233cd_0
  · exact ch7233cd_1
  · exact ch7233cd_2
  · exact ch7233cd_3
  · exact ch7233cd_4
  · exact ch7233cd_5
  · exact ch7233cd_6
  · exact ch7233cd_7
  · exact ch7233cd_8
  · exact ch7233cd_9
  · exact ch7233cd_10
  · exact ch7233cd_11
  · exact ch7233cd_12
  · exact ch7233cd_13
  · exact ch7233cd_14
  · exact ch7233cd_15
  · exact ch7233cd_16
  · exact ch7233cd_17
  · exact ch7233cd_18
  · exact ch7233cd_19

theorem conj64W_letters : ∀ i < 20, ∀ l ∈ conj64W.getD i [], l ≠ 0 ∧ l.natAbs ≤ 6 := by
  decide

theorem conj64_distinctK {i j : Nat} (hi : i < 20) (hj : j < 20) (hij : i ≠ j) :
    u64.map (MulAut.conj (wG (conj64W.getD i []))).toMonoidHom ≠
      u64.map (MulAut.conj (wG (conj64W.getD j []))).toMonoidHom := by
  intro heq
  have h := CFSG.KC.Misc.RuBase.allN_iff.1 (cd_all i hi) j hj
  rw [CFSG.KC.Misc.RuBase.bIf_eq, if_neg (by rw [Nat.beq_eq]; exact hij)] at h
  obtain ⟨k, hk, h⟩ := anyK_iff.1 h
  rw [sB] at h
  beta_reduce at h
  rw [CFSG.KC.Misc.RuBase.bIf_eq] at h
  have hci := ptR_wF (conj64W_letters i hi)
  have hcj := ptR_wF (conj64W_letters j hj)
  set ci := wG (conj64W.getD i []) with hci'
  set cj := wG (conj64W.getD j []) with hcj'
  have hmi : ci * v64 ⟨k, hk⟩ * ci⁻¹ ∈ u64.map (MulAut.conj ci).toMonoidHom :=
    ⟨v64 ⟨k, hk⟩, Subgroup.subset_closure ⟨⟨k, hk⟩, rfl⟩, rfl⟩
  rw [heq] at hmi
  obtain ⟨y, hy, hye⟩ := hmi
  have hye' : cj * y * cj⁻¹ = ci * v64 ⟨k, hk⟩ * ci⁻¹ := hye
  have ey : y = cj⁻¹ * (ci * (wG (basis64W.getD k []) * (ci⁻¹ * cj))) := by
    calc y = cj⁻¹ * (cj * y * cj⁻¹) * cj := by group
      _ = cj⁻¹ * (ci * v64 ⟨k, hk⟩ * ci⁻¹) * cj := by rw [hye']
      _ = _ := by
        change cj⁻¹ * (ci * wG (basis64W.getD k []) * ci⁻¹) * cj = _
        group
  rw [ey] at hy
  have hin := inSp_of_mem p64 ebasisK.2.1
    (ptR_comp hcj.2 (ptR_comp hci.1 (ptR_comp (p64 k hk) (ptR_comp hci.2 hcj.1)))) hy
  split_ifs at h with hin'
  all_goals first | exact Bool.false_ne_true h | exact hin' hin | exact absurd hin hin'

theorem ns_memP : ∀ g ∈ [ruNs0, ruNs1], g ∈ ruP := by
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact ruNs0_mem'
  · exact ruNs1_mem'

theorem ns_memN : ∀ g ∈ [ruNs0, ruNs1], g ∈ ruN := by
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact ruNs0_memN
  · exact ruNs1_memN

theorem cs_memP : ∀ g ∈ [ruC0, ruC1], g ∈ ruP := by
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact ruC0_mem
  · exact ruC1_mem

theorem ruKGens_getD (a : Nat) :
    ruKGens.getD a 1 = evalSigned [ruNs0, ruNs1] (ruKWords.getD a []) := by
  rw [ruKGens, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ruKWords[a]? <;> rfl

theorem ruJGens_getD (k : Nat) :
    ruJGens.getD k 1 = evalSigned [ruC0, ruC1] (ruJWords.getD k []) := by
  rw [ruJGens, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ruJWords[k]? <;> rfl

theorem kG_mem (a : Nat) : ruKGens.getD a 1 ∈ ruP := by
  rw [ruKGens_getD]
  exact evalSigned_mem ns_memP _

theorem ruKWords_letters : ∀ a < 8, ∀ l ∈ ruKWords.getD a [], l ≠ 0 ∧ l.natAbs ≤ 2 := by decide

theorem ruJWords_letters : ∀ k < 6, ∀ l ∈ ruJWords.getD k [], l ≠ 0 ∧ l.natAbs ≤ 2 := by decide

theorem ptR_kF {a : Nat} (ha : a < 8) :
    PtR (kF a) (ruKGens.getD a 1) ∧ PtR (kFI a) (ruKGens.getD a 1)⁻¹ := by
  rw [ruKGens_getD]
  exact ptR_wAp (ptR_pk2 prep_Ns0 prep_Ns1) (ptR_pk2I prep_Ns0I prep_Ns1I) _
    (ruKWords_letters a ha)

theorem ptR_commF {A AI B BI : Nat → Nat} {a b : Equiv.Perm (Fin 4060)} (hA : PtR A a)
    (hAI : PtR AI a⁻¹) (hB : PtR B b) (hBI : PtR BI b⁻¹) :
    PtR (commF A AI B BI) (a * b * a⁻¹ * b⁻¹) := by
  have h := ptR_comp hA (ptR_comp hB (ptR_comp hAI hBI))
  have e : a * (b * (a⁻¹ * b⁻¹)) = a * b * a⁻¹ * b⁻¹ := by group
  rw [e] at h
  exact h

theorem cm_mem {a b : Equiv.Perm (Fin 4060)} (ha : a ∈ ruP) (hb : b ∈ ruP) :
    a * b * a⁻¹ * b⁻¹ ∈ ruP :=
  ruP.mul_mem (ruP.mul_mem (ruP.mul_mem ha hb) (ruP.inv_mem ha)) (ruP.inv_mem hb)

theorem ruK_sq_commK {a b : Nat} (ha : a < 8) (hb : b < 8) :
    ruKGens.getD a 1 * ruKGens.getD a 1 ∈ uE ∧
      ruKGens.getD a 1 * ruKGens.getD b 1 * (ruKGens.getD a 1)⁻¹ * (ruKGens.getD b 1)⁻¹ ∈ uE := by
  have h := CFSG.KC.Misc.RuBase.allN_iff.1 ch7233ke_ok a ha
  simp only [CFSG.KC.Misc.RuBase.bAnd_eq', Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have h3 := CFSG.KC.Misc.RuBase.allN_iff.1 h2 b hb
  have hA := ptR_kF ha
  have hB := ptR_kF hb
  exact ⟨mem_of_inSp pE ebasisK.1 (ruP.mul_mem (kG_mem a) (kG_mem a)) (ptR_comp hA.1 hA.1) h1,
    mem_of_inSp pE ebasisK.1 (cm_mem (kG_mem a) (kG_mem b)) (ptR_commF hA.1 hA.2 hB.1 hB.2) h3⟩

theorem vE_commK :
    vE 0 = ruKGens.getD 3 1 * ruKGens.getD 4 1 * (ruKGens.getD 3 1)⁻¹ * (ruKGens.getD 4 1)⁻¹ ∧
    vE 1 = ruKGens.getD 3 1 * ruKGens.getD 1 1 * (ruKGens.getD 3 1)⁻¹ * (ruKGens.getD 1 1)⁻¹ ∧
    vE 2 = ruKGens.getD 4 1 * ruKGens.getD 0 1 * (ruKGens.getD 4 1)⁻¹ *
      (ruKGens.getD 0 1)⁻¹ := by
  have h := ch7233kb_ok
  unfold ch7233kb at h
  simp only [CFSG.KC.Misc.RuBase.bAnd_eq', Bool.and_eq_true] at h
  obtain ⟨h0, h1, h2⟩ := h
  have k0 := ptR_kF (a := 0) (by norm_num)
  have k1 := ptR_kF (a := 1) (by norm_num)
  have k3 := ptR_kF (a := 3) (by norm_num)
  have k4 := ptR_kF (a := 4) (by norm_num)
  exact ⟨(eq_of_img4 bF hbsJ (cm_mem (kG_mem 3) (kG_mem 4)) (wG_mem _)
      (ptR_commF k3.1 k3.2 k4.1 k4.2) (pE 0 (by norm_num)) (Nat.eq_of_beq_eq_true h0)).symm,
    (eq_of_img4 bF hbsJ (cm_mem (kG_mem 3) (kG_mem 1)) (wG_mem _)
      (ptR_commF k3.1 k3.2 k1.1 k1.2) (pE 1 (by norm_num)) (Nat.eq_of_beq_eq_true h1)).symm,
    (eq_of_img4 bF hbsJ (cm_mem (kG_mem 4) (kG_mem 0)) (wG_mem _)
      (ptR_commF k4.1 k4.2 k0.1 k0.2) (pE 2 (by norm_num)) (Nat.eq_of_beq_eq_true h2)).symm⟩

theorem ptR_AX : (∀ k < 2, PtR (AX k) ([xE, nE * xE * nE⁻¹].getD k 1)) ∧
    ∀ k < 2, PtR (AXI k) ([xE, nE * xE * nE⁻¹].getD k 1)⁻¹ := by
  have hx : PtR (apP (Q 10)) xE ∧ PtR (apP (Q 11)) xE⁻¹ := ptR_QW (k := 10) (Or.inl rfl)
  have hn : PtR (wF nEW) nE ∧ PtR (wFI nEW) nE⁻¹ := ptR_wF (by decide)
  have e : (nE * xE * nE⁻¹)⁻¹ = nE * xE⁻¹ * nE⁻¹ := by group
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · interval_cases k
    · exact hx.1
    · have h : PtR (fun x => wF nEW (apP (Q 10) (wFI nEW x))) (nE * xE * nE⁻¹) := fun x => by
        change wF nEW (apP (Q 10) (wFI nEW x)) = _
        rw [hn.2 x, hx.1 _, hn.1 _, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
      exact h
  · interval_cases k
    · exact hx.2
    · have h : PtR (fun x => wF nEW (apP (Q 11) (wFI nEW x))) (nE * xE⁻¹ * nE⁻¹) := fun x => by
        change wF nEW (apP (Q 11) (wFI nEW x)) = _
        rw [hn.2 x, hx.2 _, hn.1 _, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
      change PtR (AXI 1) (nE * xE * nE⁻¹)⁻¹
      rw [e]
      exact h

theorem xs_memP : ∀ g ∈ [xE, nE * xE * nE⁻¹], g ∈ ruP := by
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact wG_mem _
  · exact ruP.mul_mem (ruP.mul_mem (wG_mem _) (wG_mem _)) (ruP.inv_mem (wG_mem _))

theorem ruNs_wordsK : ruNs0 = evalSigned [xE, nE * xE * nE⁻¹] (nsInXW.getD 0 []) ∧
    ruNs1 = evalSigned [xE, nE * xE * nE⁻¹] (nsInXW.getD 1 []) := by
  have h := ch7233ns_ok
  unfold ch7233ns at h
  simp only [CFSG.KC.Misc.RuBase.bAnd_eq', Bool.and_eq_true] at h
  obtain ⟨h0, h1⟩ := h
  exact ⟨(eq_of_img4 bF hbsJ (evalSigned_mem xs_memP _) ruNs0_mem'
      (ptR_wAp ptR_AX.1 ptR_AX.2 _ (by decide)).1 (ptR_apP prep_Ns0)
      (Nat.eq_of_beq_eq_true h0)).symm,
    (eq_of_img4 bF hbsJ (evalSigned_mem xs_memP _) ruNs1_mem'
      (ptR_wAp ptR_AX.1 ptR_AX.2 _ (by decide)).1 (ptR_apP prep_Ns1)
      (Nat.eq_of_beq_eq_true h1)).symm⟩

theorem commut_not_centK :
    x32 * cQ * x32⁻¹ * cQ⁻¹ ∉ Subgroup.centralizer (u32 : Set (Equiv.Perm (Fin 4060))) := by
  intro hc
  have h := ch7233cq_ok
  unfold ch7233cq at h
  obtain ⟨i, hi, h⟩ := anyK_iff.1 h
  rw [sB] at h
  beta_reduce at h
  rw [CFSG.KC.Misc.RuBase.bIf_eq] at h
  have hx : PtR (apP (Q 14)) x32 ∧ PtR (apP (Q 15)) x32⁻¹ :=
    ptR_QW (k := 14) (Or.inr (Or.inr (Or.inl rfl)))
  have hq : PtR (wF cQW) cQ ∧ PtR (wFI cQW) cQ⁻¹ := ptR_wF (by decide)
  have hC := ptR_commF hx.1 hx.2 hq.1 hq.2
  have hv := p32 i hi
  have hcomm := Subgroup.mem_centralizer_iff.mp hc (wG (basis32W.getD i []))
    (Subgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩)
  have hB := ptR_comp hv hC
  rw [hcomm] at hB
  have e := img4_eq_of_eq (ptR_comp hC hv) hB
  rw [if_pos (by rw [Nat.beq_eq]; exact e)] at h
  exact Bool.false_ne_true h

theorem ptR_jA : (∀ k < 6, PtR (jA k) (ruJGens.getD k 1)) ∧
    ∀ k < 6, PtR (jAI k) (ruJGens.getD k 1)⁻¹ := by
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · rw [ruJGens_getD]
    exact (ptR_wAp (ptR_pk2 prep_C0 prep_C1) (ptR_pk2I prep_C0I prep_C1I) _
      (ruJWords_letters k hk)).1
  · rw [ruJGens_getD]
    exact (ptR_wAp (ptR_pk2 prep_C0 prep_C1) (ptR_pk2I prep_C0I prep_C1I) _
      (ruJWords_letters k hk)).2

theorem cQ_memJK : cQ ∈ ruJ := by
  have h := ch7233cj_ok
  unfold ch7233cj at h
  have hJP : ∀ g ∈ ruJGens, g ∈ ruP := fun g hg => by
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
    exact evalSigned_mem cs_memP w
  have hJ : ∀ g ∈ ruJGens, g ∈ ruJ := fun g hg => Subgroup.subset_closure hg
  have e := eq_of_img4 bF hbsJ (evalSigned_mem hJP cQJW) (wG_mem cQW)
    (ptR_wAp ptR_jA.1 ptR_jA.2 cQJW (by decide)).1 (ptR_wF (w := cQW) (by decide)).1
    (Nat.eq_of_beq_eq_true h)
  change wG cQW ∈ ruJ
  rw [← e]
  exact evalSigned_mem hJ _

theorem eNW_letters : ∀ i < 3, ∀ l ∈ eNW.getD i [], l ≠ 0 ∧ l.natAbs ≤ 2 := by decide

theorem vE_conjK (i : Fin 3) : ∃ m ∈ ruN, m * ruZ * m⁻¹ = vE i := by
  have h := CFSG.KC.Misc.RuBase.allN_iff.1 ch7233ee_ok i i.2
  have hw := ptR_wAp (ptR_pk2 prep_Ns0 prep_Ns1) (ptR_pk2I prep_Ns0I prep_Ns1I)
    (eNW.getD i []) (eNW_letters i i.2)
  have hm := evalSigned_mem ns_memP (eNW.getD i [])
  refine ⟨_, evalSigned_mem ns_memN (eNW.getD i []), ?_⟩
  have hP := pE i i.2
  rw [Nat.zero_add] at hP
  exact eq_of_img4 bF hbsJ (ruP.mul_mem (ruP.mul_mem hm ruZ_mem) (ruP.inv_mem hm)) (wG_mem _)
    (ptR_comp (ptR_comp hw.1 ptR_Z) hw.2) hP (Nat.eq_of_beq_eq_true h).symm

theorem evalSigned_congr {M : Type*} [Group M] {gens gens' : List M} :
    ∀ {w : List ℤ}, (∀ l ∈ w, gens.getD (l.natAbs - 1) 1 = gens'.getD (l.natAbs - 1) 1) →
      evalSigned gens w = evalSigned gens' w
  | [], _ => rfl
  | l :: w, h => by
    rw [evalSigned_cons, evalSigned_cons, h l List.mem_cons_self,
      evalSigned_congr fun l' hl' => h l' (List.mem_cons_of_mem _ hl')]

theorem getD_ab {α : Type*} (a b : α) (l : List α) (d : α) :
    (a :: b :: l).getD 0 d = [a, b].getD 0 d ∧ (a :: b :: l).getD 1 d = [a, b].getD 1 d :=
  ⟨rfl, rfl⟩

theorem wG_eq_ab {w : List ℤ} (hw : ∀ l ∈ w, l.natAbs ≤ 2) :
    wG w = evalSigned [ruA0, ruA1] w := by
  have hg := getD_ab ruA0 ruA1 [ruC0, ruC1, ruNs0, ruNs1] 1
  refine evalSigned_congr fun l hl => ?_
  have h2 := hw l hl
  rcases (by omega : l.natAbs - 1 = 0 ∨ l.natAbs - 1 = 1) with e | e
  · rw [e]
    exact hg.1
  · rw [e]
    exact hg.2

theorem hW_letters : ∀ l ∈ hWordsZ.getD 0 [], l ≠ 0 ∧ l.natAbs ≤ 2 := by decide +kernel

theorem conj30W_letters :∀ w < 30, ∀ l ∈ conj30W.getD w [], l ≠ 0 ∧ l.natAbs ≤ 6 := by decide

theorem conj30W_C :
    ∀ w < 30, (conj30W.getD w []).all (fun l => l.natAbs == 3 || l.natAbs == 4) = true := by
  decide

theorem exists_conj_r30K {v : Equiv.Perm (Fin 4060)} (hv : v ∈ u32) (h1 : v ≠ 1)
    (hz : v ≠ ruZ) : ∃ c ∈ ruC, c * (evalSigned [ruA0, ruA1] (hWordsZ.getD 0 []) * ruZ *
      (evalSigned [ruA0, ruA1] (hWordsZ.getD 0 []))⁻¹) * c⁻¹ = v := by
  obtain ⟨m, hm, rfl⟩ := exists_mProd ebasisK.2.2.2.2.1 hv
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact h1 (mProd_zero _ _)
  have h := CFSG.KC.Misc.RuBase.allN_iff.1 ch7233r30_ok (m - 1) (by omega)
  have e : Nat.succ (m - 1) = m := by omega
  rw [sB] at h
  beta_reduce at h
  rw [e, CFSG.KC.Misc.RuBase.bIf_eq] at h
  have hP := ptR_mAp m p32
  have hmP := mProd_mem bF hbsJ (wGv_mem basis32W) m 5
  split_ifs at h with hzI
  · exact absurd (eq_of_img4 bF hbsJ hmP ruZ_mem hP ptR_Z (Nat.eq_of_beq_eq_true hzI)) hz
  · obtain ⟨w, hw, h⟩ := anyK_iff.1 h
    have hc := ptR_wF (conj30W_letters w hw)
    have hh := ptR_wF (w := hWordsZ.getD 0 []) fun l hl => ⟨(hW_letters l hl).1,
      le_trans (hW_letters l hl).2 (by norm_num)⟩
    have hr : PtR rt (wG (hWordsZ.getD 0 []) * ruZ * (wG (hWordsZ.getD 0 []))⁻¹) := fun x => by
      change wF (hWordsZ.getD 0 []) (apP RuG.Z (wFI (hWordsZ.getD 0 []) x)) = _
      rw [hh.2 x, ptR_Z _, hh.1 _, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    have hrP : wG (hWordsZ.getD 0 []) * ruZ * (wG (hWordsZ.getD 0 []))⁻¹ ∈ ruP :=
      ruP.mul_mem (ruP.mul_mem (wG_mem _) ruZ_mem) (ruP.inv_mem (wG_mem _))
    refine ⟨wG (conj30W.getD w []), wG_memC (conj30W_C w hw), ?_⟩
    rw [← wG_eq_ab fun l hl => (hW_letters l hl).2]
    exact eq_of_img4 bF hbsJ (ruP.mul_mem (ruP.mul_mem (wG_mem _) hrP) (ruP.inv_mem (wG_mem _)))
      hmP (ptR_comp (ptR_comp hc.1 hr) hc.2) hP (Nat.eq_of_beq_eq_true h)

end Facts

end CertificateChecks.KernelMisc.RuBigZ

end
