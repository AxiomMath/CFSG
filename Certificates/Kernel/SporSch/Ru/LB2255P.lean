
module

public import Certificates.Kernel.SporSch.Ru.LB2255R
public import Certificates.Kernel.SporSch.Ru.LB2255L0
public import Certificates.Kernel.SporSch.Ru.LB2255L1
public import Certificates.Kernel.SporSch.Ru.LB2255L2
public import Certificates.Kernel.SporSch.Ru.LB2255L3
public import Certificates.Kernel.SporSch.Ru.LB2255C0
public import Certificates.Kernel.SporSch.Ru.LB2255C1
public import Certificates.Kernel.SporSch.Ru.LB2255C2
public import Certificates.Kernel.SporSch.Ru.LB2255C3
public import Certificates.Kernel.SporSch.Ru.LFacts
public import Certificates.Kernel.SporSch.Ru.CNFacts
public import CFSG.Certificates.Kernel.SporSch.Ru2255Sound
public import CFSG.Certificates.Kernel.SporSch.RuZWitSound
public import CFSG.Quasithin.Vol2.KGFactC31RuBaseBase
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.SporSch.MathieuBTSplit

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuLB

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Ru2250 CFSG.KS.Ru2255 CFSG.Sporadic.RuSchreier
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.Schreier CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.RuG
  Finset

theorem beq_nat (x y : Nat) : (x == y) = Nat.beq x y := by
  cases e : Nat.beq x y
  · simp only [beq_eq_false_iff_ne]
    exact fun h => absurd (Nat.beq_eq.mpr h) (by simp [e])
  · exact beq_iff_eq.mpr (Nat.eq_of_beq_eq_true e)

theorem prep_of {a : Array Nat} {P : Nat} {g : Equiv.Perm (Fin 4060)} (ha : a = unpack 4060 12 P)
    (h : Rep 4060 a g) : Orb.PRep 4060 12 P g := fun x => by
  rw [← Orb.unpack_get x.2, ← ha]
  exact h x

theorem hPL : ∀ j, 1 ≤ j → j < 593775 →
    ruTreePar[j]! = RuTree.plK j / 16 ∧ ruTreeLab[j]! = RuTree.plK j % 16 := fun j h1 h2 => by
  rw [treePar_get h1 h2, treeLab_get h1 h2]
  exact RuTree.pl_spec h1 h2

theorem jOf_lt {k : Nat} (hk : k < 19) : jOf k < 593775 := by
  interval_cases k <;> decide

theorem g_prep {k : Nat} (hk : k < 19) : Orb.PRep 4060 12 (gT (jOf k)) (ruTElt 64 (jOf k)) :=
  pw_prep hPL (prep_of a0_eq rep_ruA0) (prep_of a1_eq rep_ruA1) 64 _ (jOf_lt hk)

theorem rep_parts {k : Nat} (hk : k < 19) :
    conjK 4060 12 (mask 12) (gT (jOf k)) (TK k) Z = true ∧
      conjRK 4060 12 (mask 12) (gT (jOf k)) A0 (AG k) = true := by
  have h := allN_spec rep k hk
  unfold repOK at h
  rw [PackFld.strictB_eqP] at h
  exact (bAnd_iff _ _).1 h

theorem tk_prep {k : Nat} (hk : k < 19) : Orb.PRep 4060 12 (TK k) (ruTZ (jOf k)) :=
  conjK_sound (g_prep hk) (prep_of z_eq rep_ruZ) (rep_parts hk).1

theorem ag_prep {k : Nat} (hk : k < 19) : Orb.PRep 4060 12 (AG k)
    ((ruTElt 64 (jOf k))⁻¹ * ruA0 * ruTElt 64 (jOf k)) :=
  conjRK_sound (g_prep hk) (prep_of a0_eq rep_ruA0) (rep_parts hk).2

theorem tk_get {k : Nat} (hk : k < 19) {x : Nat} (hx : x < 4060) :
    (ruRepZA k)[x]! = pg 12 (mask 12) (TK k) x := by
  rw [tk_prep hk ⟨x, hx⟩]
  exact rep_ruTZ _ ⟨x, hx⟩

theorem tk_lt {k : Nat} (hk : k < 19) : ∀ x < 4060, pg 12 (mask 12) (TK k) x < 4060 :=
  fun x hx => by
    rw [tk_prep hk ⟨x, hx⟩]
    exact Fin.is_lt _

theorem ruTZ_memP (j : Nat) : ruTZ j ∈ ruP :=
  ruP.mul_mem (ruP.mul_mem (ruTElt_mem 64 j) ruZ_mem) (ruP.inv_mem (ruTElt_mem 64 j))

theorem baseP : BaseFaithful ruP bs4 := CFSG.Quasithin.KGC31.Ru.ruJoin_baseFaithful

theorem comm_eq' {T0 T1 X : Nat} {t : Array Nat} (h0 : ∀ x < 4060, pg 12 (mask 12) T0 x < 4060)
    (h1 : ∀ x < 4060, pg 12 (mask 12) T1 x < 4060) (ht : ∀ x < 4060, t[x]! = pg 12 (mask 12) X x)
    (hX : ∀ x < 4060, pg 12 (mask 12) X x < 4060) :
    ruCommTest (compA 4060 (unpack 4060 12 T0) (unpack 4060 12 T1)) t =
      cmK 4060 12 (mask 12) T0 T1 X := by
  unfold ruCommTest cmK
  refine allLt_eq_allN fun x hx => ?_
  rw [ht x hx, comp_get h1 (hX x hx), comp_get h1 hx, ht _ (tv_lt h0 h1 hx), beq_nat]

theorem centAll : ∀ k < 19, centOK k = true := by
  intro k hk
  have h5 : k % 5 < 5 := Nat.mod_lt _ (by norm_num)
  rcases (by omega : k / 5 = 0 ∨ k / 5 = 1 ∨ k / 5 = 2 ∨ k / 5 = 3) with h | h | h | h
  · have h' := L0.all (k % 5) h5
    have ek : Nat.add (Nat.mul 5 0) (k % 5) = k := by simp only [Nat.add_eq, Nat.mul_eq]; omega
    rwa [cent0, centP, ek] at h'
  · have h' := L1.all (k % 5) h5
    have ek : Nat.add (Nat.mul 5 1) (k % 5) = k := by simp only [Nat.add_eq, Nat.mul_eq]; omega
    rwa [cent1, centP, ek] at h'
  · have h' := L2.all (k % 5) h5
    have ek : Nat.add (Nat.mul 5 2) (k % 5) = k := by simp only [Nat.add_eq, Nat.mul_eq]; omega
    rwa [cent2, centP, ek] at h'
  · have h4 : k % 5 < 4 := by omega
    have h' := L3.all (k % 5) h4
    have ek : Nat.add (Nat.mul 5 3) (k % 5) = k := by simp only [Nat.add_eq, Nat.mul_eq]; omega
    rwa [cent3, centP, ek] at h'

theorem cL0 : rcnt (RuLS.LR 0) = 1820 := Nat.eq_of_beq_eq_true RuL.cnt0
theorem cL1 : rcnt (RuLS.LR 1) = 64 := Nat.eq_of_beq_eq_true RuL.cnt1

theorem cent_eq {k : Nat} (hk : k < 19) : ruCentCount k = ruCentCounts.getD k 0 := by
  have hc := centAll k hk
  unfold centOK at hc
  rw [PackFld.strictB_eqP, PackFld.strictB_eqP] at hc
  have hl : ruLevL = rawLevels 4060 (ruField4060 5) (ruBaseArr 4060 ruLChainBase) := rfl
  have h2 := count2_eq RuL.binds RuLS.head RuLS.hl (le_refl 2)
    (p := fun l => ruCommTest l (ruRepZA k)) (P := pCm k) fun a ha b hb =>
      comm_eq' (tr_lt RuLS.hl (i := 0) (by norm_num) ha) (tr_lt RuLS.hl (i := 1) (by norm_num) hb)
        (fun x hx => tk_get hk hx) (tk_lt hk)
  rw [cL0, cL1] at h2
  rw [← Nat.eq_of_beq_eq_true hc, ruCentCount, ruCentCountOf, hl, h2]
  rfl

theorem cents : (List.range 19).map ruCentCount = ruCentCounts := by
  apply List.ext_getElem (by simp [ruCentCounts])
  intro i h1 _
  simp only [List.length_map, List.length_range] at h1
  rw [List.getElem_map, List.getElem_range, cent_eq h1]
  interval_cases i <;> rfl

theorem ord14_iff {t : Array Nat} {g : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g) :
    ruOrd14 t = true ↔ g ^ 14 = 1 ∧ g ^ 7 ≠ 1 ∧ g ^ 2 ≠ 1 := by
  rw [ruOrd14, Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true',
    eqA_iff (rep_powA ht 14) rep_idA, ← Bool.not_eq_true, ← Bool.not_eq_true,
    eqA_iff (rep_powA ht 7) rep_idA, eqA_iff (rep_powA ht 2) rep_idA, and_assoc]

theorem ord_eq {k : Nat} (hk : k < 19) :
    ruOrd14 (compA 4060 ruA0A (ruRepZA k)) = ord14Exp.getD k false := by
  have hf : ∀ x : Fin 4060, atK k x = (ruA0 * ruTZ (jOf k)) x := fun x => by
    unfold atK
    rw [tk_prep hk x, prep_of a0_eq rep_ruA0, Equiv.Perm.mul_apply]
  have hr : Rep 4060 (ruRepZA k) (ruTZ (jOf k)) := rep_ruTZ _
  have e : ruOrd14 (compA 4060 ruA0A (ruRepZA k)) = ordK (atK k) := by
    apply Bool.eq_iff_iff.mpr
    rw [ord14_iff (rep_compA rep_ruA0 hr),
      ordK_iff (by norm_num) baseP hf (ruP.mul_mem ruA0_mem (ruTZ_memP _))]
  have h := allN_spec ord k hk
  unfold ordOK at h
  rw [e]
  cases e1 : ord14Exp.getD k false <;> rw [e1] at h <;> cases e2 : ordK (atK k) <;>
    rw [e2] at h <;> first | rfl | exact absurd h Bool.false_ne_true

theorem ords : (List.range 19).map (fun k => ruOrd14 (compA 4060 ruA0A (ruRepZA k))) =
    [false, false, false, true, false, false, true, false, false, false, false, true, false,
      false, false, false, false, false, false] := by
  apply List.ext_getElem (by simp)
  intro i h1 _
  simp only [List.length_map, List.length_range] at h1
  rw [List.getElem_map, List.getElem_range, ord_eq h1]
  interval_cases i <;> rfl

theorem cC0' : rcnt (RuCS.LR 0) = 1920 := Nat.eq_of_beq_eq_true RuCNF.cC0
theorem cC1' : rcnt (RuCS.LR 1) = 64 := Nat.eq_of_beq_eq_true RuCNF.cC1
theorem cC2' : rcnt (RuCS.LR 2) = 2 := Nat.eq_of_beq_eq_true RuCNF.cC2

theorem blkAll : ∀ f < 4, ∀ q < 30, blkC (Nat.add (Nat.mul 30 f) q) = true := by
  intro f hf q hq
  rcases (by omega : f = 0 ∨ f = 1 ∨ f = 2 ∨ f = 3) with rfl | rfl | rfl | rfl
  exacts [C0.all q hq, C1.all q hq, C2.all q hq, C3.all q hq]

theorem tot_eq (f : Nat) : totC f = ∑ q ∈ range 30, cntCB (Nat.add (Nat.mul 30 f) q) := by
  unfold totC
  rw [CFSG.KS.SporSch.MBT.foldN_add' (f := fun q s => Nat.add s (cntCB (Nat.add (Nat.mul 30 f) q)))
      (g := fun q => cntCB (Nat.add (Nat.mul 30 f) q)) (fun q s => rfl),
    Nat.zero_add]

theorem countC_of {f : Nat} (hf : f < 4) {p : Array Nat → Bool}
    (hP : ∀ a < rcnt (RuCS.LR 0), ∀ b < rcnt (RuCS.LR 1), ∀ c < rcnt (RuCS.LR 2),
      p (compA 4060 (compA 4060 (unpack 4060 12 (RuCS.TR (Nat.add (oC 0) a)))
        (unpack 4060 12 (RuCS.TR (Nat.add (oC 1) b)))) (unpack 4060 12 (RuCS.TR (Nat.add (oC 2) c)))) =
      pC f (RuCS.TR (Nat.add (oC 0) a)) (RuCS.TR (Nat.add (oC 1) b)) (RuCS.TR (Nat.add (oC 2) c))) :
    count3 4060 ruLevC p = totC f := by
  have e : (1920 : Nat) = 64 * 30 := rfl
  rw [show ruLevC = rawLevels 4060 (ruField4060 1) (ruBaseArr 4060 ruCBase) from rfl,
    count3_eq RuCNF.bindsC RuCS.head RuCS.hl (le_refl 3) (P := pC f) hP, cC0', cC1', cC2', e,
    cnt3K_blocks, tot_eq]
  refine sum_congr rfl fun q hq => ?_
  have hq' := mem_range.mp hq
  have h := blkAll f hf q hq'
  unfold blkC at h
  rw [PackFld.strictB_eqP, PackFld.strictB_eqP, PackFld.strictB_eqP] at h
  have e1 : Nat.div (Nat.add (Nat.mul 30 f) q) 30 = f := by
    change (30 * f + q) / 30 = f
    omega
  have e2 : Nat.mod (Nat.add (Nat.mul 30 f) q) 30 = q := by
    change (30 * f + q) % 30 = q
    omega
  rw [e1, e2] at h
  exact Nat.eq_of_beq_eq_true h

theorem chainC : ruChainOK 4060 (ruField4060 1) 2 7 ruCBase ruCDerivations = true :=
  RuCNF.factsC.1

theorem lev_size {i a : Nat} (hi : i < 3) (ha : a < rcnt (RuCS.LR i)) :
    a < (ChainArrays.lev 4060 (ruField4060 1) (ruBaseArr 4060 ruCBase) i).pts.size := by
  rw [show ChainArrays.lev 4060 (ruField4060 1) (ruBaseArr 4060 ruCBase) i =
    (rawLevels 4060 (ruField4060 1) (ruBaseArr 4060 ruCBase))[i]! from rfl,
    (levelTr_sound RuCNF.bindsC RuCS.head RuCS.hl hi).1]
  exact ha

theorem compC_rep {a b c : Nat} (ha : a < rcnt (RuCS.LR 0)) (hb : b < rcnt (RuCS.LR 1))
    (hc : c < rcnt (RuCS.LR 2)) : ∃ R ∈ ruP,
      Rep 4060 (compA 4060 (compA 4060 (unpack 4060 12 (RuCS.TR (Nat.add (oC 0) a)))
        (unpack 4060 12 (RuCS.TR (Nat.add (oC 1) b))))
        (unpack 4060 12 (RuCS.TR (Nat.add (oC 2) c)))) R := by
  have hA : ChainArrays ruChainC ((ruField4060 1).extract 0 2) (ruField4060 1)
      (ruBaseArr 4060 ruCBase) (ruWordsArr 2 7 ruCDerivations) := ruChain_arrays chainC
  have h3 : 3 ≤ ruChainC.baseCount := by decide
  have ha' := lev_size (by norm_num) ha
  have hb' := lev_size (by norm_num) hb
  have hc' := lev_size (by norm_num) hc
  refine ⟨ChainArrays.levT 4060 (ruField4060 1) (ruBaseArr 4060 ruCBase) 0 a *
    ChainArrays.levT 4060 (ruField4060 1) (ruBaseArr 4060 ruCBase) 1 b *
    ChainArrays.levT 4060 (ruField4060 1) (ruBaseArr 4060 ruCBase) 2 c, ?_, ?_⟩
  · refine ruC_le ?_
    rw [← ruChainC_sub]
    exact ruChainC.originalSubgroup.mul_mem (ruChainC.originalSubgroup.mul_mem
      (chain_levT_mem_original hA (by norm_num) chainC (by omega) ha')
      (chain_levT_mem_original hA (by norm_num) chainC (by omega) hb'))
      (chain_levT_mem_original hA (by norm_num) chainC (by omega) hc')
  · have hr := chain_rep_prod3A hA chainC h3 ha' hb' hc'
    rwa [show rawLevels 4060 (ruField4060 1) (ruBaseArr 4060 ruCBase) = ruLevC from rfl,
      show ruLevC = rawLevels 4060 (ruField4060 1) (ruBaseArr 4060 ruCBase) from rfl,
      prod3A_eq RuCNF.bindsC RuCS.head RuCS.hl (le_refl 3) ha hb hc] at hr

theorem trC_lt {i a : Nat} (hi : i < 3) (ha : a < rcnt (RuCS.LR i)) :
    ∀ x < 4060, pg 12 (mask 12) (RuCS.TR (Nat.add (oC i) a)) x < 4060 :=
  tr_lt RuCS.hl hi ha

theorem sqC {a b c : Nat} (ha : a < rcnt (RuCS.LR 0)) (hb : b < rcnt (RuCS.LR 1))
    (hc : c < rcnt (RuCS.LR 2)) :
    ruSqZA (compA 4060 (compA 4060 (unpack 4060 12 (RuCS.TR (Nat.add (oC 0) a)))
      (unpack 4060 12 (RuCS.TR (Nat.add (oC 1) b)))) (unpack 4060 12 (RuCS.TR (Nat.add (oC 2) c)))) =
    pSq (RuCS.TR (Nat.add (oC 0) a)) (RuCS.TR (Nat.add (oC 1) b)) (RuCS.TR (Nat.add (oC 2) c)) := by
  rw [ruSqZA, z_eq]
  exact sq_eq (trC_lt (by norm_num) hb) (trC_lt (by norm_num) hc) (trC_lt (by norm_num) ha)

theorem roots : count3 4060 ruLevC ruSqZA = 816 := by
  rw [countC_of (f := 0) (p := ruSqZA) (by norm_num) fun a ha b hb c hc => sqC ha hb hc]
  have T := tot
  simp only [bAnd_iff] at T
  exact Nat.eq_of_beq_eq_true T.1

theorem fibTest_iff {gA giA t : Array Nat} {g r : Equiv.Perm (Fin 4060)} (hg : Rep 4060 gA g)
    (hgi : Rep 4060 giA g⁻¹) (ht : Rep 4060 t r) :
    ruFibTest gA giA t = true ↔ (ruA0 * (g * r * g⁻¹)) ^ 13 = 1 ∧
      (ruA0 * (g * r * g⁻¹) * ruA0 * (g * r * g⁻¹) ^ 2) ^ 29 = 1 := by
  have hx : Rep 4060 (compA 4060 (compA 4060 gA t) giA) (g * r * g⁻¹) :=
    rep_compA (rep_compA hg ht) hgi
  have hax := rep_compA rep_ruA0 hx
  rw [ruFibTest, Bool.and_eq_true, eqA_iff (rep_powA hax 13) rep_idA,
    eqA_iff (rep_powA (rep_compA (rep_compA hax rep_ruA0) (rep_compA hx hx)) 29) rep_idA,
    pow_two]

theorem conj_pow_eq_one {g x : Equiv.Perm (Fin 4060)} (e : ℕ) :
    (g * x * g⁻¹) ^ e = 1 ↔ x ^ e = 1 := by
  rw [conj_pow]
  constructor
  · intro h
    have := congrArg (fun y => g⁻¹ * y * g) h
    simpa [mul_assoc] using this
  · intro h
    rw [h, mul_one, mul_inv_cancel]

theorem fib_iff (g r : Equiv.Perm (Fin 4060)) :
    ((ruA0 * (g * r * g⁻¹)) ^ 13 = 1 ∧ (ruA0 * (g * r * g⁻¹) * ruA0 * (g * r * g⁻¹) ^ 2) ^ 29 = 1) ↔
      ((g⁻¹ * ruA0 * g * r) ^ 13 = 1 ∧
        (g⁻¹ * ruA0 * g * r * (g⁻¹ * ruA0 * g) * (r * r)) ^ 29 = 1) := by
  have e1 : ruA0 * (g * r * g⁻¹) = g * (g⁻¹ * ruA0 * g * r) * g⁻¹ := by group
  have e2 : ruA0 * (g * r * g⁻¹) * ruA0 * (g * r * g⁻¹) ^ 2 =
      g * (g⁻¹ * ruA0 * g * r * (g⁻¹ * ruA0 * g) * (r * r)) * g⁻¹ := by
    rw [pow_two]
    group
  rw [e2, e1, conj_pow_eq_one, conj_pow_eq_one]

private theorem true_and_bAnd {a b : Bool} (h : a = b) : (true && a) = bAnd(true, b) := by
  subst h; rfl

theorem fibC {f : Nat} (hf1 : 1 ≤ f) (hf : f < 4) {a b c : Nat} (ha : a < rcnt (RuCS.LR 0))
    (hb : b < rcnt (RuCS.LR 1)) (hc : c < rcnt (RuCS.LR 2)) :
    (fun r => ruSqZA r && ruFibTest (ruTEltA 64 (ruReps.getD (fRep f) 0))
      (ruTEltInvA 64 (ruReps.getD (fRep f) 0)) r)
      (compA 4060 (compA 4060 (unpack 4060 12 (RuCS.TR (Nat.add (oC 0) a)))
        (unpack 4060 12 (RuCS.TR (Nat.add (oC 1) b)))) (unpack 4060 12 (RuCS.TR (Nat.add (oC 2) c)))) =
    pC f (RuCS.TR (Nat.add (oC 0) a)) (RuCS.TR (Nat.add (oC 1) b)) (RuCS.TR (Nat.add (oC 2) c)) := by
  have hk : fRep f < 19 := by
    rcases (by omega : f = 1 ∨ f = 2 ∨ f = 3) with rfl | rfl | rfl <;> decide
  have hpC : pC f (RuCS.TR (Nat.add (oC 0) a)) (RuCS.TR (Nat.add (oC 1) b))
      (RuCS.TR (Nat.add (oC 2) c)) = pFib (fRep f) (RuCS.TR (Nat.add (oC 0) a))
        (RuCS.TR (Nat.add (oC 1) b)) (RuCS.TR (Nat.add (oC 2) c)) := by
    unfold pC
    have : Nat.beq f 0 = false := by
      cases e : Nat.beq f 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) (by omega)
    rw [this]
  obtain ⟨R, hRm, hR⟩ := compC_rep ha hb hc
  have h0 := trC_lt (by norm_num) ha
  have h1 := trC_lt (by norm_num) hb
  have h2 := trC_lt (by norm_num) hc
  have hR' : ∀ x : Fin 4060, tv3 12 (mask 12) (RuCS.TR (Nat.add (oC 0) a))
      (RuCS.TR (Nat.add (oC 1) b)) (RuCS.TR (Nat.add (oC 2) c)) x = R x := fun x => by
    rw [← comp3_get h1 h2 x.2]
    exact hR x
  dsimp only
  rw [hpC, sqC ha hb hc]
  rw [pFib, pSq]
  cases sqK 4060 12 (mask 12) (RuCS.TR (Nat.add (oC 0) a)) (RuCS.TR (Nat.add (oC 1) b))
      (RuCS.TR (Nat.add (oC 2) c)) Z
  · rfl
  · refine true_and_bAnd ?_
    apply Bool.eq_iff_iff.mpr
    rw [fibTest_iff (rep_ruTElt 64 _) (rep_ruTEltInv 64 _) hR, fib_iff,
      fibK_iff (by norm_num) baseP (ag_prep hk) hR'
        (ruP.mul_mem (ruP.mul_mem (ruP.inv_mem (ruTElt_mem 64 _)) ruA0_mem) (ruTElt_mem 64 _)) hRm]
    rfl

theorem fib_count {f : Nat} (hf1 : 1 ≤ f) (hf : f < 4) : ruFibCount (fRep f) = totC f := by
  unfold ruFibCount ruFibCountOf
  exact countC_of hf fun a ha b hb c hc => fibC hf1 hf ha hb hc

theorem fibs : [ruFibCount 3, ruFibCount 6, ruFibCount 11] = [0, 0, 4] := by
  have T := tot
  simp only [bAnd_iff] at T
  obtain ⟨-, t1, t2, t3⟩ := T
  have h1 := fib_count (f := 1) (by norm_num) (by norm_num)
  have h2 := fib_count (f := 2) (by norm_num) (by norm_num)
  have h3 := fib_count (f := 3) (by norm_num) (by norm_num)
  have r1 : fRep 1 = 3 := rfl
  have r2 : fRep 2 = 6 := rfl
  have r3 : fRep 3 = 11 := rfl
  rw [r1] at h1
  rw [r2] at h2
  rw [r3] at h3
  rw [h1, h2, h3, Nat.eq_of_beq_eq_true t1, Nat.eq_of_beq_eq_true t2, Nat.eq_of_beq_eq_true t3]

theorem facts : (List.range 19).map ruCentCount = ruCentCounts ∧
    (List.range 19).map (fun k => ruOrd14 (compA 4060 ruA0A (ruRepZA k))) =
      [false, false, false, true, false, false, true, false, false, false, false, true, false,
        false, false, false, false, false, false] ∧
    count3 4060 ruLevC ruSqZA = 816 ∧
    [ruFibCount 3, ruFibCount 6, ruFibCount 11] = [0, 0, 4] :=
  ⟨cents, ords, roots, fibs⟩

end CertificateChecks.KernelSporSch.RuLB

end
