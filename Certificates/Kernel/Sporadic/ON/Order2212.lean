
module

public import Certificates.Kernel.Sporadic.ON.Levels
public import Certificates.Kernel.Sporadic.ON.Minus2124
public import CFSG.Certificates.Kernel.Spor.ONMvSound
public import CFSG.Sporadic.ON.Chain
public import CFSG.Sporadic.Schreier.ONCheckChainInputs
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.NormNum
public import CFSG.Sporadic.Th.F2Spec

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.F3.Native CFSG.Sporadic.Fi23.Native
open CFSG.Sporadic.ON CFSG.Sporadic.ON.Native CFSG.ONSchreier.Native CFSG.Monster.B.Co2

@[expose] noncomputable def Pq (i : Nat) : Vec := vecOf (wOfK (key ONV.K i))

theorem colsA_bind : (CFSG.Sporadic.ON.Native.colsA ()).size = 154 ∧ ONV.LA.length = 154 ∧
    ∀ j < 154, (CFSG.Sporadic.ON.Native.colsA ())[j]! = wOfK (ONV.LA.getD j 0) := by
  unfold CFSG.Sporadic.ON.Native.colsA rowsA
  exact cols_of ONSeedA.eq colsAK (list_eq ONV.LA ONV.CA (allN_spec listA)) rfl

theorem colsB_bind : (CFSG.Sporadic.ON.Native.colsB ()).size = 154 ∧ ONV.LB.length = 154 ∧
    ∀ j < 154, (CFSG.Sporadic.ON.Native.colsB ())[j]! = wOfK (ONV.LB.getD j 0) := by
  unfold CFSG.Sporadic.ON.Native.colsB rowsB
  exact cols_of ONSeedB.eq colsBK (list_eq ONV.LB ONV.CB (allN_spec listB)) rfl

theorem mv_facts {h : Nat} (hh : h < 245520) : tab ONV.A h < 245520 ∧ tab ONV.B h < 245520 ∧
    key ONV.K (tab ONV.A h) = mv ONV.LA (key ONV.K h) ∧
    key ONV.K (tab ONV.B h) = mv ONV.LB (key ONV.K h) := by
  have e := pt_of mvAll (fun _ => rfl) h hh
  unfold mvAt at e
  simp only [strictB_eq'] at e
  obtain ⟨-, h1, h2, h3, h4⟩ := (by simpa only [bAnd_iff] using e :
    canon (key ONV.K h) = true ∧ Nat.blt (tab ONV.A h) 245520 = true ∧
    Nat.blt (tab ONV.B h) 245520 = true ∧
    Nat.beq (key ONV.K (tab ONV.A h)) (mv ONV.LA (key ONV.K h)) = true ∧
    Nat.beq (key ONV.K (tab ONV.B h)) (mv ONV.LB (key ONV.K h)) = true)
  exact ⟨Nat.blt_eq ▸ h1, Nat.blt_eq ▸ h2, Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4⟩

theorem ga_smul_Pq {i : Nat} (hi : i < 245520) : ga • Pq i = Pq (tab ONV.A i) := by
  have hc := canon_key i hi
  rw [smul_vec, mat_ga, ← toMat_rowsA, Pq, Pq, (mv_facts hi).2.2.1,
    ← mv_sound colsA_bind (canon_of colsAK (list_eq ONV.LA ONV.CA (allN_spec listA))) hc]
  unfold CFSG.Sporadic.ON.Native.colsA
  exact (vecOf_mulVecT (rowsA ()) (wf_of_canon154 (canon_sound hc))).symm

theorem gb_smul_Pq {i : Nat} (hi : i < 245520) : gb • Pq i = Pq (tab ONV.B i) := by
  have hc := canon_key i hi
  rw [smul_vec, mat_gb, ← toMat_rowsB, Pq, Pq, (mv_facts hi).2.2.2,
    ← mv_sound colsB_bind (canon_of colsBK (list_eq ONV.LB ONV.CB (allN_spec listB))) hc]
  unfold CFSG.Sporadic.ON.Native.colsB
  exact (vecOf_mulVecT (rowsB ()) (wf_of_canon154 (canon_sound hc))).symm

theorem Pq_injective {i j : Nat} (hi : i < 245520) (hj : j < 245520) (h : Pq i = Pq j) : i = j :=
  sort_distinct (pt_of sortAll fun _ => rfl) i hi j hj
    (wOfK_inj (canon_key i hi) (canon_key j hj)
      (vecOf_inj (canon_sound (canon_key i hi)) (canon_sound (canon_key j hj)) h))

@[expose] noncomputable def qSet : Set Vec := Pq '' Set.Iio 245520

theorem smul_mem_qSet (g : J) : ∀ v ∈ qSet, g • v ∈ qSet := by
  refine CFSG.Sporadic.Th.smul_mem_of_closure closure_gab ((Set.finite_Iio 245520).image _) ?_ ?_ g
  · rintro _ ⟨i, hi, rfl⟩
    exact ⟨_, (mv_facts hi).1, (ga_smul_Pq hi).symm⟩
  · rintro _ ⟨i, hi, rfl⟩
    exact ⟨_, (mv_facts hi).2.1, (gb_smul_Pq hi).symm⟩

@[expose] noncomputable def qSub : SubMulAction J Vec where
  carrier := qSet
  smul_mem' g _ hv := smul_mem_qSet g _ hv

@[expose] noncomputable def qEquiv : Fin 245520 ≃ qSub :=
  Equiv.ofBijective (fun i => ⟨Pq i, ⟨i, i.isLt, rfl⟩⟩)
    ⟨fun i j h => Fin.ext (Pq_injective i.isLt j.isLt (by simpa using congrArg Subtype.val h)), by
      rintro ⟨v, ⟨i, hi, rfl⟩⟩
      exact ⟨⟨i, hi⟩, rfl⟩⟩

@[expose] noncomputable def rho : J →* Equiv.Perm (Fin 245520) :=
  (Equiv.permCongrHom qEquiv.symm).toMonoidHom.comp (MulAction.toPermHom J qSub)

theorem rho_apply (g : J) (i : Fin 245520) : Pq (rho g i).val = g • Pq i.val := by
  have e : qEquiv (rho g i) = g • qEquiv i := by
    unfold rho
    simp [Equiv.permCongrHom, Equiv.permCongr_apply]
  have := congrArg Subtype.val e
  exact this

theorem rho_tab {g : J} {T : Nat → Nat} (hT : ∀ i < 245520, T i < 245520 ∧ g • Pq i = Pq (T i))
    (i : Fin 245520) : (rho g i).val = T i.val := by
  apply Pq_injective (rho g i).isLt (hT i.val i.isLt).1
  rw [rho_apply, (hT i.val i.isLt).2]

theorem perm_eq {t : Array Nat} {T : Nat → Nat} (ht : t = Array.ofFn (n := 245520) fun i => T i.val)
    {g : Equiv.Perm (Fin 245520)} (hg : ∀ i : Fin 245520, (g i).val = T i.val)
    (hinv : ∀ i < 245520, T i < 245520) (hinj : ∀ i < 245520, ∀ j < 245520, T i = T j → i = j) :
    permOfArr 245520 t = g := by
  have hc : (∀ i < 245520, t[i]! < 245520) ∧ ∀ i < 245520, ∀ j < 245520, t[i]! = t[j]! → i = j := by
    subst ht
    refine ⟨fun i hi => ?_, fun i hi j hj h => ?_⟩
    · rw [getElem!_ofFn_nat _ hi]
      exact hinv i hi
    · rw [getElem!_ofFn_nat _ hi, getElem!_ofFn_nat _ hj] at h
      exact hinj i hi j hj h
  ext x
  rw [permOfArr, dite_eq_left hc]
  simp only [Equiv.ofBijective_apply]
  rw [hg x]
  subst ht
  rw [getElem!_ofFn_nat _ x.isLt]

theorem tabA_inj : ∀ i < 245520, ∀ j < 245520, tab ONV.A i = tab ONV.A j → i = j := by
  intro i hi j hj h
  apply Pq_injective hi hj
  have := congrArg (fun k => ga⁻¹ • Pq k) h
  simp only [← ga_smul_Pq hi, ← ga_smul_Pq hj, inv_smul_smul] at this
  exact this

theorem tabB_inj : ∀ i < 245520, ∀ j < 245520, tab ONV.B i = tab ONV.B j → i = j := by
  intro i hi j hj h
  apply Pq_injective hi hj
  have := congrArg (fun k => gb⁻¹ • Pq k) h
  simp only [← gb_smul_Pq hi, ← gb_smul_Pq hj, inv_smul_smul] at this
  exact this

theorem card_ab_le :
    Nat.card (Subgroup.closure ({permOfArr 245520 (natTab (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits)).alpha),
      permOfArr 245520 (natTab (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits)).beta)} :
        Set (Equiv.Perm (Fin 245520)))) ≤ 460815505920 := by
  obtain ⟨ha, hb⟩ := orb_tabs mvAll ordAll sortAll
  have e1 : permOfArr 245520 (natTab (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits)).alpha) = rho ga :=
    perm_eq ha (rho_tab fun i hi => ⟨(mv_facts hi).1, ga_smul_Pq hi⟩) (fun i hi => (mv_facts hi).1) tabA_inj
  have e2 : permOfArr 245520 (natTab (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits)).beta) = rho gb :=
    perm_eq hb (rho_tab fun i hi => ⟨(mv_facts hi).2.1, gb_smul_Pq hi⟩) (fun i hi => (mv_facts hi).2.1) tabB_inj
  rw [e1, e2]
  have hle : Subgroup.closure ({rho ga, rho gb} : Set (Equiv.Perm (Fin 245520))) ≤ rho.range := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨ga, rfl⟩
    · exact ⟨gb, rfl⟩
  have hJ : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J]; norm_num)
  calc Nat.card (Subgroup.closure ({rho ga, rho gb} : Set (Equiv.Perm (Fin 245520))))
      ≤ Nat.card rho.range := Subgroup.card_le_of_le hle
    _ ≤ Nat.card J := Nat.card_le_card_of_surjective _ rho.rangeRestrict_surjective
    _ = 460815505920 := card_J

theorem orbit_sizes : cOrbitSizes 245520 CFSG.ONSchreier.qonStrongArrs CFSG.ONSchreier.Data.baseList.toArray =
    [245520, 52136, 36] ++ List.replicate 26 1 := by
  unfold cOrbitSizes
  rw [cLevels_eq']
  simp only [Array.toList_ofFn, List.map_ofFn, Function.comp_def, Array.size_ofFn]
  decide

theorem facts2212 : pointChainOK nPts 2 CFSG.ONSchreier.qonStrongArrs CFSG.ONSchreier.Data.baseList.toArray
      CFSG.ONSchreier.Data.strongWords 4 = true ∧
    cOrbitSizes nPts CFSG.ONSchreier.qonStrongArrs CFSG.ONSchreier.Data.baseList.toArray =
      [245520, 52136, 36] ++ List.replicate 26 1 := by
  refine ⟨?_, orbit_sizes⟩
  obtain ⟨w1, w2, w3⟩ := words_ok
  unfold CFSG.ONSchreier.qonStrongArrs
  refine pointChainOK_of_card ⟨by rw [w1]; norm_num, w2.1, w2.2, fun j hj h2 => (w3 j (by rw [w1] at hj; exact hj) h2).2.2⟩
    ?_ ?_ ?_
  · intro j hj
    have hS := qon_SA
    unfold CFSG.ONSchreier.qonStrongArrs at hS
    rw [hS] at hj ⊢
    have hj7 : j < 7 := by simpa [SA_size] using hj
    unfold pisInv allBelowN
    rw [Nat.all_eq_finRange_all, List.all_eq_true]
    rintro ⟨x, hx⟩ -
    obtain ⟨p1, -, p3⟩ := perm_facts' x hx j hj7
    simp only [SA_get hj7 hx, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    refine ⟨p1, ?_⟩
    have e := CFSG.KS.CB.pinvCand_get (n := 245520) (T := TT j) (U := UU j) (fun x hx => (perm_facts' x hx j hj7).1)
      (fun x hx => (perm_facts' x hx j hj7).2.2) p1
    unfold SA
    rw [getElem!_pos _ j (by simpa using hj7), Array.getElem_ofFn]
    rw [e, p3]
  · intro i hi
    have hi29 : i < 29 := by rw [base_size] at hi; exact hi
    rw [base_get hi29]
    exact bK_lt hi29
  · have h := card_ab_le
    have e := orbit_sizes
    unfold CFSG.ONSchreier.qonStrongArrs at e
    rw [e]
    refine h.trans (le_of_eq ?_)
    decide

end CertificateChecks.KernelSpor.ON

end
