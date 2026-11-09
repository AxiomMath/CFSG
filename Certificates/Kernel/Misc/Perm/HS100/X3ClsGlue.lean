module

public import Certificates.Kernel.Misc.Perm.HS100.X3ClsCheck
public import Certificates.Kernel.Misc.Perm.HS100.BaseGlue
public import CFSG.Certificates.Kernel.PCentCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.ThreeCentFix
public import CFSG.RankThree.Native.HSMcLAut
import CFSG.Certificates.Kernel.Misc.ArrEnumUnpack
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.HS100.X3Cls

open CFSG.KC.PCent CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin
open CFSG.KC.Misc.ArrEnum (pp_of_permB)
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem x3band {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  revert h
  cases a <;> cases b <;> decide

theorem x3sz : CFSG.KS.Raw.szOK 100 7 = true := by quickRfl

theorem x3_permOfArr_unpack {q : Nat} (hq : PP 100 7 q) :
    permOfArr 100 (unpack 100 7 q) = toPerm 100 7 q := by
  have h : Rep 100 (unpack 100 7 q) (toPerm 100 7 q) :=
    fun x => by rw [Orb.unpack_get x.2, toPerm_apply hq]
  have hc : (∀ i < 100, (unpack 100 7 q)[i]! < 100) ∧
      ∀ i < 100, ∀ j < 100, (unpack 100 7 q)[i]! = (unpack 100 7 q)[j]! → i = j :=
    ⟨fun i hi => h.lt hi, fun i hi j hj hij => by
      rw [h.apply hi, h.apply hj] at hij
      have := (toPerm 100 7 q).injective (Fin.ext hij)
      simpa using this⟩
  ext x
  rw [permOfArr, dite_eq_left hc]
  change (unpack 100 7 q)[(x : ℕ)]! = _
  exact h x

theorem pp_hsW : ∀ k < 6, PP 100 7 (hsW k) := by
  have h := fun j (hj : j < 3) => pp_of_permB x3sz (Orb.allN_iff.1 x3Perm j hj)
  intro k hk
  interval_cases k
  · exact h 0 (by norm_num)
  · exact h 1 (by norm_num)
  · exact h 2 (by norm_num)
  · exact (h 0 (by norm_num)).inv
  · exact (h 1 (by norm_num)).inv
  · exact (h 2 (by norm_num)).inv

theorem toPerm_hsW0 : toPerm 100 7 (hsW 0) = hs100A := by
  rw [hs100A, hs100Arr_eq 0 (by norm_num)]
  exact (x3_permOfArr_unpack (pp_hsW 0 (by norm_num))).symm

theorem toPerm_hsW1 : toPerm 100 7 (hsW 1) = hs100B := by
  rw [hs100B, hs100Arr_eq 1 (by norm_num)]
  exact (x3_permOfArr_unpack (pp_hsW 1 (by norm_num))).symm

theorem toPerm_hsW2 : toPerm 100 7 (hsW 2) = hs100U := by
  rw [hs100U, hs100Arr_eq 15 (by norm_num)]
  exact (x3_permOfArr_unpack (pp_hsW 2 (by norm_num))).symm

theorem mem_hsW : ∀ k < 6, toPerm 100 7 (hsW k) ∈ hs100R := by
  have hA : hs100A ∈ hs100R := Subgroup.subset_closure (by simp)
  have hB : hs100B ∈ hs100R := Subgroup.subset_closure (by simp)
  have hU : hs100U ∈ hs100R := Subgroup.subset_closure (by simp)
  have i0 : toPerm 100 7 (hsW 3) = hs100A⁻¹ := by
    rw [← toPerm_hsW0, ← toPerm_inv (pp_hsW 0 (by norm_num))]
    rfl
  have i1 : toPerm 100 7 (hsW 4) = hs100B⁻¹ := by
    rw [← toPerm_hsW1, ← toPerm_inv (pp_hsW 1 (by norm_num))]
    rfl
  have i2 : toPerm 100 7 (hsW 5) = hs100U⁻¹ := by
    rw [← toPerm_hsW2, ← toPerm_inv (pp_hsW 2 (by norm_num))]
    rfl
  intro k hk
  interval_cases k
  · rw [toPerm_hsW0]; exact hA
  · rw [toPerm_hsW1]; exact hB
  · rw [toPerm_hsW2]; exact hU
  · rw [i0]; exact inv_mem hA
  · rw [i1]; exact inv_mem hB
  · rw [i2]; exact inv_mem hU

theorem mem_hsW_P : ∀ k < 6, (Nat.blt k 2 || Nat.beq k 3 || Nat.beq k 4) = true →
    toPerm 100 7 (hsW k) ∈ hs100P := by
  have hA : hs100A ∈ hs100P := Subgroup.subset_closure (by simp)
  have hB : hs100B ∈ hs100P := Subgroup.subset_closure (by simp)
  have i0 : toPerm 100 7 (hsW 3) = hs100A⁻¹ := by
    rw [← toPerm_hsW0, ← toPerm_inv (pp_hsW 0 (by norm_num))]
    rfl
  have i1 : toPerm 100 7 (hsW 4) = hs100B⁻¹ := by
    rw [← toPerm_hsW1, ← toPerm_inv (pp_hsW 1 (by norm_num))]
    rfl
  intro k hk hl
  interval_cases k
  · rw [toPerm_hsW0]; exact hA
  · rw [toPerm_hsW1]; exact hB
  · exact absurd hl (by decide)
  · rw [i0]; exact inv_mem hA
  · rw [i1]; exact inv_mem hB
  · exact absurd hl (by decide)

theorem x3_word_in {H : Subgroup (Equiv.Perm (Fin 100))} : ∀ ws : List Nat,
    (∀ c ∈ ws, c < 6 ∧ toPerm 100 7 (hsW c) ∈ H) → toPerm 100 7 (wordK 100 7 hsW ws) ∈ H
  | [], _ => by
    change toPerm 100 7 (pidn 100 7) ∈ H
    rw [toPerm_pidn x3sz]
    exact H.one_mem
  | c :: ws, hc => by
    obtain ⟨hc6, hcH⟩ := hc c List.mem_cons_self
    have hw : ∀ c' ∈ ws, c' < 6 ∧ toPerm 100 7 (hsW c') ∈ H :=
      fun c' h' => hc c' (List.mem_cons_of_mem _ h')
    have h1 := (wordK_sound x3sz pp_hsW ws fun c' h' => (hw c' h').1).1
    change toPerm 100 7 (pcomp 100 7 (mask 7) (hsW c) (wordK 100 7 hsW ws)) ∈ H
    rw [toPerm_mul (pp_hsW c hc6) h1]
    exact H.mul_mem hcH (x3_word_in ws hw)

theorem closure_hsW_le {m : Nat} (hm : m ≤ 6) : Subgroup.closure (gens 100 7 hsW m) ≤ hs100R := by
  rw [Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact mem_hsW k (by omega)

theorem x3_word_mem {ws : List Nat} (hw : allL (fun c => Nat.blt c 6) ws = true) :
    PP 100 7 (wordK 100 7 hsW ws) ∧ toPerm 100 7 (wordK 100 7 hsW ws) ∈ hs100R := by
  have hc : ∀ c ∈ ws, c < 6 := fun c hc => Nat.blt_eq.mp (allL_iff.1 hw c hc)
  obtain ⟨h1, h2⟩ := wordK_sound x3sz pp_hsW ws hc
  exact ⟨h1, closure_hsW_le le_rfl h2⟩

theorem x3_pp_v : PP 100 7 v ∧ toPerm 100 7 v = hs100A * hs100U * (hs100A * hs100U) := by
  have hv := Nat.eq_of_beq_eq_true (x3band x3Cls_bind).2
  have pA := pp_hsW 0 (by norm_num)
  have pU := pp_hsW 2 (by norm_num)
  change PP 100 7 (HX.F 0) at pA
  change PP 100 7 (HX.F 15) at pU
  rw [hv]
  refine ⟨(pA.mul pU).mul (pA.mul pU), ?_⟩
  rw [toPerm_mul (pA.mul pU) (pA.mul pU), toPerm_mul pA pU]
  rw [← toPerm_hsW0, ← toPerm_hsW2]
  rfl

theorem x3_pG_facts : ∀ k < 3, PP 100 7 (pG k) ∧ toPerm 100 7 (pG k) ∈ hs100R ∧
    pg 7 (mask 7) (pG k) p = p := by
  intro k hk
  have h := Orb.allN_iff.1 (x3band x3Cls_bind).1 k hk
  obtain ⟨h12, h3⟩ := x3band h
  obtain ⟨h1, h2⟩ := x3band h12
  rw [Nat.eq_of_beq_eq_true h1]
  rw [Nat.eq_of_beq_eq_true h1] at h3
  obtain ⟨hp, hm⟩ := x3_word_mem h2
  exact ⟨hp, hm, Nat.eq_of_beq_eq_true h3⟩

theorem x3_pC_facts : ∀ k < 4, PP 100 7 (pC k) ∧ toPerm 100 7 (pC k) ∈ hs100R ∧
    toPerm 100 7 (pC k) * toPerm 100 7 v = toPerm 100 7 v * toPerm 100 7 (pC k) := by
  intro k hk
  have h := Orb.allN_iff.1 x3Cent_bind k hk
  obtain ⟨h12, h3⟩ := x3band h
  obtain ⟨h1, h2⟩ := x3band h12
  obtain ⟨hp, hm⟩ := x3_word_mem h2
  rw [← Nat.eq_of_beq_eq_true h1] at hp hm
  refine ⟨hp, hm, ?_⟩
  rw [← toPerm_mul hp x3_pp_v.1, ← toPerm_mul x3_pp_v.1 hp, Nat.eq_of_beq_eq_true h3]

theorem x3_card_fix_v : (Finset.univ.filter fun i : Fin 100 => toPerm 100 7 v i = i).card = 10 := by
  have e : (Finset.univ.filter fun i : Fin 100 => toPerm 100 7 v i = i) =
      Finset.univ.filter fun i : Fin 100 => pg 7 (mask 7) v i = i := by
    refine Finset.filter_congr fun i _ => ?_
    rw [Fin.ext_iff, toPerm_apply x3_pp_v.1]
  rw [e]
  decide +kernel

theorem card_centralizer_AU2 :
    Nat.card ↥(hs100R ⊓ Subgroup.centralizer
      ({hs100A * hs100U * (hs100A * hs100U)} : Set (Equiv.Perm (Fin 100)))) = 720 := by
  rw [← x3_pp_v.2]
  obtain ⟨hp, hpts, hpo, -⟩ := pointOrbK_sound (fun k hk => pp_hsW k (by omega))
    (x3band x3Pt_ok).1
  have hlen : PO.length = 100 := Nat.eq_of_beq_eq_true (x3band x3Pt_ok).2
  have hstab := CFSG.KC.PCent.card_mul_card_stab_le (H := hs100R) (ptsOf 100 PO) fun s hs => by
    obtain ⟨g, hg, he⟩ := hpo s hs
    exact ⟨g, closure_hsW_le (by norm_num) hg, he⟩
  rw [hpts, hlen, card_hs100R] at hstab
  have hfix : toPerm 100 7 v ⟨p, hp⟩ = ⟨p, hp⟩ := by
    refine Fin.ext ?_
    rw [toPerm_apply x3_pp_v.1]
    exact Nat.eq_of_beq_eq_true (x3band x3Cls_len).2
  obtain ⟨S, hS, hS'⟩ := classK_sound (fun k hk => (x3_pG_facts k hk).1) x3_pp_v.1 x3Cls_ok
  have hup := CFSG.EvenSporadicStandard.HSStd.FiveY.card_centralizer_mul_le_fix_mul hs100R hfix S
    fun s hs => by
      obtain ⟨g, hg, he⟩ := hS' s hs
      refine ⟨g, ?_, he⟩
      revert hg
      refine fun hg => (Subgroup.closure_le _).2 ?_ hg
      rintro _ ⟨k, hk, rfl⟩
      obtain ⟨-, hm, hf⟩ := x3_pG_facts k hk
      refine Subgroup.mem_inf.2 ⟨hm, MulAction.mem_stabilizer_iff.2 ?_⟩
      rw [Equiv.Perm.smul_def]
      exact Fin.ext ((toPerm_apply (x3_pG_facts k hk).1 _).trans hf)
  have hRlen : R.length = 12320 := Nat.eq_of_beq_eq_true (x3band x3Cls_len).1
  rw [hS, hRlen, x3_card_fix_v] at hup
  have hlow := prod_le_card_of_stabLowK x3sz (fun k hk => (x3_pC_facts k hk).1) x3Cent_ok
  rw [Nat.eq_of_beq_eq_true x3Cent_len] at hlow
  have hle : Subgroup.closure (gens 100 7 pC 4) ≤
      hs100R ⊓ Subgroup.centralizer ({toPerm 100 7 v} : Set (Equiv.Perm (Fin 100))) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨-, hm, hc⟩ := x3_pC_facts k hk
    exact Subgroup.mem_inf.2 ⟨hm, Subgroup.mem_centralizer_singleton_iff.2 hc⟩
  have hlow' := hlow.trans (Subgroup.card_le_of_le hle)
  omega

theorem x3_pG_P : ∀ k < 3, toPerm 100 7 (pG k) ∈ hs100P := by
  intro k hk
  have h := Orb.allN_iff.1 (x3band x3Cls_bind).1 k hk
  obtain ⟨h12, -⟩ := x3band h
  obtain ⟨h1, h2⟩ := x3band h12
  rw [Nat.eq_of_beq_eq_true h1]
  have h6 := allL_iff.1 h2
  have hab := allL_iff.1 (Orb.allN_iff.1 x3Cls_wAB k hk)
  exact x3_word_in _ fun c hc =>
    ⟨Nat.blt_eq.mp (h6 c hc), mem_hsW_P c (Nat.blt_eq.mp (h6 c hc)) (hab c hc)⟩

theorem x3_arith {c s r : ℕ} (h1 : c * 12320 ≤ 10 * s) (h2 : 100 * s ≤ 44352000)
    (h3 : 720 ≤ r * c) (h4 : r ≤ 2) : c = 360 := by
  have h5 : r * c ≤ 2 * c := Nat.mul_le_mul_right c h4
  omega

theorem card_centralizer_AU2P :
    Nat.card ↥(hs100P ⊓ Subgroup.centralizer
      ({hs100A * hs100U * (hs100A * hs100U)} : Set (Equiv.Perm (Fin 100)))) = 360 := by
  have h720 := card_centralizer_AU2
  rw [← x3_pp_v.2] at h720 ⊢
  obtain ⟨hp, hpts, hpo, -⟩ := pointOrbK_sound (fun k hk => pp_hsW k (by omega))
    (x3band x3Pt_ok).1
  have hlen : PO.length = 100 := Nat.eq_of_beq_eq_true (x3band x3Pt_ok).2
  have hstab := CFSG.KC.PCent.card_mul_card_stab_le (H := hs100P) (ptsOf 100 PO) fun s hs => by
    obtain ⟨g, hg, he⟩ := hpo s hs
    refine ⟨g, (Subgroup.closure_le _).2 ?_ hg, he⟩
    rintro _ ⟨k, hk, rfl⟩
    exact mem_hsW_P k (by omega) (by interval_cases k <;> rfl)
  rw [hpts, hlen, card_hs100P] at hstab
  have hfix : toPerm 100 7 v ⟨p, hp⟩ = ⟨p, hp⟩ := by
    refine Fin.ext ?_
    rw [toPerm_apply x3_pp_v.1]
    exact Nat.eq_of_beq_eq_true (x3band x3Cls_len).2
  obtain ⟨S, hS, hS'⟩ := classK_sound (fun k hk => (x3_pG_facts k hk).1) x3_pp_v.1 x3Cls_ok
  have hup := CFSG.EvenSporadicStandard.HSStd.FiveY.card_centralizer_mul_le_fix_mul hs100P hfix S
    fun s hs => by
      obtain ⟨g, hg, he⟩ := hS' s hs
      refine ⟨g, ?_, he⟩
      revert hg
      refine fun hg => (Subgroup.closure_le _).2 ?_ hg
      rintro _ ⟨k, hk, rfl⟩
      obtain ⟨hpp, -, hf⟩ := x3_pG_facts k hk
      refine Subgroup.mem_inf.2 ⟨x3_pG_P k hk, MulAction.mem_stabilizer_iff.2 ?_⟩
      rw [Equiv.Perm.smul_def]
      exact Fin.ext ((toPerm_apply hpp _).trans hf)
  have hRlen : R.length = 12320 := Nat.eq_of_beq_eq_true (x3band x3Cls_len).1
  rw [hS, hRlen, x3_card_fix_v] at hup
  have hR := Subgroup.relIndex_mul_card (H := hs100P) (K := hs100R)
  rw [inf_of_le_left hs100P_le_R, card_hs100P, card_hs100R] at hR
  have hR2 : hs100P.relIndex hs100R = 2 :=
    Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 44352000) (hR.trans (by norm_num))
  have hC := Subgroup.relIndex_mul_card (H := hs100P)
    (K := hs100R ⊓ Subgroup.centralizer ({toPerm 100 7 v} : Set (Equiv.Perm (Fin 100))))
  rw [h720, ← inf_assoc, inf_of_le_left hs100P_le_R] at hC
  have hi := Subgroup.relIndex_le_of_le_right (H := hs100P)
    (inf_le_left : hs100R ⊓ Subgroup.centralizer ({toPerm 100 7 v} : Set (Equiv.Perm (Fin 100))) ≤
      hs100R) (by rw [hR2]; decide)
  rw [hR2] at hi
  exact x3_arith hup hstab hC.ge hi

end CertificateChecks.KernelMisc.HS100.X3Cls

end
