module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicPermutesPackage
public import CFSG.GroupTheory.SylowTwoEquiv
public import CFSG.Sporadic.FischerOddCore.Fi22FiveExact
public import CFSG.Monster.AxisCount.Abstract
public import CFSG.GroupTheory.DisjointSupCard
public import Certificates.Kernel.Fi22Nine.Elem
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.Statements
public import CFSG.Monster.B.Fischer.Fi22Model
public import Certificates.Data.ExceptionalSL3

public section

namespace CertificateChecks.KernelSpor.Fi22Nine

open CFSG.Monster.B.Fischer
open CFSG.Certificates CFSG.Certificates.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.Th.Native CFSG.Sporadic.FischerOddCore CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.SmallOddCore.Native
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.QuasithinUnique CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine CFSG.Sporadic.Schreier
open CFSG.Monster.B.Co2
open scoped Pointwise commutatorElement

set_option linter.unusedSectionVars false

private noncomputable abbrev fi22NineZ : Equiv.Perm (Fin 3510) := fi22ExtRep 1

private noncomputable abbrev fi22NineT : Subgroup (Equiv.Perm (Fin 3510)) := fi22OuterT

private noncomputable abbrev fi22NineC : Subgroup (Equiv.Perm (Fin 3510)) := fi22H 1

private noncomputable abbrev fi22NineX0Set : Set (Fin 3510) := finSet 3510 X0

private noncomputable abbrev fi22NineX1Set : Set (Fin 3510) := finSet 3510 X1

private noncomputable abbrev fi22NineXP : Equiv.Perm (Fin 3510) := xE

private noncomputable abbrev fi22NineYP : Equiv.Perm (Fin 3510) := yE

private noncomputable abbrev fi22NineAP : Equiv.Perm (Fin 3510) := aE

private noncomputable abbrev fi22NineGP : Equiv.Perm (Fin 3510) := gE

private noncomputable abbrev fi22NineSP : Equiv.Perm (Fin 3510) := sE

private noncomputable abbrev fi22NineS1P : Equiv.Perm (Fin 3510) := s1E

private theorem fi22NineX3 : fi22NineXP ^ 3 = 1 := x3

private theorem fi22NineY3 : fi22NineYP ^ 3 = 1 := y3

private theorem fi22NineA3 : fi22NineAP ^ 3 = 1 := a3

private theorem fi22NineXYComm : Commute fi22NineXP fi22NineYP := xy_comm

private theorem fi22NineXNeOne : fi22NineXP ≠ 1 := x_ne_one

private theorem fi22NineYNeOne : fi22NineYP ≠ 1 := y_ne_one

private theorem fi22NineYNeX : fi22NineYP ≠ fi22NineXP := y_ne_x

private theorem fi22NineYNeXsq : fi22NineYP ≠ fi22NineXP ^ 2 := y_ne_x2

private theorem fi22NineANeOne : fi22NineAP ≠ 1 := a_ne_one

private theorem fi22NineXFix : fi22NineXP • fi22NineX0Set = fi22NineX0Set := x_fix

private theorem fi22NineYFix : fi22NineYP • fi22NineX0Set = fi22NineX0Set := y_fix

private theorem fi22NineAFix : fi22NineAP • fi22NineX1Set = fi22NineX1Set := a_fix

private theorem fi22NineSFix : fi22NineSP • fi22NineX0Set = fi22NineX0Set := s_fix

private theorem fi22NineS1Fix : fi22NineS1P • fi22NineX1Set = fi22NineX1Set := s1_fix

private theorem fi22NineSZ : Commute fi22NineSP fi22NineZ := s_comm

private theorem fi22NineS1Z : Commute fi22NineS1P fi22NineZ := s1_comm

private theorem fi22NineInvert : fi22NineGP * fi22NineAP * fi22NineGP⁻¹ = fi22NineAP⁻¹ := g_inv

private theorem fi22NineX_mem_C : fi22NineXP ∈ fi22NineC := xE_mem

private theorem fi22NineY_mem_C : fi22NineYP ∈ fi22NineC := yE_mem

private theorem fi22NineA_mem_C : fi22NineAP ∈ fi22NineC := aE_mem

private theorem fi22NineGP_mem_P : fi22NineGP ∈ fi22P := gE_mem

private theorem fi22NineUS_mem_P : fi22U * fi22NineSP ∈ fi22P := us_mem

private theorem fi22NineUS1_mem_P : fi22U * fi22NineS1P ∈ fi22P := us1_mem

private theorem fi22NineZ_mem_T : fi22NineZ ∈ fi22NineT := z_mem_T

private theorem fi22NineZ_ne_one : fi22NineZ ≠ 1 := z_ne_one

private theorem fi22NineZ_central : ∀ y ∈ fi22NineT, fi22NineZ * y = y * fi22NineZ := z_central

private theorem fi22NineCenter_eq (t : Equiv.Perm (Fin 3510)) :
    (t ∈ fi22NineT ∧ ∀ y ∈ fi22NineT, t * y = y * t) ↔ t = 1 ∨ t = fi22NineZ := by
  constructor
  · rintro ⟨ht, hcent⟩
    exact center_mem ht hcent
  · rintro (rfl | rfl)
    · exact ⟨fi22NineT.one_mem, fun y _ => by simp⟩
    · exact ⟨fi22NineZ_mem_T, fi22NineZ_central⟩

private theorem fi22NineT_le_R : fi22NineT ≤ fi22R :=
  fun _ hx => fi22P_le_R (fi22OuterT_le hx)

private theorem fi22NineConjZ_of_mem_normalizer {r : Equiv.Perm (Fin 3510)}
    (hr : r ∈ Subgroup.normalizer (fi22NineT : Set (Equiv.Perm (Fin 3510)))) :
    r * fi22NineZ * r⁻¹ = fi22NineZ := by
  have hzT : fi22NineZ ∈ fi22NineT := fi22NineZ_mem_T
  have hzmem : r * fi22NineZ * r⁻¹ ∈ fi22NineT :=
    (Subgroup.mem_normalizer_iff.mp hr fi22NineZ).mp hzT
  have hcentral : ∀ y ∈ fi22NineT,
      (r * fi22NineZ * r⁻¹) * y = y * (r * fi22NineZ * r⁻¹) := by
    intro y hy
    have hy' : r⁻¹ * y * r ∈ fi22NineT := by
      have hinv : r⁻¹ ∈ Subgroup.normalizer (fi22NineT : Set (Equiv.Perm (Fin 3510))) :=
        Subgroup.inv_mem _ hr
      exact (Subgroup.mem_normalizer_iff.mp hinv y).mp hy
    calc (r * fi22NineZ * r⁻¹) * y
        = r * (fi22NineZ * (r⁻¹ * y * r)) * r⁻¹ := by group
      _ = r * ((r⁻¹ * y * r) * fi22NineZ) * r⁻¹ := by
          rw [fi22NineZ_central (r⁻¹ * y * r) hy']
      _ = y * (r * fi22NineZ * r⁻¹) := by group
  rcases (fi22NineCenter_eq (r * fi22NineZ * r⁻¹)).1 ⟨hzmem, hcentral⟩ with h1 | hz
  · exfalso
    have hz1 : fi22NineZ = 1 := by
      calc fi22NineZ = r⁻¹ * (r * fi22NineZ * r⁻¹) * r := by group
        _ = 1 := by rw [h1]; group
    exact fi22NineZ_ne_one hz1
  · exact hz

private theorem fi22NineT_fix :
    fi22NineT ≤ MulAction.stabilizer (Equiv.Perm (Fin 3510)) fi22NineX0Set := T_fix0

private noncomputable def fi22NineZR : fi22R :=
  ⟨fi22NineZ, fi22NineT_le_R fi22NineZ_mem_T⟩

private noncomputable def fi22NineCR : Subgroup fi22R :=
  Subgroup.centralizer {fi22NineZR}

private theorem fi22NineP_inf_centralizer :
    fi22P ⊓ Subgroup.centralizer {fi22NineZ} = fi22NineC := by
  have h := (CFSG.Sporadic.FischerOddCore.CTUC_Fi22_five_exact_involution_fixed_subgroups).2.1
  simpa [fi22NineC, fi22NineZ] using h

private theorem fi22NineT_le_C :
    fi22NineT ≤ fi22NineC := by
  intro x hx
  have h := fi22NineP_inf_centralizer
  rw [← h]
  refine ⟨fi22OuterT_le hx, ?_⟩
  exact Subgroup.mem_centralizer_singleton_iff.mpr (fi22NineZ_central x hx).symm

private theorem fi22NineP_inf_CR :
    fi22P.subgroupOf fi22R ⊓ fi22NineCR =
      fi22NineC.subgroupOf fi22R := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxP, hxCR⟩ := Subgroup.mem_inf.mp hx
    have hxP' : (x : Equiv.Perm (Fin 3510)) ∈ fi22P :=
      Subgroup.mem_subgroupOf.mp hxP
    have hxcz : (x : Equiv.Perm (Fin 3510)) * fi22NineZ =
        fi22NineZ * (x : Equiv.Perm (Fin 3510)) := by
      have hxCR' : x ∈ Subgroup.centralizer {fi22NineZR} := by
        simpa [fi22NineCR] using hxCR
      have h := Subgroup.mem_centralizer_singleton_iff.mp hxCR'
      simpa [fi22NineZR] using congrArg Subtype.val h
    have hxmem : (x : Equiv.Perm (Fin 3510)) ∈
        fi22P ⊓ Subgroup.centralizer {fi22NineZ} :=
      ⟨hxP', Subgroup.mem_centralizer_singleton_iff.mpr hxcz⟩
    have hxC : (x : Equiv.Perm (Fin 3510)) ∈ fi22NineC := by
      rw [← fi22NineP_inf_centralizer]
      exact hxmem
    exact Subgroup.mem_subgroupOf.mpr hxC
  · intro hy
    have hyC : (x : Equiv.Perm (Fin 3510)) ∈ fi22NineC := Subgroup.mem_subgroupOf.mp hy
    have hymem : (x : Equiv.Perm (Fin 3510)) ∈
        fi22P ⊓ Subgroup.centralizer {fi22NineZ} := by
      rw [fi22NineP_inf_centralizer]
      exact hyC
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr hymem.1, ?_⟩
    rw [fi22NineCR, Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp hymem.2

private theorem fi22NineS_mem_R : fi22NineSP ∈ fi22R :=
  (mem_fi22R_iff fi22NineSP).2 (Or.inr fi22NineUS_mem_P)

private theorem fi22NineS_mem_CR :
    (⟨fi22NineSP, fi22NineS_mem_R⟩ : fi22R) ∈ fi22NineCR := by
  rw [fi22NineCR, Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  exact fi22NineSZ.eq

private theorem fi22NineConjC_mem {h : Equiv.Perm (Fin 3510)} (hh : h ∈ fi22NineC) :
    fi22NineSP * h * fi22NineSP⁻¹ ∈ fi22NineC := by
  have hfive := fi22NineP_inf_centralizer
  have hmem : h ∈ fi22P ⊓ Subgroup.centralizer {fi22NineZ} := by
    rw [fi22NineP_inf_centralizer]
    exact hh
  have hhP : h ∈ fi22P := hmem.1
  have hhz : h * fi22NineZ = fi22NineZ * h :=
    Subgroup.mem_centralizer_singleton_iff.mp hmem.2
  have hsR : fi22NineSP ∈ fi22R := fi22NineS_mem_R
  have hP : fi22NineSP * h * fi22NineSP⁻¹ ∈ fi22P := by
    have hnorm : fi22NineSP ∈
        Subgroup.normalizer (fi22P : Set (Equiv.Perm (Fin 3510))) :=
      fi22R_le_normalizer hsR
    exact (Subgroup.mem_normalizer_iff.mp hnorm h).mp hhP
  have hsz : fi22NineSP * fi22NineZ = fi22NineZ * fi22NineSP := fi22NineSZ.eq
  have hsz' : fi22NineSP⁻¹ * fi22NineZ = fi22NineZ * fi22NineSP⁻¹ := by
    calc fi22NineSP⁻¹ * fi22NineZ
        = fi22NineSP⁻¹ * (fi22NineZ * fi22NineSP) * fi22NineSP⁻¹ := by group
      _ = fi22NineSP⁻¹ * (fi22NineSP * fi22NineZ) * fi22NineSP⁻¹ := by rw [← hsz]
      _ = fi22NineZ * fi22NineSP⁻¹ := by group
  have hz : (fi22NineSP * h * fi22NineSP⁻¹) * fi22NineZ =
      fi22NineZ * (fi22NineSP * h * fi22NineSP⁻¹) := by
    calc (fi22NineSP * h * fi22NineSP⁻¹) * fi22NineZ
        = fi22NineSP * (h * (fi22NineSP⁻¹ * fi22NineZ)) := by group
      _ = fi22NineSP * (h * (fi22NineZ * fi22NineSP⁻¹)) := by rw [hsz']
      _ = fi22NineSP * ((fi22NineZ * h) * fi22NineSP⁻¹) := by rw [← hhz]; group
      _ = (fi22NineZ * fi22NineSP) * (h * fi22NineSP⁻¹) := by rw [← hsz]; group
      _ = fi22NineZ * (fi22NineSP * h * fi22NineSP⁻¹) := by group
  rw [← hfive]
  exact ⟨hP, Subgroup.mem_centralizer_singleton_iff.mpr hz⟩

private noncomputable def fi22NineH9 : Subgroup (Equiv.Perm (Fin 3510)) :=
  fi22NineC ⊓ MulAction.stabilizer (Equiv.Perm (Fin 3510)) fi22NineX0Set

private noncomputable def fi22NineH3 : Subgroup (Equiv.Perm (Fin 3510)) :=
  fi22NineC ⊓ MulAction.stabilizer (Equiv.Perm (Fin 3510)) fi22NineX1Set

private theorem fi22NineH9_upper :
    Nat.card ↥fi22NineH9 ≤ 1179648 := by
  classical
  have hstab : Nat.card (MulAction.stabilizer ↥fi22NineC fi22NineX0Set) =
      Nat.card ↥fi22NineH9 := by
    rw [fi22NineH9]
    rw [← MulAction.stabilizer_subgroupOf (G := Equiv.Perm (Fin 3510)) fi22NineC
      fi22NineX0Set]
    rw [← Subgroup.inf_subgroupOf_left
      (MulAction.stabilizer (Equiv.Perm (Fin 3510)) fi22NineX0Set) fi22NineC]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hcardC : Nat.card ↥fi22NineC = 53084160 := by
    change Nat.card ↥(fi22H 1) = 53084160
    rw [card_fi22H (c := 1) (by norm_num)]
    decide
  have hOS := CFSG.Monster.AxisCount.card_orbit_mul_card_stabilizer
    (K := ↥fi22NineC) (X := Set (Fin 3510)) fi22NineX0Set
  have hle := orb0_lower
  have horbge : 45 ≤ Nat.card (MulAction.orbit ↥fi22NineC fi22NineX0Set) := by
    rw [Nat.card_coe_set_eq]
    simpa [MulAction.orbit] using hle
  have hmul : Nat.card (MulAction.orbit ↥fi22NineC fi22NineX0Set) *
      Nat.card (MulAction.stabilizer ↥fi22NineC fi22NineX0Set) = 53084160 := by
    rw [hOS, hcardC]
  have hmul' : Nat.card (MulAction.orbit ↥fi22NineC fi22NineX0Set) *
      Nat.card ↥fi22NineH9 = 53084160 := by
    rw [← hstab]
    exact hmul
  have h45 : 45 * Nat.card ↥fi22NineH9 ≤ 45 * 1179648 := by
    calc 45 * Nat.card ↥fi22NineH9
        ≤ Nat.card (MulAction.orbit ↥fi22NineC fi22NineX0Set) * Nat.card ↥fi22NineH9 :=
          Nat.mul_le_mul_right _ horbge
      _ = 53084160 := hmul'
      _ = 45 * 1179648 := by norm_num
  exact Nat.le_of_mul_le_mul_left h45 (by norm_num)

private theorem fi22NineCardLower (T Q H : Subgroup (Equiv.Perm (Fin 3510)))
    (hT : T ≤ H) (hQ : Q ≤ H) (hdisj : Disjoint T Q) (hQcard : Nat.card Q = 9) :
    9 * Nat.card T ≤ Nat.card H := by
  classical
  let f : ↥T × ↥Q → ↥H := fun p =>
    ⟨(p.1 : Equiv.Perm (Fin 3510)) * (p.2 : Equiv.Perm (Fin 3510)),
      Subgroup.mul_mem _ (hT p.1.2) (hQ p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨a1, b1⟩ ⟨a2, b2⟩ h
    have hprod : (a1 : Equiv.Perm (Fin 3510)) * (b1 : Equiv.Perm (Fin 3510)) =
        (a2 : Equiv.Perm (Fin 3510)) * (b2 : Equiv.Perm (Fin 3510)) :=
      congrArg Subtype.val h
    have heq : (a2 : Equiv.Perm (Fin 3510))⁻¹ * (a1 : Equiv.Perm (Fin 3510)) =
        (b2 : Equiv.Perm (Fin 3510)) * (b1 : Equiv.Perm (Fin 3510))⁻¹ := by
      calc (a2 : Equiv.Perm (Fin 3510))⁻¹ * (a1 : Equiv.Perm (Fin 3510))
          = (a2 : Equiv.Perm (Fin 3510))⁻¹ *
              ((a1 : Equiv.Perm (Fin 3510)) * (b1 : Equiv.Perm (Fin 3510))) *
              (b1 : Equiv.Perm (Fin 3510))⁻¹ := by group
        _ = (a2 : Equiv.Perm (Fin 3510))⁻¹ *
              ((a2 : Equiv.Perm (Fin 3510)) * (b2 : Equiv.Perm (Fin 3510))) *
              (b1 : Equiv.Perm (Fin 3510))⁻¹ := by rw [hprod]
        _ = (b2 : Equiv.Perm (Fin 3510)) * (b1 : Equiv.Perm (Fin 3510))⁻¹ := by group
    have h1 : (a2 : Equiv.Perm (Fin 3510))⁻¹ * (a1 : Equiv.Perm (Fin 3510)) ∈ T :=
      T.mul_mem (T.inv_mem a2.2) a1.2
    have h2 : (a2 : Equiv.Perm (Fin 3510))⁻¹ * (a1 : Equiv.Perm (Fin 3510)) ∈ Q := by
      rw [heq]
      exact Q.mul_mem b2.2 (Q.inv_mem b1.2)
    have hone : (a2 : Equiv.Perm (Fin 3510))⁻¹ * (a1 : Equiv.Perm (Fin 3510)) = 1 :=
      (Subgroup.disjoint_def.mp hdisj) h1 h2
    have ha : a1 = a2 := by
      apply Subtype.ext
      have h := congrArg (fun x => (a2 : Equiv.Perm (Fin 3510)) * x) hone
      simpa [mul_assoc] using h
    have hb : b1 = b2 := by
      apply Subtype.ext
      have hb' : (b2 : Equiv.Perm (Fin 3510)) * (b1 : Equiv.Perm (Fin 3510))⁻¹ = 1 := by
        rw [← heq]
        exact hone
      have h := congrArg (fun x => x * (b1 : Equiv.Perm (Fin 3510))) hb'
      simpa [mul_assoc] using h.symm
    exact Prod.ext ha hb
  have hle := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, hQcard] at hle
  rwa [Nat.mul_comm]

private theorem fi22NineT_le_H9 :
    fi22NineT ≤ fi22NineH9 := by
  rw [fi22NineH9]
  intro x hx
  exact ⟨fi22NineT_le_C hx, fi22NineT_fix hx⟩

private theorem fi22NineQ_le_C :
    Subgroup.closure ({fi22NineXP, fi22NineYP} : Set (Equiv.Perm (Fin 3510))) ≤
      fi22NineC := by
  rw [Subgroup.closure_le]
  rintro g (rfl | rfl)
  · exact fi22NineX_mem_C
  · exact fi22NineY_mem_C

private theorem fi22NineX_le_S :
    fi22NineXP ∈ MulAction.stabilizer (Equiv.Perm (Fin 3510)) fi22NineX0Set :=
  MulAction.mem_stabilizer_iff.mpr fi22NineXFix

private theorem fi22NineY_le_S :
    fi22NineYP ∈ MulAction.stabilizer (Equiv.Perm (Fin 3510)) fi22NineX0Set :=
  MulAction.mem_stabilizer_iff.mpr fi22NineYFix

private theorem fi22NineQ_le_S :
    Subgroup.closure ({fi22NineXP, fi22NineYP} : Set (Equiv.Perm (Fin 3510))) ≤
      MulAction.stabilizer (Equiv.Perm (Fin 3510)) fi22NineX0Set := by
  rw [Subgroup.closure_le]
  rintro g (rfl | rfl)
  · exact fi22NineX_le_S
  · exact fi22NineY_le_S

private theorem fi22NineH9_lower :
    1179648 ≤ Nat.card ↥fi22NineH9 := by
  classical
  let Q : Subgroup (Equiv.Perm (Fin 3510)) :=
    Subgroup.closure ({fi22NineXP, fi22NineYP} : Set (Equiv.Perm (Fin 3510)))
  have hQcard : Nat.card Q = 9 :=
    CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine fi22NineX3 fi22NineY3
      fi22NineXYComm fi22NineXNeOne
      (CFSG.RankThree.Asc83Table.not_mem_zpowers_of_ne fi22NineX3 fi22NineYNeOne
        fi22NineYNeX fi22NineYNeXsq)
  have hdisj : Disjoint fi22NineT Q := by
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [fi22NineT, card_fi22OuterT, hQcard]
    norm_num
  have hT_le_H : fi22NineT ≤ fi22NineH9 := fi22NineT_le_H9
  have hQ_le_C : Q ≤ fi22NineC := fi22NineQ_le_C
  have hQ_le_S : Q ≤ MulAction.stabilizer (Equiv.Perm (Fin 3510)) fi22NineX0Set :=
    fi22NineQ_le_S
  have hQ_le_H : Q ≤ fi22NineH9 := by
    rw [fi22NineH9]
    exact le_inf hQ_le_C hQ_le_S
  have hlower : 9 * Nat.card fi22NineT ≤ Nat.card ↥fi22NineH9 :=
    fi22NineCardLower fi22NineT Q fi22NineH9 hT_le_H hQ_le_H hdisj hQcard
  have hTcard : Nat.card fi22NineT = 131072 := by
    simpa [fi22NineT] using card_fi22OuterT
  have h9 : 9 * Nat.card fi22NineT = 1179648 := by
    rw [hTcard]
  calc 1179648 = 9 * Nat.card fi22NineT := h9.symm
    _ ≤ Nat.card ↥fi22NineH9 := hlower

private theorem fi22NineH9_card :
    Nat.card ↥fi22NineH9 = 1179648 :=
  le_antisymm fi22NineH9_upper fi22NineH9_lower

private theorem fi22NineT_fix1 :
    fi22NineT ≤ MulAction.stabilizer (Equiv.Perm (Fin 3510)) fi22NineX1Set := T_fix1

private theorem fi22NineT_le_H3 :
    fi22NineT ≤ fi22NineH3 := by
  rw [fi22NineH3]
  intro x hx
  exact ⟨fi22NineT_le_C hx, fi22NineT_fix1 hx⟩

private theorem fi22NineAtp_le_H3 :
    Subgroup.zpowers (fi22NineAP) ≤ fi22NineH3 := by
  rw [fi22NineH3]
  refine le_inf ?_ ?_
  · rw [Subgroup.zpowers_le]
    exact fi22NineA_mem_C
  · rw [Subgroup.zpowers_le]
    exact MulAction.mem_stabilizer_iff.mpr fi22NineAFix

private theorem fi22NineA_zpowers_card :
    Nat.card (Subgroup.zpowers (fi22NineAP)) = 3 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime fi22NineA3 fi22NineANeOne

private theorem fi22NineH3_upper :
    Nat.card ↥fi22NineH3 ≤ 393216 := by
  classical
  have hstab : Nat.card (MulAction.stabilizer ↥fi22NineC fi22NineX1Set) =
      Nat.card ↥fi22NineH3 := by
    rw [fi22NineH3]
    rw [← MulAction.stabilizer_subgroupOf (G := Equiv.Perm (Fin 3510)) fi22NineC
      fi22NineX1Set]
    rw [← Subgroup.inf_subgroupOf_left
      (MulAction.stabilizer (Equiv.Perm (Fin 3510)) fi22NineX1Set) fi22NineC]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hcardC : Nat.card ↥fi22NineC = 53084160 := by
    change Nat.card ↥(fi22H 1) = 53084160
    rw [card_fi22H (c := 1) (by norm_num)]
    decide
  have hOS := CFSG.Monster.AxisCount.card_orbit_mul_card_stabilizer
    (K := ↥fi22NineC) (X := Set (Fin 3510)) fi22NineX1Set
  have hle := orb1_lower
  have horbge : 135 ≤ Nat.card (MulAction.orbit ↥fi22NineC fi22NineX1Set) := by
    rw [Nat.card_coe_set_eq]
    simpa [MulAction.orbit] using hle
  have hmul : Nat.card (MulAction.orbit ↥fi22NineC fi22NineX1Set) *
      Nat.card (MulAction.stabilizer ↥fi22NineC fi22NineX1Set) = 53084160 := by
    rw [hOS, hcardC]
  have hmul' : Nat.card (MulAction.orbit ↥fi22NineC fi22NineX1Set) *
      Nat.card ↥fi22NineH3 = 53084160 := by
    rw [← hstab]
    exact hmul
  have h45 : 135 * Nat.card ↥fi22NineH3 ≤ 135 * 393216 := by
    calc 135 * Nat.card ↥fi22NineH3
        ≤ Nat.card (MulAction.orbit ↥fi22NineC fi22NineX1Set) * Nat.card ↥fi22NineH3 :=
          Nat.mul_le_mul_right _ horbge
      _ = 53084160 := hmul'
      _ = 135 * 393216 := by norm_num
  exact Nat.le_of_mul_le_mul_left h45 (by norm_num)

private theorem fi22NineH3_lower :
    393216 ≤ Nat.card ↥fi22NineH3 := by
  classical
  have hdisj : Disjoint fi22NineT
      (Subgroup.zpowers (fi22NineAP)) := by
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [fi22NineT, card_fi22OuterT, fi22NineA_zpowers_card]
    norm_num
  have hsup : fi22NineT ⊔ Subgroup.zpowers (fi22NineAP) ≤ fi22NineH3 :=
    sup_le fi22NineT_le_H3 fi22NineAtp_le_H3
  have hleSup : Nat.card ↥(fi22NineT ⊔
      Subgroup.zpowers (fi22NineAP)) ≤ Nat.card ↥fi22NineH3 :=
    Subgroup.card_le_of_le hsup
  have hprod := CFSG.GroupTheory.card_mul_card_le_card_sup_of_disjoint
    (H := fi22NineT) (K := Subgroup.zpowers (fi22NineAP)) hdisj
  have hmain : Nat.card fi22NineT * 3 ≤ Nat.card ↥fi22NineH3 := by
    calc Nat.card fi22NineT * 3
        = Nat.card fi22NineT *
            Nat.card (Subgroup.zpowers (fi22NineAP)) := by
          rw [fi22NineA_zpowers_card]
      _ ≤ Nat.card ↥(fi22NineT ⊔
            Subgroup.zpowers (fi22NineAP)) := hprod
      _ ≤ Nat.card ↥fi22NineH3 := hleSup
  have hTcard : Nat.card fi22NineT = 131072 := by
    simpa [fi22NineT] using card_fi22OuterT
  have h9 : Nat.card fi22NineT * 3 = 393216 := by
    rw [hTcard]
  calc 393216 = Nat.card fi22NineT * 3 := h9.symm
    _ ≤ Nat.card ↥fi22NineH3 := hmain

private theorem fi22NineH3_card :
    Nat.card ↥fi22NineH3 = 393216 :=
  le_antisymm fi22NineH3_upper fi22NineH3_lower

private theorem fi22NineS1_mem_R : fi22NineS1P ∈ fi22R :=
  (mem_fi22R_iff fi22NineS1P).2 (Or.inr fi22NineUS1_mem_P)

private theorem fi22NineS1_mem_CR :
    (⟨fi22NineS1P, fi22NineS1_mem_R⟩ : fi22R) ∈ fi22NineCR := by
  rw [fi22NineCR, Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  exact fi22NineS1Z.eq

private theorem fi22NineConjC_mem1
    {h : Equiv.Perm (Fin 3510)} (hh : h ∈ fi22NineC) :
    fi22NineS1P * h * fi22NineS1P⁻¹ ∈ fi22NineC := by
  have hfive := fi22NineP_inf_centralizer
  have hmem : h ∈ fi22P ⊓ Subgroup.centralizer {fi22NineZ} := by
    rw [fi22NineP_inf_centralizer]
    exact hh
  have hhP : h ∈ fi22P := hmem.1
  have hhz : h * fi22NineZ = fi22NineZ * h :=
    Subgroup.mem_centralizer_singleton_iff.mp hmem.2
  have hsR : fi22NineS1P ∈ fi22R := fi22NineS1_mem_R
  have hP : fi22NineS1P * h * fi22NineS1P⁻¹ ∈ fi22P := by
    have hnorm : fi22NineS1P ∈
        Subgroup.normalizer (fi22P : Set (Equiv.Perm (Fin 3510))) :=
      fi22R_le_normalizer hsR
    exact (Subgroup.mem_normalizer_iff.mp hnorm h).mp hhP
  have hsz : fi22NineS1P * fi22NineZ = fi22NineZ * fi22NineS1P := fi22NineS1Z.eq
  have hsz' : fi22NineS1P⁻¹ * fi22NineZ = fi22NineZ * fi22NineS1P⁻¹ := by
    calc fi22NineS1P⁻¹ * fi22NineZ
        = fi22NineS1P⁻¹ * (fi22NineZ * fi22NineS1P) * fi22NineS1P⁻¹ := by group
      _ = fi22NineS1P⁻¹ * (fi22NineS1P * fi22NineZ) * fi22NineS1P⁻¹ := by rw [← hsz]
      _ = fi22NineZ * fi22NineS1P⁻¹ := by group
  have hz : (fi22NineS1P * h * fi22NineS1P⁻¹) * fi22NineZ =
      fi22NineZ * (fi22NineS1P * h * fi22NineS1P⁻¹) := by
    calc (fi22NineS1P * h * fi22NineS1P⁻¹) * fi22NineZ
        = fi22NineS1P * (h * (fi22NineS1P⁻¹ * fi22NineZ)) := by group
      _ = fi22NineS1P * (h * (fi22NineZ * fi22NineS1P⁻¹)) := by rw [hsz']
      _ = fi22NineS1P * ((fi22NineZ * h) * fi22NineS1P⁻¹) := by rw [← hhz]; group
      _ = (fi22NineZ * fi22NineS1P) * (h * fi22NineS1P⁻¹) := by rw [← hsz]; group
      _ = fi22NineZ * (fi22NineS1P * h * fi22NineS1P⁻¹) := by group
  rw [← hfive]
  exact ⟨hP, Subgroup.mem_centralizer_singleton_iff.mpr hz⟩

private theorem fi22NineCR_orbit9 {c : ↥fi22R} (hc : c ∈ fi22NineCR) :
    (c : Equiv.Perm (Fin 3510)) • fi22NineX0Set ∈
      Set.range (fun g : ↥fi22NineC => g • fi22NineX0Set) := by
  classical
  by_cases hP : (c : Equiv.Perm (Fin 3510)) ∈ fi22P
  · have hc' : c ∈ fi22P.subgroupOf fi22R ⊓ fi22NineCR :=
      ⟨Subgroup.mem_subgroupOf.mpr hP, hc⟩
    rw [fi22NineP_inf_CR] at hc'
    have hC : (c : Equiv.Perm (Fin 3510)) ∈ fi22NineC := Subgroup.mem_subgroupOf.mp hc'
    exact ⟨⟨(c : Equiv.Perm (Fin 3510)), hC⟩, rfl⟩
  · have hcR : (c : Equiv.Perm (Fin 3510)) ∈ fi22R := c.2
    have hUP : fi22U * (c : Equiv.Perm (Fin 3510)) ∈ fi22P :=
      ((mem_fi22R_iff (c : Equiv.Perm (Fin 3510))).1 hcR).resolve_left hP
    have hUS : fi22U * fi22NineSP ∈ fi22P := fi22NineUS_mem_P
    have hprodP : (fi22U * (c : Equiv.Perm (Fin 3510)))⁻¹ * (fi22U * fi22NineSP) ∈ fi22P :=
      fi22P.mul_mem (fi22P.inv_mem hUP) hUS
    have hprodEq : (fi22U * (c : Equiv.Perm (Fin 3510)))⁻¹ * (fi22U * fi22NineSP) =
        (c : Equiv.Perm (Fin 3510))⁻¹ * fi22NineSP := by
      calc (fi22U * (c : Equiv.Perm (Fin 3510)))⁻¹ * (fi22U * fi22NineSP)
          = (c : Equiv.Perm (Fin 3510))⁻¹ * (fi22U * fi22U) * fi22NineSP := by
            rw [mul_inv_rev, fi22U_inv]; group
        _ = (c : Equiv.Perm (Fin 3510))⁻¹ * fi22NineSP := by
            rw [fi22U_mul_self]; group
    have hprodP' : (c : Equiv.Perm (Fin 3510))⁻¹ * fi22NineSP ∈ fi22P := by
      rwa [← hprodEq]
    have hsCR : (⟨fi22NineSP, fi22NineS_mem_R⟩ : fi22R) ∈ fi22NineCR :=
      fi22NineS_mem_CR
    let hR : fi22R := ⟨(c : Equiv.Perm (Fin 3510))⁻¹ * fi22NineSP,
      fi22R.mul_mem (fi22R.inv_mem c.2) fi22NineS_mem_R⟩
    have hprodCR : hR ∈ fi22NineCR := by
      have hmul : c⁻¹ * ⟨fi22NineSP, fi22NineS_mem_R⟩ ∈ fi22NineCR :=
        fi22NineCR.mul_mem (fi22NineCR.inv_mem hc) hsCR
      have heq : hR = c⁻¹ * ⟨fi22NineSP, fi22NineS_mem_R⟩ := by
        apply Subtype.ext
        rfl
      rwa [heq]
    have hprodC : (c : Equiv.Perm (Fin 3510))⁻¹ * fi22NineSP ∈ fi22NineC := by
      have hmem : hR ∈ fi22P.subgroupOf fi22R ⊓ fi22NineCR :=
        ⟨Subgroup.mem_subgroupOf.mpr hprodP', hprodCR⟩
      rw [fi22NineP_inf_CR] at hmem
      exact Subgroup.mem_subgroupOf.mp hmem
    let h' : Equiv.Perm (Fin 3510) := ((c : Equiv.Perm (Fin 3510))⁻¹ * fi22NineSP)⁻¹
    have hh' : h' ∈ fi22NineC := fi22NineC.inv_mem hprodC
    have hcEq : (c : Equiv.Perm (Fin 3510)) = fi22NineSP * h' := by
      dsimp [h']
      group
    have h'' : fi22NineSP * h' * fi22NineSP⁻¹ ∈ fi22NineC := fi22NineConjC_mem hh'
    have hsinv : fi22NineSP⁻¹ • fi22NineX0Set = fi22NineX0Set := by
      have h := congrArg (fun y => fi22NineSP⁻¹ • y) fi22NineSFix
      simpa [smul_smul] using h.symm
    refine ⟨⟨fi22NineSP * h' * fi22NineSP⁻¹, h''⟩, ?_⟩
    rw [hcEq]
    show (fi22NineSP * h' * fi22NineSP⁻¹) • fi22NineX0Set =
      (fi22NineSP * h') • fi22NineX0Set
    simp only [mul_smul, hsinv]
private theorem fi22NineCR_orbit3 {c : ↥fi22R} (hc : c ∈ fi22NineCR) :
    (c : Equiv.Perm (Fin 3510)) • fi22NineX1Set ∈
      Set.range (fun g : ↥fi22NineC => g • fi22NineX1Set) := by
  classical
  by_cases hP : (c : Equiv.Perm (Fin 3510)) ∈ fi22P
  · have hc' : c ∈ fi22P.subgroupOf fi22R ⊓ fi22NineCR :=
      ⟨Subgroup.mem_subgroupOf.mpr hP, hc⟩
    rw [fi22NineP_inf_CR] at hc'
    have hC : (c : Equiv.Perm (Fin 3510)) ∈ fi22NineC := Subgroup.mem_subgroupOf.mp hc'
    exact ⟨⟨(c : Equiv.Perm (Fin 3510)), hC⟩, rfl⟩
  · have hcR : (c : Equiv.Perm (Fin 3510)) ∈ fi22R := c.2
    have hUP : fi22U * (c : Equiv.Perm (Fin 3510)) ∈ fi22P :=
      ((mem_fi22R_iff (c : Equiv.Perm (Fin 3510))).1 hcR).resolve_left hP
    have hUS : fi22U * fi22NineS1P ∈ fi22P := fi22NineUS1_mem_P
    have hprodP : (fi22U * (c : Equiv.Perm (Fin 3510)))⁻¹ * (fi22U * fi22NineS1P) ∈ fi22P :=
      fi22P.mul_mem (fi22P.inv_mem hUP) hUS
    have hprodEq : (fi22U * (c : Equiv.Perm (Fin 3510)))⁻¹ * (fi22U * fi22NineS1P) =
        (c : Equiv.Perm (Fin 3510))⁻¹ * fi22NineS1P := by
      calc (fi22U * (c : Equiv.Perm (Fin 3510)))⁻¹ * (fi22U * fi22NineS1P)
          = (c : Equiv.Perm (Fin 3510))⁻¹ * (fi22U * fi22U) * fi22NineS1P := by
            rw [mul_inv_rev, fi22U_inv]; group
        _ = (c : Equiv.Perm (Fin 3510))⁻¹ * fi22NineS1P := by
            rw [fi22U_mul_self]; group
    have hprodP' : (c : Equiv.Perm (Fin 3510))⁻¹ * fi22NineS1P ∈ fi22P := by
      rwa [← hprodEq]
    have hsCR : (⟨fi22NineS1P, fi22NineS1_mem_R⟩ : fi22R) ∈ fi22NineCR :=
      fi22NineS1_mem_CR
    let hR : fi22R := ⟨(c : Equiv.Perm (Fin 3510))⁻¹ * fi22NineS1P,
      fi22R.mul_mem (fi22R.inv_mem c.2) fi22NineS1_mem_R⟩
    have hprodCR : hR ∈ fi22NineCR := by
      have hmul : c⁻¹ * ⟨fi22NineS1P, fi22NineS1_mem_R⟩ ∈ fi22NineCR :=
        fi22NineCR.mul_mem (fi22NineCR.inv_mem hc) hsCR
      have heq : hR = c⁻¹ * ⟨fi22NineS1P, fi22NineS1_mem_R⟩ := by
        apply Subtype.ext
        rfl
      rwa [heq]
    have hprodC : (c : Equiv.Perm (Fin 3510))⁻¹ * fi22NineS1P ∈ fi22NineC := by
      have hmem : hR ∈ fi22P.subgroupOf fi22R ⊓ fi22NineCR :=
        ⟨Subgroup.mem_subgroupOf.mpr hprodP', hprodCR⟩
      rw [fi22NineP_inf_CR] at hmem
      exact Subgroup.mem_subgroupOf.mp hmem
    let h' : Equiv.Perm (Fin 3510) := ((c : Equiv.Perm (Fin 3510))⁻¹ * fi22NineS1P)⁻¹
    have hh' : h' ∈ fi22NineC := fi22NineC.inv_mem hprodC
    have hcEq : (c : Equiv.Perm (Fin 3510)) = fi22NineS1P * h' := by
      dsimp [h']
      group
    have h'' : fi22NineS1P * h' * fi22NineS1P⁻¹ ∈ fi22NineC := fi22NineConjC_mem1 hh'
    have hsinv : fi22NineS1P⁻¹ • fi22NineX1Set = fi22NineX1Set := by
      have h := congrArg (fun y => fi22NineS1P⁻¹ • y) fi22NineS1Fix
      simpa [smul_smul] using h.symm
    refine ⟨⟨fi22NineS1P * h' * fi22NineS1P⁻¹, h''⟩, ?_⟩
    rw [hcEq]
    show (fi22NineS1P * h' * fi22NineS1P⁻¹) • fi22NineX1Set =
      (fi22NineS1P * h') • fi22NineX1Set
    simp only [mul_smul, hsinv]

private theorem fi22NineStab9_card :
    Nat.card (MulAction.stabilizer ↥fi22NineC fi22NineX0Set) = 1179648 := by
  have h : Nat.card (MulAction.stabilizer ↥fi22NineC fi22NineX0Set) =
      Nat.card ↥fi22NineH9 := by
    rw [fi22NineH9]
    rw [← MulAction.stabilizer_subgroupOf (G := Equiv.Perm (Fin 3510)) fi22NineC
      fi22NineX0Set]
    rw [← Subgroup.inf_subgroupOf_left
      (MulAction.stabilizer (Equiv.Perm (Fin 3510)) fi22NineX0Set) fi22NineC]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [h]
  exact fi22NineH9_card

private theorem fi22NineStab3_card :
    Nat.card (MulAction.stabilizer ↥fi22NineC fi22NineX1Set) = 393216 := by
  have h : Nat.card (MulAction.stabilizer ↥fi22NineC fi22NineX1Set) =
      Nat.card ↥fi22NineH3 := by
    rw [fi22NineH3]
    rw [← MulAction.stabilizer_subgroupOf (G := Equiv.Perm (Fin 3510)) fi22NineC
      fi22NineX1Set]
    rw [← Subgroup.inf_subgroupOf_left
      (MulAction.stabilizer (Equiv.Perm (Fin 3510)) fi22NineX1Set) fi22NineC]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [h]
  exact fi22NineH3_card

private theorem fi22NineOrbit9_card :
    (Set.range fun g : ↥fi22NineC => g • fi22NineX0Set).ncard = 45 := by
  have hOS := CFSG.Monster.AxisCount.card_orbit_mul_card_stabilizer
    (K := ↥fi22NineC) (X := Set (Fin 3510)) fi22NineX0Set
  have hcardC : Nat.card ↥fi22NineC = 53084160 := by
    change Nat.card ↥(fi22H 1) = 53084160
    rw [card_fi22H (c := 1) (by norm_num)]
    decide
  have hmul : Nat.card (MulAction.orbit ↥fi22NineC fi22NineX0Set) * 1179648 = 53084160 := by
    have h := hOS
    rw [fi22NineStab9_card, hcardC] at h
    exact h
  have h : Nat.card (MulAction.orbit ↥fi22NineC fi22NineX0Set) * 1179648 =
      45 * 1179648 := by
    rw [hmul]
  have h45 : Nat.card (MulAction.orbit ↥fi22NineC fi22NineX0Set) = 45 :=
    Nat.eq_of_mul_eq_mul_right (by norm_num) h
  simpa [MulAction.orbit, Nat.card_coe_set_eq] using h45

private theorem fi22NineOrbit3_card :
    (Set.range fun g : ↥fi22NineC => g • fi22NineX1Set).ncard = 135 := by
  have hOS := CFSG.Monster.AxisCount.card_orbit_mul_card_stabilizer
    (K := ↥fi22NineC) (X := Set (Fin 3510)) fi22NineX1Set
  have hcardC : Nat.card ↥fi22NineC = 53084160 := by
    change Nat.card ↥(fi22H 1) = 53084160
    rw [card_fi22H (c := 1) (by norm_num)]
    decide
  have hmul : Nat.card (MulAction.orbit ↥fi22NineC fi22NineX1Set) * 393216 = 53084160 := by
    have h := hOS
    rw [fi22NineStab3_card, hcardC] at h
    exact h
  have h : Nat.card (MulAction.orbit ↥fi22NineC fi22NineX1Set) * 393216 =
      135 * 393216 := by
    rw [hmul]
  have h135 : Nat.card (MulAction.orbit ↥fi22NineC fi22NineX1Set) = 135 :=
    Nat.eq_of_mul_eq_mul_right (by norm_num) h
  simpa [MulAction.orbit, Nat.card_coe_set_eq] using h135

private theorem fi22NineUnique9 :
    ∀ y ∈ Set.range (fun g : ↥fi22NineC => g • fi22NineX0Set),
      (∀ t ∈ fi22NineT, t • y = y) → y = fi22NineX0Set := by
  exact orb0_unique fi22NineOrbit9_card

private theorem fi22NineUnique3 :
    ∀ y ∈ Set.range (fun g : ↥fi22NineC => g • fi22NineX1Set),
      (∀ t ∈ fi22NineT, t • y = y) → y = fi22NineX1Set := by
  exact orb1_unique fi22NineOrbit3_card

private theorem fi22NineX_mem_P : fi22NineXP ∈ fi22P := by
  have h : fi22NineXP ∈ fi22P ⊓ Subgroup.centralizer {fi22NineZ} := by
    rw [fi22NineP_inf_centralizer]
    exact fi22NineX_mem_C
  exact h.1

private theorem fi22NineY_mem_P : fi22NineYP ∈ fi22P := by
  have h : fi22NineYP ∈ fi22P ⊓ Subgroup.centralizer {fi22NineZ} := by
    rw [fi22NineP_inf_centralizer]
    exact fi22NineY_mem_C
  exact h.1

private theorem fi22NineA_mem_P : fi22NineAP ∈ fi22P := by
  have h : fi22NineAP ∈ fi22P ⊓ Subgroup.centralizer {fi22NineZ} := by
    rw [fi22NineP_inf_centralizer]
    exact fi22NineA_mem_C
  exact h.1

private theorem fi22NineAutPerm :
    ∀ α : MulAut ↥fi22P, ∃ r ∈ fi22R, ∀ n : ↥fi22P,
      ((α n : ↥fi22P) : Equiv.Perm (Fin 3510)) =
        r * (n : Equiv.Perm (Fin 3510)) * r⁻¹ := by
  intro α
  refine ⟨fi22RAut.symm α, (fi22RAut.symm α).2, fun n => ?_⟩
  have h : fi22RAut (fi22RAut.symm α) = α := MulEquiv.apply_symm_apply fi22RAut α
  have hα : ((α n : ↥fi22P) : Equiv.Perm (Fin 3510)) =
      ((fi22RAut (fi22RAut.symm α)) n : ↥fi22P) := by rw [h]
  exact hα.trans (fi22ConjHom_apply (fi22RAut.symm α) n)

private theorem fi22NineHNCperm :
    fi22R ⊓ Subgroup.normalizer
        (((fi22NineT.subgroupOf fi22P).map fi22P.subtype : Subgroup
          (Equiv.Perm (Fin 3510))) : Set (Equiv.Perm (Fin 3510))) ≤
      Subgroup.centralizer {fi22NineZ} := by
  intro r hr
  have hrR := hr.1
  have hrN := hr.2
  rw [Subgroup.map_subgroupOf_eq_of_le fi22OuterT_le] at hrN
  have hconj := fi22NineConjZ_of_mem_normalizer hrN
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc r * fi22NineZ = (r * fi22NineZ * r⁻¹) * r := by group
    _ = fi22NineZ * r := by rw [hconj]

private theorem fi22NineHfixPerm :
    ∀ u ∈ fi22NineT.subgroupOf fi22P,
      (u : Equiv.Perm (Fin 3510)) • fi22NineX0Set = fi22NineX0Set := by
  intro u hu
  exact fi22NineT_fix (Subgroup.mem_subgroupOf.mp hu)

private theorem fi22NineH9_le_P : fi22NineH9 ≤ fi22P := by
  intro x hx
  rw [fi22NineH9] at hx
  have hmem : x ∈ fi22P ⊓ Subgroup.centralizer {fi22NineZ} := by
    rw [fi22NineP_inf_centralizer]
    exact hx.1
  exact hmem.1

private theorem fi22NineH3_le_P : fi22NineH3 ≤ fi22P := by
  intro x hx
  rw [fi22NineH3] at hx
  have hmem : x ∈ fi22P ⊓ Subgroup.centralizer {fi22NineZ} := by
    rw [fi22NineP_inf_centralizer]
    exact hx.1
  exact hmem.1

private theorem fi22NineHuniq9 :
    ∀ c ∈ fi22R ⊓ Subgroup.centralizer {fi22NineZ},
      (∀ u ∈ fi22NineT.subgroupOf fi22P,
        (u : Equiv.Perm (Fin 3510)) • (c • fi22NineX0Set) = c • fi22NineX0Set) →
      c • fi22NineX0Set = fi22NineX0Set := by
  intro c hc hfix
  have hcR : c ∈ fi22R := hc.1
  have hcCR : (⟨c, hcR⟩ : fi22R) ∈ fi22NineCR := by
    rw [fi22NineCR, Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp hc.2
  have horb := fi22NineCR_orbit9 hcCR
  refine fi22NineUnique9 _ horb ?_
  intro t ht
  let u : fi22NineT.subgroupOf fi22P := ⟨⟨t, fi22OuterT_le ht⟩, ht⟩
  have h := hfix u u.2
  simpa [u] using h

private theorem fi22NineHuniq3 :
    ∀ c ∈ fi22R ⊓ Subgroup.centralizer {fi22NineZ},
      (∀ u ∈ fi22NineT.subgroupOf fi22P,
        (u : Equiv.Perm (Fin 3510)) • (c • fi22NineX1Set) = c • fi22NineX1Set) →
      c • fi22NineX1Set = fi22NineX1Set := by
  intro c hc hfix
  have hcR : c ∈ fi22R := hc.1
  have hcCR : (⟨c, hcR⟩ : fi22R) ∈ fi22NineCR := by
    rw [fi22NineCR, Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp hc.2
  have horb := fi22NineCR_orbit3 hcCR
  refine fi22NineUnique3 _ horb ?_
  intro t ht
  let u : fi22NineT.subgroupOf fi22P := ⟨⟨t, fi22OuterT_le ht⟩, ht⟩
  have h := hfix u u.2
  simpa [u] using h

private theorem fi22NineIsSylowU :
    CFSG.QuasithinUnique.IsSylowTwoOf (fi22NineT.subgroupOf fi22P) ⊤ := by
  obtain ⟨S, hS⟩ := fi22OuterT_sylow
  refine ⟨le_top, ?_, ?_⟩
  · rw [← hS]
    exact S.isPGroup'
  · change ¬ 2 ∣ (fi22NineT.subgroupOf fi22P).relIndex ⊤
    rw [Subgroup.relIndex_top_right, ← hS]
    exact S.not_dvd_index

private theorem fi22NineY_not_zpowers :
    fi22NineYP ∉ Subgroup.zpowers fi22NineXP :=
  CFSG.RankThree.Asc83Table.not_mem_zpowers_of_ne fi22NineX3 fi22NineYNeOne
    fi22NineYNeX fi22NineYNeXsq

private theorem fi22NineHfix1Perm :
    ∀ u ∈ fi22NineT.subgroupOf fi22P,
      (u : Equiv.Perm (Fin 3510)) • fi22NineX1Set = fi22NineX1Set := by
  intro u hu
  exact fi22NineT_fix1 (Subgroup.mem_subgroupOf.mp hu)

private noncomputable abbrev fi22NineNT : Subgroup ↥fi22R := fi22P.subgroupOf fi22R

private noncomputable abbrev fi22NineiNT : ↥fi22NineNT ≃* ↥fi22P :=
  Subgroup.subgroupOfEquivOfLe fi22P_le_R

private noncomputable abbrev fi22NineUN : Subgroup ↥fi22NineNT :=
  (fi22NineT.subgroupOf fi22P).map fi22NineiNT.symm.toMonoidHom

private theorem fi22NineUN_map :
    fi22NineUN.map fi22NineNT.subtype = fi22NineT.subgroupOf fi22R := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hu
    have hk' : (k : Equiv.Perm (Fin 3510)) ∈ fi22NineT := Subgroup.mem_subgroupOf.mp hk
    exact Subgroup.mem_subgroupOf.mpr (by
      simpa [Subgroup.subgroupOfEquivOfLe_symm_apply_coe_coe] using hk')
  · intro hx
    have hxT : (x : Equiv.Perm (Fin 3510)) ∈ fi22NineT := Subgroup.mem_subgroupOf.mp hx
    let k : ↥fi22P := ⟨(x : Equiv.Perm (Fin 3510)), fi22OuterT_le hxT⟩
    have hk : k ∈ fi22NineT.subgroupOf fi22P := hxT
    refine Subgroup.mem_map.mpr ⟨fi22NineiNT.symm k, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨k, hk, rfl⟩
    · apply Subtype.ext
      rfl

private theorem fi22NineIsSylowUN :
    CFSG.QuasithinUnique.IsSylowTwoOf fi22NineUN ⊤ := by
  have h := CFSG.QuasithinUnique.IsSylowTwoOf.map_mulEquiv fi22NineiNT.symm fi22NineIsSylowU
  rw [Subgroup.map_top_of_surjective fi22NineiNT.symm.toMonoidHom
    fi22NineiNT.symm.surjective] at h
  simpa [fi22NineUN] using h

private theorem fi22NineAutR :
    ∀ α : MulAut ↥fi22NineNT, ∃ r ∈ (⊤ : Subgroup ↥fi22R),
      ∀ n : ↥fi22NineNT,
        ((α n : ↥fi22NineNT) : ↥fi22R) = r * n * r⁻¹ := by
  intro α
  let β : MulAut ↥fi22P := (fi22NineiNT.symm.trans α).trans fi22NineiNT
  obtain ⟨r, hrR, hr⟩ := fi22NineAutPerm β
  refine ⟨⟨r, hrR⟩, Subgroup.mem_top _, fun n => ?_⟩
  apply Subtype.ext
  have h := hr (fi22NineiNT n)
  simpa [β, fi22NineiNT, Subgroup.subgroupOfEquivOfLe_apply_coe,
    Subgroup.subgroupOfEquivOfLe_symm_apply_coe_coe] using h

private theorem fi22NineHfixR9 :
    ∀ u ∈ fi22NineUN, (u : ↥fi22R) • fi22NineX0Set = fi22NineX0Set := by
  intro u hu
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hu
  have h := fi22NineHfixPerm k hk
  simpa [Subgroup.smul_def, Subgroup.subgroupOfEquivOfLe_symm_apply_coe_coe] using h

private theorem fi22NineHfixR3 :
    ∀ u ∈ fi22NineUN, (u : ↥fi22R) • fi22NineX1Set = fi22NineX1Set := by
  intro u hu
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hu
  have h := fi22NineHfix1Perm k hk
  simpa [Subgroup.smul_def, Subgroup.subgroupOfEquivOfLe_symm_apply_coe_coe] using h

private theorem fi22NineHNCR :
    (⊤ : Subgroup ↥fi22R) ⊓ Subgroup.normalizer
        ((fi22NineUN.map fi22NineNT.subtype : Subgroup ↥fi22R) : Set ↥fi22R) ≤
      fi22NineCR := by
  rw [fi22NineUN_map]
  intro r hr
  have hrN : r ∈ Subgroup.normalizer
      ((fi22NineT.subgroupOf fi22R : Subgroup ↥fi22R) : Set ↥fi22R) := hr.2
  rw [← Subgroup.subgroupOf_normalizer_eq fi22NineT_le_R] at hrN
  have hr' : (r : Equiv.Perm (Fin 3510)) ∈ fi22R ⊓ Subgroup.normalizer
      (((fi22NineT.subgroupOf fi22P).map fi22P.subtype : Subgroup
        (Equiv.Perm (Fin 3510))) : Set (Equiv.Perm (Fin 3510))) := by
    refine ⟨r.2, ?_⟩
    simpa [Subgroup.map_subgroupOf_eq_of_le fi22OuterT_le] using
      (Subgroup.mem_subgroupOf.mp hrN)
  rw [fi22NineCR, Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  simpa [fi22NineZR] using Subgroup.mem_centralizer_singleton_iff.mp
    (fi22NineHNCperm hr')

private theorem fi22NineHuniqR9 :
    ∀ c ∈ (⊤ : Subgroup ↥fi22R) ⊓ fi22NineCR,
      (∀ u ∈ fi22NineUN,
        (u : ↥fi22R) • (c • fi22NineX0Set) = c • fi22NineX0Set) →
      c • fi22NineX0Set = fi22NineX0Set := by
  intro c hc hfix
  have hcR : (c : ↥fi22R) ∈ fi22NineCR := hc.2
  have hc' : (c : Equiv.Perm (Fin 3510)) ∈
      fi22R ⊓ Subgroup.centralizer {fi22NineZ} := by
    refine ⟨c.2, ?_⟩
    have h := Subgroup.mem_centralizer_singleton_iff.mp
      (by simpa [fi22NineCR] using hcR)
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by
      simpa [fi22NineZR] using congrArg Subtype.val h)
  refine fi22NineHuniq9 (c : Equiv.Perm (Fin 3510)) hc' ?_
  intro t ht
  let k : ↥fi22P := ⟨t, fi22OuterT_le ht⟩
  let u : ↥fi22NineNT := fi22NineiNT.symm k
  have hu : u ∈ fi22NineUN := Subgroup.mem_map.mpr ⟨k, ht, rfl⟩
  have h := hfix u hu
  simpa [u, Subgroup.smul_def, fi22NineiNT,
    Subgroup.subgroupOfEquivOfLe_symm_apply_coe_coe] using h

private theorem fi22NineHuniqR3 :
    ∀ c ∈ (⊤ : Subgroup ↥fi22R) ⊓ fi22NineCR,
      (∀ u ∈ fi22NineUN,
        (u : ↥fi22R) • (c • fi22NineX1Set) = c • fi22NineX1Set) →
      c • fi22NineX1Set = fi22NineX1Set := by
  intro c hc hfix
  have hcR : (c : ↥fi22R) ∈ fi22NineCR := hc.2
  have hc' : (c : Equiv.Perm (Fin 3510)) ∈
      fi22R ⊓ Subgroup.centralizer {fi22NineZ} := by
    refine ⟨c.2, ?_⟩
    have h := Subgroup.mem_centralizer_singleton_iff.mp
      (by simpa [fi22NineCR] using hcR)
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by
      simpa [fi22NineZR] using congrArg Subtype.val h)
  refine fi22NineHuniq3 (c : Equiv.Perm (Fin 3510)) hc' ?_
  intro t ht
  let k : ↥fi22P := ⟨t, fi22OuterT_le ht⟩
  let u : ↥fi22NineNT := fi22NineiNT.symm k
  have hu : u ∈ fi22NineUN := Subgroup.mem_map.mpr ⟨k, ht, rfl⟩
  have h := hfix u hu
  simpa [u, Subgroup.smul_def, fi22NineiNT,
    Subgroup.subgroupOfEquivOfLe_symm_apply_coe_coe] using h

private theorem fi22NineHcardSub9R :
    (fi22NineCR ⊓ MulAction.stabilizer ↥fi22R fi22NineX0Set).subgroupOf fi22NineNT =
      (fi22NineH9.subgroupOf fi22P).comap fi22NineiNT.toMonoidHom := by
  ext x
  constructor
  · intro hx
    have hx' := Subgroup.mem_subgroupOf.mp hx
    have hxCR : (x : ↥fi22R) ∈ fi22NineCR := (Subgroup.mem_inf.mp hx').1
    have hxstab : (x : ↥fi22R) ∈ MulAction.stabilizer ↥fi22R fi22NineX0Set :=
      (Subgroup.mem_inf.mp hx').2
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have hxP : (x : Equiv.Perm (Fin 3510)) ∈ fi22P := by
        simpa using Subgroup.mem_subgroupOf.mp x.2
      have hxcz : (x : Equiv.Perm (Fin 3510)) * fi22NineZ =
          fi22NineZ * (x : Equiv.Perm (Fin 3510)) := by
        have h := Subgroup.mem_centralizer_singleton_iff.mp
          (by simpa [fi22NineCR] using hxCR)
        simpa [fi22NineZR] using congrArg Subtype.val h
      have hmem : (x : Equiv.Perm (Fin 3510)) ∈
          fi22P ⊓ Subgroup.centralizer {fi22NineZ} :=
        ⟨hxP, Subgroup.mem_centralizer_singleton_iff.mpr hxcz⟩
      have hC : (x : Equiv.Perm (Fin 3510)) ∈ fi22NineC := by
        rw [← fi22NineP_inf_centralizer]
        exact hmem
      simpa [fi22NineiNT, Subgroup.subgroupOfEquivOfLe_apply_coe] using hC
    · have hstab : (x : ↥fi22R) • fi22NineX0Set = fi22NineX0Set :=
        MulAction.mem_stabilizer_iff.mp hxstab
      rw [MulAction.mem_stabilizer_iff]
      simpa [fi22NineiNT, Subgroup.smul_def,
        Subgroup.subgroupOfEquivOfLe_apply_coe] using hstab
  · intro hx
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf] at hx
    have hxP : (x : Equiv.Perm (Fin 3510)) ∈ fi22P := by
      simpa using Subgroup.mem_subgroupOf.mp x.2
    have hC : (x : Equiv.Perm (Fin 3510)) ∈ fi22NineC := by
      simpa [fi22NineiNT, Subgroup.subgroupOfEquivOfLe_apply_coe] using hx.1
    have hstab : (x : Equiv.Perm (Fin 3510)) ∈
        MulAction.stabilizer (Equiv.Perm (Fin 3510)) fi22NineX0Set := by
      rw [MulAction.mem_stabilizer_iff]
      have h := MulAction.mem_stabilizer_iff.mp hx.2
      simpa [fi22NineiNT, Subgroup.smul_def,
        Subgroup.subgroupOfEquivOfLe_apply_coe] using h
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · rw [fi22NineCR, Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      have hmem : (x : Equiv.Perm (Fin 3510)) ∈
          fi22P ⊓ Subgroup.centralizer {fi22NineZ} := by
        rw [fi22NineP_inf_centralizer]
        exact hC
      have hcz := Subgroup.mem_centralizer_singleton_iff.mp hmem.2
      simpa [fi22NineZR] using hcz
    · rw [MulAction.mem_stabilizer_iff]
      simpa [Subgroup.smul_def] using hstab

private theorem fi22NineHcardSub3R :
    (fi22NineCR ⊓ MulAction.stabilizer ↥fi22R fi22NineX1Set).subgroupOf fi22NineNT =
      (fi22NineH3.subgroupOf fi22P).comap fi22NineiNT.toMonoidHom := by
  ext x
  constructor
  · intro hx
    have hx' := Subgroup.mem_subgroupOf.mp hx
    have hxCR : (x : ↥fi22R) ∈ fi22NineCR := (Subgroup.mem_inf.mp hx').1
    have hxstab : (x : ↥fi22R) ∈ MulAction.stabilizer ↥fi22R fi22NineX1Set :=
      (Subgroup.mem_inf.mp hx').2
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have hxP : (x : Equiv.Perm (Fin 3510)) ∈ fi22P := by
        simpa using Subgroup.mem_subgroupOf.mp x.2
      have hxcz : (x : Equiv.Perm (Fin 3510)) * fi22NineZ =
          fi22NineZ * (x : Equiv.Perm (Fin 3510)) := by
        have h := Subgroup.mem_centralizer_singleton_iff.mp
          (by simpa [fi22NineCR] using hxCR)
        simpa [fi22NineZR] using congrArg Subtype.val h
      have hmem : (x : Equiv.Perm (Fin 3510)) ∈
          fi22P ⊓ Subgroup.centralizer {fi22NineZ} :=
        ⟨hxP, Subgroup.mem_centralizer_singleton_iff.mpr hxcz⟩
      have hC : (x : Equiv.Perm (Fin 3510)) ∈ fi22NineC := by
        rw [← fi22NineP_inf_centralizer]
        exact hmem
      simpa [fi22NineiNT, Subgroup.subgroupOfEquivOfLe_apply_coe] using hC
    · have hstab : (x : ↥fi22R) • fi22NineX1Set = fi22NineX1Set :=
        MulAction.mem_stabilizer_iff.mp hxstab
      rw [MulAction.mem_stabilizer_iff]
      simpa [fi22NineiNT, Subgroup.smul_def,
        Subgroup.subgroupOfEquivOfLe_apply_coe] using hstab
  · intro hx
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf] at hx
    have hxP : (x : Equiv.Perm (Fin 3510)) ∈ fi22P := by
      simpa using Subgroup.mem_subgroupOf.mp x.2
    have hC : (x : Equiv.Perm (Fin 3510)) ∈ fi22NineC := by
      simpa [fi22NineiNT, Subgroup.subgroupOfEquivOfLe_apply_coe] using hx.1
    have hstab : (x : Equiv.Perm (Fin 3510)) ∈
        MulAction.stabilizer (Equiv.Perm (Fin 3510)) fi22NineX1Set := by
      rw [MulAction.mem_stabilizer_iff]
      have h := MulAction.mem_stabilizer_iff.mp hx.2
      simpa [fi22NineiNT, Subgroup.smul_def,
        Subgroup.subgroupOfEquivOfLe_apply_coe] using h
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · rw [fi22NineCR, Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      have hmem : (x : Equiv.Perm (Fin 3510)) ∈
          fi22P ⊓ Subgroup.centralizer {fi22NineZ} := by
        rw [fi22NineP_inf_centralizer]
        exact hC
      have hcz := Subgroup.mem_centralizer_singleton_iff.mp hmem.2
      simpa [fi22NineZR] using hcz
    · rw [MulAction.mem_stabilizer_iff]
      simpa [Subgroup.smul_def] using hstab

private theorem fi22NineCardH9sub :
    Nat.card (fi22NineH9.subgroupOf fi22P) =
      9 * Nat.card (fi22NineT.subgroupOf fi22P) := by
  have hcardT : Nat.card (fi22NineT.subgroupOf fi22P) = Nat.card fi22NineT :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe fi22OuterT_le).toEquiv
  rw [hcardT, Nat.card_congr (Subgroup.subgroupOfEquivOfLe fi22NineH9_le_P).toEquiv,
    fi22NineH9_card, card_fi22OuterT]

private theorem fi22NineCardH3sub :
    Nat.card (fi22NineH3.subgroupOf fi22P) =
      3 * Nat.card (fi22NineT.subgroupOf fi22P) := by
  have hcardT : Nat.card (fi22NineT.subgroupOf fi22P) = Nat.card fi22NineT :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe fi22OuterT_le).toEquiv
  rw [hcardT, Nat.card_congr (Subgroup.subgroupOfEquivOfLe fi22NineH3_le_P).toEquiv,
    fi22NineH3_card, card_fi22OuterT]

private theorem fi22NineHcardR9 :
    Nat.card ((fi22NineCR ⊓ MulAction.stabilizer ↥fi22R fi22NineX0Set).subgroupOf
        fi22NineNT) = 9 * Nat.card fi22NineUN := by
  have hUN : Nat.card fi22NineUN = Nat.card (fi22NineT.subgroupOf fi22P) := by
    simpa [fi22NineUN] using Subgroup.card_map_of_injective
      (f := fi22NineiNT.symm.toMonoidHom) fi22NineiNT.symm.injective
      (K := fi22NineT.subgroupOf fi22P)
  have hcomap : Nat.card ((fi22NineH9.subgroupOf fi22P).comap fi22NineiNT.toMonoidHom) =
      Nat.card (fi22NineH9.subgroupOf fi22P) := by
    rw [← Subgroup.card_map_of_injective (f := fi22NineiNT.toMonoidHom)
      fi22NineiNT.injective (K := (fi22NineH9.subgroupOf fi22P).comap
        fi22NineiNT.toMonoidHom)]
    rw [Subgroup.map_comap_eq_self_of_surjective fi22NineiNT.surjective]
  rw [fi22NineHcardSub9R, hUN, hcomap, fi22NineCardH9sub]

private theorem fi22NineHcardR3 :
    Nat.card ((fi22NineCR ⊓ MulAction.stabilizer ↥fi22R fi22NineX1Set).subgroupOf
        fi22NineNT) = 3 * Nat.card fi22NineUN := by
  have hUN : Nat.card fi22NineUN = Nat.card (fi22NineT.subgroupOf fi22P) := by
    simpa [fi22NineUN] using Subgroup.card_map_of_injective
      (f := fi22NineiNT.symm.toMonoidHom) fi22NineiNT.symm.injective
      (K := fi22NineT.subgroupOf fi22P)
  have hcomap : Nat.card ((fi22NineH3.subgroupOf fi22P).comap fi22NineiNT.toMonoidHom) =
      Nat.card (fi22NineH3.subgroupOf fi22P) := by
    rw [← Subgroup.card_map_of_injective (f := fi22NineiNT.toMonoidHom)
      fi22NineiNT.injective (K := (fi22NineH3.subgroupOf fi22P).comap
        fi22NineiNT.toMonoidHom)]
    rw [Subgroup.map_comap_eq_self_of_surjective fi22NineiNT.surjective]
  rw [fi22NineHcardSub3R, hUN, hcomap, fi22NineCardH3sub]

private noncomputable abbrev fi22NinePR9 : Subgroup ↥fi22NineNT :=
  (fi22NineH9.subgroupOf fi22P).map fi22NineiNT.symm.toMonoidHom

private noncomputable abbrev fi22NinePR3 : Subgroup ↥fi22NineNT :=
  (fi22NineH3.subgroupOf fi22P).map fi22NineiNT.symm.toMonoidHom

private noncomputable abbrev fi22NineKP : Subgroup ↥fi22P :=
  (Subgroup.closure ({fi22NineXP, fi22NineYP} :
    Set (Equiv.Perm (Fin 3510)))).subgroupOf fi22P

private noncomputable abbrev fi22NineQN : Subgroup ↥fi22NineNT :=
  fi22NineKP.map fi22NineiNT.symm.toMonoidHom

private theorem fi22NinePR9_eq :
    (fi22NineCR ⊓ MulAction.stabilizer ↥fi22R fi22NineX0Set).subgroupOf fi22NineNT =
      fi22NinePR9 := by
  rw [fi22NineHcardSub9R, Subgroup.comap_equiv_eq_map_symm']

private theorem fi22NinePR3_eq :
    (fi22NineCR ⊓ MulAction.stabilizer ↥fi22R fi22NineX1Set).subgroupOf fi22NineNT =
      fi22NinePR3 := by
  rw [fi22NineHcardSub3R, Subgroup.comap_equiv_eq_map_symm']

private theorem fi22NineUN_le_PR9 : fi22NineUN ≤ fi22NinePR9 := by
  rw [fi22NineUN, fi22NinePR9]
  exact Subgroup.map_mono (Subgroup.subgroupOf_mono fi22P fi22NineT_le_H9)

private theorem fi22NineUN_le_PR3 : fi22NineUN ≤ fi22NinePR3 := by
  rw [fi22NineUN, fi22NinePR3]
  exact Subgroup.map_mono (Subgroup.subgroupOf_mono fi22P fi22NineT_le_H3)

private theorem fi22NineXY_le_P :
    Subgroup.closure ({fi22NineXP, fi22NineYP} :
      Set (Equiv.Perm (Fin 3510))) ≤ fi22P := by
  rw [Subgroup.closure_le]
  intro w hw
  rcases hw with rfl | rfl
  · exact fi22NineX_mem_P
  · exact fi22NineY_mem_P

private theorem fi22NineXY_le_H9 :
    Subgroup.closure ({fi22NineXP, fi22NineYP} :
      Set (Equiv.Perm (Fin 3510))) ≤ fi22NineH9 :=
  le_inf fi22NineQ_le_C fi22NineQ_le_S

private theorem fi22NineKP_le_H9sub :
    fi22NineKP ≤ fi22NineH9.subgroupOf fi22P := by
  rw [fi22NineKP]
  exact Subgroup.subgroupOf_mono fi22P fi22NineXY_le_H9

private theorem fi22NineQN_le_PR9 : fi22NineQN ≤ fi22NinePR9 := by
  rw [fi22NineQN, fi22NinePR9]
  exact Subgroup.map_mono fi22NineKP_le_H9sub

private theorem fi22NineQN_card : Nat.card fi22NineQN = 9 := by
  rw [fi22NineQN, Subgroup.card_map_of_injective
    (f := fi22NineiNT.symm.toMonoidHom) fi22NineiNT.symm.injective]
  rw [fi22NineKP, Nat.card_congr
    (Subgroup.subgroupOfEquivOfLe fi22NineXY_le_P).toEquiv]
  exact CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine fi22NineX3
    fi22NineY3 fi22NineXYComm fi22NineXNeOne fi22NineY_not_zpowers

private theorem fi22NineQN_three :
    ∀ q ∈ fi22NineQN, q ^ 3 = 1 := by
  intro q hq
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hq
  have hk' : (k : Equiv.Perm (Fin 3510)) ∈
      Subgroup.closure ({fi22NineXP, fi22NineYP} :
        Set (Equiv.Perm (Fin 3510))) := Subgroup.mem_subgroupOf.mp hk
  have hcomm : ⁅fi22NineXP, fi22NineYP⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact fi22NineXYComm.eq
  have hk3 := pow_three_eq_one_of_mem_closure_cubic fi22NineX3 fi22NineY3
    (by rw [hcomm]; exact Commute.one_left _)
    (by rw [hcomm]; exact Commute.one_left _) hk'
  have hk3' : k ^ 3 = 1 := by
    apply Subtype.ext
    simpa using hk3
  apply fi22NineiNT.injective
  simpa using hk3'

private noncomputable def fi22NineAN : ↥fi22NineNT :=
  fi22NineiNT.symm ⟨fi22NineAP, fi22NineA_mem_P⟩

private noncomputable def fi22NineGN : ↥fi22NineNT :=
  fi22NineiNT.symm ⟨fi22NineGP, fi22NineGP_mem_P⟩

private theorem fi22NineAN_mem_PR3 : fi22NineAN ∈ fi22NinePR3 := by
  rw [fi22NinePR3]
  refine Subgroup.mem_map.mpr ⟨⟨fi22NineAP, fi22NineA_mem_P⟩, ?_, rfl⟩
  exact Subgroup.mem_subgroupOf.mpr (by
    simpa [fi22NineAP] using
      fi22NineAtp_le_H3 (Subgroup.mem_zpowers (fi22NineAP)))

private theorem fi22NineAN_ne_one :
    fi22NineAN ≠ 1 := by
  intro h
  apply fi22NineANeOne
  have h' := congrArg fi22NineiNT h
  simpa [fi22NineAN, fi22NineAP] using congrArg Subtype.val h'

private theorem fi22NineAN3 :
    fi22NineAN ^ 3 = 1 := by
  apply fi22NineiNT.injective
  simpa [fi22NineAN, fi22NineAP] using fi22NineA3

private theorem fi22NineAGN :
    fi22NineGN * fi22NineAN * fi22NineGN⁻¹ = fi22NineAN⁻¹ := by
  apply fi22NineiNT.injective
  apply Subtype.ext
  simpa [fi22NineGN, fi22NineAN, fi22NineAP, fi22NineGP] using fi22NineInvert

private theorem fi22NinePackageCore : IndexNinePackage ↥fi22NineNT := by
  classical
  haveI := (fi22R_semidirect).1
  refine ⟨fi22NineUN, fi22NinePR9, fi22NineQN, fi22NineIsSylowUN,
    fi22NineUN_le_PR9, ?_, ?_, fi22NineQN_le_PR9, fi22NineQN_card,
    fi22NineQN_three⟩
  · rw [← fi22NinePR9_eq]
    exact fi22NineHcardR9
  · intro α hα
    rw [← fi22NinePR9_eq]
    exact map_eq_of_unique_fixed fi22NineAutR fi22NineHNCR fi22NineHfixR9
      fi22NineHuniqR9 α hα

theorem index_nine_package : IndexNinePackage ↥(fi22P.subgroupOf fi22R) :=
  fi22NinePackageCore

private theorem fi22NinePackageCore3 : IndexThreePackage ↥fi22NineNT := by
  classical
  haveI := (fi22R_semidirect).1
  refine ⟨fi22NineUN, fi22NinePR3, fi22NineAN, fi22NineGN,
    fi22NineIsSylowUN, fi22NineUN_le_PR3, ?_, ?_, fi22NineAN_mem_PR3,
    fi22NineAN_ne_one, fi22NineAN3, fi22NineAGN⟩
  · rw [← fi22NinePR3_eq]
    exact fi22NineHcardR3
  · intro α hα
    rw [← fi22NinePR3_eq]
    exact map_eq_of_unique_fixed fi22NineAutR fi22NineHNCR fi22NineHfixR3
      fi22NineHuniqR3 α hα

theorem index_three_package : IndexThreePackage ↥(fi22P.subgroupOf fi22R) :=
  fi22NinePackageCore3

end CertificateChecks.KernelSpor.Fi22Nine

end
