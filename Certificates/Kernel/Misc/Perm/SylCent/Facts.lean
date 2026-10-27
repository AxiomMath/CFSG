module

public import Certificates.Kernel.Misc.Perm.SylCent.Checks
public import CFSG.Certificates.Kernel.Misc.PermCentSound
import CFSG.Certificates.Kernel.LocalQTPermSound
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourCertificateBase
public import Certificates.Certificate2022Base

public section

namespace CertificateChecks.KernelMisc.SylCent

open Equiv CFSG.KC.Ord CFSG.KS CFSG.KC.Misc.Clos CFSG.KC.Misc.ClosW CFSG.KC.Misc.Cent
open CFSG.KC.LQT.P (allN anyN impB)
open CFSG.KC.Enum (pcomp pidn pg)
open CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four.Native

abbrev gs : List (Perm (Fin 42)) := [g₁, g₂, g₃, g₄, g₅, g₆]

theorem tabs : ∀ j < 6, ∀ i : Fin 42, (#[g₁T, g₂T, g₃T, g₄T, g₅T, g₆T][j]!)[i.val]! =
    (gs.getD j 1 i : ℕ) := by
  intro j hj i
  interval_cases j
  · exact tabRep_g₁.2 i
  · exact tabRep_g₂.2 i
  · exact tabRep_g₃.2 i
  · exact tabRep_g₄.2 i
  · exact tabRep_g₅.2 i
  · exact tabRep_g₆.2 i

theorem tcodes : ∀ j < 6, GC j = tcode 42 6 (#[g₁T, g₂T, g₃T, g₄T, g₅T, g₆T][j]!) := by
  decide +kernel

theorem hGC : ∀ j < gs.length, GC j = wcode 6 (gs.getD j 1) := fun j hj =>
  (tcodes j hj).trans (wcode_eq_tcode (tabs j hj)).symm

theorem hGS : ∀ j < [g₁, g₂, g₃].length, GC j = wcode 6 ([g₁, g₂, g₃].getD j 1) := by
  intro j hj
  have hj3 : j < 3 := hj
  have := hGC j (by change j < 6; omega)
  interval_cases j <;> exact this

theorem hw : 42 + 1 < 2 ^ 6 := by decide
theorem hw' : 42 < 2 ^ 6 := by decide
theorem hn : 42 < 16777216 := by decide

theorem enc : ClosEnc (wcode (n := 42) 6) (pcomp 42 6 (mask 6)) (pidn 42 6) := wcode_enc hw hn

theorem S_eq : S = Subgroup.closure {g | g ∈ [g₁, g₂, g₃]} := by
  rw [S]
  congr 1
  ext z
  simp

theorem R_eq : R = Subgroup.closure {g | g ∈ gs} := by
  rw [R]
  congr 1
  ext z
  simp

theorem p_elt (j : Nat) (hj : j < 4) : ∃ p ∈ S, wcode 6 p = PC j := by
  obtain ⟨h1, h2⟩ := andB_eq_true ((allN_iff _ _).1 pwB j hj)
  obtain ⟨p, hp, hpc⟩ := wword_mem hw hn [g₁, g₂, g₃] hGS h1
  exact ⟨p, S_eq ▸ hp, hpc.trans (Nat.eq_of_beq_eq_true h2)⟩

noncomputable def pE (j : Nat) : Perm (Fin 42) :=
  if h : j < 4 then (p_elt j h).choose else 1

theorem pE_spec {j : Nat} (h : j < 4) : pE j ∈ S ∧ wcode 6 (pE j) = PC j := by
  unfold pE
  split
  · exact (p_elt j h).choose_spec
  · contradiction

noncomputable abbrev ps : List (Perm (Fin 42)) := [pE 0, pE 1, pE 2, pE 3]

noncomputable abbrev P : Subgroup (Perm (Fin 42)) := Subgroup.closure {g | g ∈ ps}

theorem hPC : ∀ j < ps.length, PC j = wcode 6 (ps.getD j 1) := by
  intro j hj
  have hj4 : j < 4 := hj
  interval_cases j
  · exact (pE_spec (j := 0) (by decide)).2.symm
  · exact (pE_spec (j := 1) (by decide)).2.symm
  · exact (pE_spec (j := 2) (by decide)).2.symm
  · exact (pE_spec (j := 3) (by decide)).2.symm

theorem clos : (∀ k < 64, ∃ g ∈ P, wcode 6 g = E k) ∧ 64 ≤ Nat.card P ∧
    ∀ {CT : Nat → Nat}, (∀ k < 64, closedAt (pcomp 42 6 (mask 6)) PC ps.length 64 E CT k = true) →
      Nat.card P = 64 ∧ ∀ g ∈ P, ∃ k < 64, wcode 6 g = E k :=
  clos_card enc ps hPC (by decide) ((allN_iff _ _).1 treeB) ((allN_iff _ _).1 sortB)

theorem P_le : P ≤ S := by
  rw [Subgroup.closure_le]
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact (pE_spec (j := 0) (by decide)).1
  · exact (pE_spec (j := 1) (by decide)).1
  · exact (pE_spec (j := 2) (by decide)).1
  · exact (pE_spec (j := 3) (by decide)).1

theorem gen_pres : ∀ j < gs.length, Pres AA (gs.getD j 1) := fun j hj => by
  have h := (allN_iff _ _).1 gpresB j hj
  rw [hGC j hj] at h
  exact fun a b hab => (presE_iff hw' AA _).1 h a b hab

theorem R_pres : ∀ x ∈ R, Pres AA x := by
  rw [R_eq]
  refine pres_closure AA fun g hg => ?_
  obtain ⟨j, hj, hgj⟩ := List.getElem_of_mem hg
  have := gen_pres j hj
  rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some, hgj] at this

open Certificates in
open CFSG.ComponentClassification.PSL3Four in
theorem facts : ∃ P : Subgroup (Equiv.Perm (Fin 42)), P ≤ S ∧ Nat.card P = 64 ∧
    ∀ x ∈ R, (∀ p ∈ P, x * p = p * x) → x ∈ P := by
  refine ⟨P, P_le, (clos.2.2 ((allN_iff _ _).1 closedB)).1, fun x hx hxc => ?_⟩
  have hcomm : ∀ g ∈ ps, x * g = g * x := fun g hg =>
    hxc g (Subgroup.subset_closure hg)
  have hl := centDfs_sound hw hn ps hPC ((allN_iff _ _).1 uwB) covB ((allN_iff _ _).1 orbB) dfsB
    x hcomm
  have hp := (presE_iff hw' AA x).2 fun a b hab => R_pres x hx a b hab
  obtain ⟨k, hk, hxk⟩ := (CFSG.KC.LQT.P.anyN_iff 64 fun k => Nat.beq (wcode 6 x) (E k)).1
    ((CFSG.KC.LQT.P.impB_iff.1 hl) hp)
  obtain ⟨y, hy, hyc⟩ := clos.1 k hk
  rw [enc.inj (hyc.trans (Nat.eq_of_beq_eq_true hxk).symm)] at hy
  exact hy

end CertificateChecks.KernelMisc.SylCent

end
