
module

public import CFSG.Certificates.Kernel.WittConjSound
public import Certificates.Kernel.LocalComp.WittDataL34
public import Certificates.Kernel.Sporadic.M22Syl.Facts
public import CFSG.Quasithin.Recognition.L34AmalgamCasesInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelLC.Witt

open Equiv CFSG.KC.WCnt CFSG.KS.PCnt CFSG.ComponentClassification.WittDesign
  CFSG.Quasithin.L34Amalgam CertificateChecks.KernelSpor.M22Syl

set_option maxRecDepth 400000
theorem pk_gen : ∀ j : Fin 5, pkw 5 ((gen j : M22) : Perm (Fin 22)) = genP.getD j.val 0 := by
  decide +kernel

theorem pk_genI : ∀ j : Fin 5, pkw 5 ((gen j : M22) : Perm (Fin 22))⁻¹ = genIP.getD j.val 0 := by
  decide +kernel

theorem pk_t1 : pkw 5 ((bT1 : M22) : Perm (Fin 22)) = t1P := by
  decide +kernel

theorem coe_evalW (w : List (Fin 5 × Bool)) : ((evalW gen w : M22) : Perm (Fin 22)) =
    (w.map fun x => cond x.2 ((gen x.1 : M22) : Perm (Fin 22)) ((gen x.1 : M22) : Perm (Fin 22))⁻¹).prod := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    have e : evalW gen (x :: w) = cond x.2 (gen x.1) (gen x.1)⁻¹ * evalW gen w := by
      simp only [evalW, List.map_cons, List.prod_cons]
    rw [e, Subgroup.coe_mul, ih, List.map_cons, List.prod_cons]
    cases x.2 <;> rfl

theorem pk_evalW (w : List (Fin 5 × Bool)) :
    pkw 5 ((evalW gen w : M22) : Perm (Fin 22)) = pevalW genP genIP I w := by
  rw [coe_evalW, pevalW_pkw _ genP genIP I pk_gen pk_genI pk_one]

theorem bPk_eq : bWords.map (fun s => pevalW genP genIP I (word s)) = bPk :=
  (eqL_iff _ _).1 (by quickRfl)

theorem cbP_eq : cbWords.map (fun s => pevalW genP genIP I (word s)) = cbP :=
  (eqL_iff _ _).1 (by quickRfl)

theorem finRange12 : List.finRange 12 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] := by
  simp [List.finRange_succ]

theorem repP_eq : (List.finRange 12).map (fun i => pevalW genP genIP I (word (repStr i))) = repP := by
  rw [finRange12]
  exact (eqL_iff _ _).1 (by quickRfl)

theorem tab_getD (g : M22) (x : Fin 22) : (tab g).getD x.val 0 = (g : Perm (Fin 22)) x := by
  simp [tab, Array.getD_eq_getD_getElem?]

@[expose] def bPerms : List (Perm (Fin 22)) := bWords.map fun s => ((evalW gen (word s) : M22) : Perm (Fin 22))
@[expose] def cbPerms : List (Perm (Fin 22)) := cbWords.map fun s => ((evalW gen (word s) : M22) : Perm (Fin 22))
@[expose] def repPerms : List (Perm (Fin 22)) := (List.finRange 12).map fun i => ((rep i : M22) : Perm (Fin 22))

theorem bPk_map : bPerms.map (pkw 5) = bPk := by
  rw [← bPk_eq, bPerms, List.map_map]
  refine List.map_congr_left fun s _ => ?_
  rw [Function.comp_apply]
  exact pk_evalW _

theorem cbP_map : cbPerms.map (pkw 5) = cbP := by
  rw [← cbP_eq, cbPerms, List.map_map]
  refine List.map_congr_left fun s _ => ?_
  rw [Function.comp_apply]
  exact pk_evalW _

theorem repP_map : repPerms.map (pkw 5) = repP := by
  rw [← repP_eq, repPerms, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  rw [Function.comp_apply, rep]
  exact pk_evalW _

theorem bTabs_iff (τ : Perm (Fin 22)) :
    (∃ T ∈ bTabs, ∀ x : Fin 22, τ x = T.getD x.val 0) ↔ memN bPk (pkw 5 τ) = true := by
  rw [← bPk_map, memN_pkw, bTabs, bPerms, exists_mem_map', List.mem_map]
  refine exists_congr fun s => and_congr_right fun _ => ?_
  simp only [tab_getD]
  exact ⟨fun h => (Equiv.ext h).symm, fun h x => by rw [h]⟩

theorem conj_tab (g r : M22) (σ : Perm (Fin 22)) :
    (∀ x : Fin 22, (tab g).getD (σ x).val 0 = (tab r).getD ((tab g).getD x.val 0).val 0) ↔
      (g : Perm (Fin 22)) * σ = (r : Perm (Fin 22)) * (g : Perm (Fin 22)) := by
  simp only [tab_getD]
  exact ⟨fun h => Equiv.ext h, fun h x => by simpa using congrArg (fun f : Perm (Fin 22) => f x) h⟩

theorem bConj_iff (σ : Perm (Fin 22)) :
    (∃ T ∈ bTabs, ∀ x : Fin 22, T.getD (σ x).val 0 = (tab bT1).getD (T.getD x.val 0).val 0) ↔
      conjAny bPk [t1P] (pkw 5 σ) = true := by
  have e : [t1P] = [((bT1 : M22) : Perm (Fin 22))].map (pkw 5) := by rw [List.map_singleton, pk_t1]
  rw [← bPk_map, e, conjAny_pkw_iff, bTabs, bPerms, exists_mem_map', exists_mem_map']
  refine exists_congr fun s => and_congr_right fun _ => ?_
  rw [conj_tab]
  simp

theorem cbConj_iff (σ : Perm (Fin 22)) :
    (∃ T ∈ cbTabs, ∃ R ∈ repTabs, ∀ x : Fin 22,
      T.getD (σ x).val 0 = R.getD (T.getD x.val 0).val 0) ↔ conjAny cbP repP (pkw 5 σ) = true := by
  rw [← cbP_map, ← repP_map, conjAny_pkw_iff, cbTabs, cbPerms, repTabs, repPerms,
    exists_mem_map', exists_mem_map']
  refine exists_congr fun s => and_congr_right fun _ => ?_
  rw [exists_mem_map', exists_mem_map']
  exact exists_congr fun i => and_congr_right fun _ => conj_tab _ _ σ

end CertificateChecks.KernelLC.Witt

end
