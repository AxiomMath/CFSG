
module

public import Certificates.Kernel.LocalComp.WittL34
public import CFSG.Quasithin.Recognition.L34AmalgamIsoRefInputs
public import CFSG.Quasithin.Recognition.L34AmalgamIsoGLInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelLC.Witt

open Equiv CFSG.KC.WCnt CFSG.KS.PCnt CFSG.ComponentClassification.WittDesign
  CFSG.Quasithin.L34Amalgam CertificateChecks.KernelSpor.M22Syl CFSG.KC.Enum

set_option maxRecDepth 100000
@[expose] def pkM (g : M22) : Nat := pkw 5 (g : Perm (Fin 22))

theorem pkM_inj {a b : M22} : pkM a = pkM b ↔ a = b := by
  unfold pkM
  rw [pkw5_inj, Subtype.ext_iff]

theorem pkM_mul (a b : M22) :
    pkM (a * b) = pcomp (nat_lit 22) (nat_lit 5) (nat_lit 31) (pkM a) (pkM b) := by
  unfold pkM
  rw [Subgroup.coe_mul, pcomp_pkw5]

theorem pkM_one : pkM 1 = I := pk_one

theorem app_pkM (g : M22) (i : Fin 22) : ((g : Perm (Fin 22)) i).val = pt (pkM g) i.val := by
  unfold pkM
  rw [pt_pkw]

theorem pkM_evalW (w : List (Fin 5 × Bool)) : pkM (evalW gen w) = pevalW genP genIP I w :=
  pk_evalW w

theorem pk_refa : pkM refa = refaP := by decide +kernel
theorem pk_refaI : pkM refa⁻¹ = refaIP := by decide +kernel
theorem pk_refb : pkM refb = refbP := by decide +kernel
theorem pk_refbI : pkM refb⁻¹ = refbIP := by decide +kernel
theorem pk_refE : pkM refE0 = refEP.getD 0 0 ∧ pkM refE1 = refEP.getD 1 0 ∧
    pkM refE2 = refEP.getD 2 0 ∧ pkM refE3 = refEP.getD 3 0 := by decide +kernel

theorem pk_selM (b : Bool) (g : M22) : pkM (selM b g) = cond b (pkM g) I := by
  cases b
  · rw [selM, if_neg Bool.false_ne_true, pkM_one, cond_false]
  · rw [selM, if_pos rfl, cond_true]

theorem crdP_ok : ∀ x : Fin 16, pcomp (nat_lit 22) (nat_lit 5) (nat_lit 31)
    (pcomp (nat_lit 22) (nat_lit 5) (nat_lit 31)
      (pcomp (nat_lit 22) (nat_lit 5) (nat_lit 31) (cond (bit 0 x) (refEP.getD 0 0) I)
        (cond (bit 1 x) (refEP.getD 1 0) I)) (cond (bit 2 x) (refEP.getD 2 0) I))
      (cond (bit 3 x) (refEP.getD 3 0) I) = crdP.getD x.val 0 := by
  decide +kernel

theorem pk_crd (x : Fin 16) : pkM (crd x) = crdP.getD x.val 0 := by
  obtain ⟨e0, e1, e2, e3⟩ := pk_refE
  rw [← crdP_ok x, crd, pkM_mul, pkM_mul, pkM_mul, pk_selM, pk_selM, pk_selM, pk_selM, e0, e1, e2,
    e3]

theorem pk_letter (c : Char) :
    pkM (if c = 'a' then refa else if c = 'b' then refb else refb⁻¹) =
      if c = 'a' then refaP else if c = 'b' then refbP else refbIP := by
  by_cases ha : c = 'a'
  · rw [if_pos ha, if_pos ha, pk_refa]
  · rw [if_neg ha, if_neg ha]
    by_cases hb : c = 'b'
    · rw [if_pos hb, if_pos hb, pk_refb]
    · rw [if_neg hb, if_neg hb, pk_refbI]

theorem pk_cOfWord_aux (l : List Char) : ∀ g : M22,
    pkM (l.foldl (fun g c => g * if c = 'a' then refa else if c = 'b' then refb else refb⁻¹) g) =
      pwordAB refaP refbP refbIP (pkM g) l := by
  induction l with
  | nil =>
    intro g
    rw [List.foldl_nil, pwordAB_nil]
  | cons c l ih =>
    intro g
    rw [List.foldl_cons, ih, pkM_mul, pk_letter, pwordAB_cons]

theorem pk_cOfWord (s : String) : pkM (cOfWord s) = pwordAB refaP refbP refbIP I s.toList := by
  rw [cOfWord, pk_cOfWord_aux, pkM_one]

theorem cwP_eq : cWords.map (fun s => pwordAB refaP refbP refbIP I s.toList) = cwP :=
  (eqL_iff _ _).1 (by quickRfl)

theorem cwP_map : cWords.map (fun s => pkM (cOfWord s)) = cwP := by
  rw [← cwP_eq]
  exact List.map_congr_left fun s _ => pk_cOfWord s

theorem ref_facts :
    (refa : Equiv.Perm (Fin 22)) 0 = 0 ∧ (refa : Equiv.Perm (Fin 22)) 1 = 1 ∧
      (refb : Equiv.Perm (Fin 22)) 0 = 0 ∧ (refb : Equiv.Perm (Fin 22)) 1 = 1 ∧
      refa * refa = 1 ∧ refb ^ 3 = 1 ∧ (refa * refb) ^ 5 = 1 := by
  simp only [Fin.ext_iff, app_pkM, ← pkM_inj, pow_succ, pow_zero, one_mul, pkM_mul, pkM_one,
    pk_refa, pk_refb]
  decide +kernel

theorem crd_facts : ∀ x : Fin 16, ((crd x : M22) : Equiv.Perm (Fin 22)) 0 = 0 ∧
    ((crd x : M22) : Equiv.Perm (Fin 22)) 1 = 1 := by
  simp only [Fin.ext_iff, app_pkM, pk_crd]
  decide +kernel

theorem crd_mul : ∀ x y : Fin 16, crd (bxor x y) = crd x * crd y := by
  simp only [← pkM_inj, pkM_mul, pk_crd]
  decide +kernel

theorem crd_eq_one : ∀ x : Fin 16, crd x = 1 → x = 0 := by
  simp only [← pkM_inj, pkM_one, pk_crd]
  decide +kernel

theorem crd_zero : crd 0 = 1 := by
  rw [← pkM_inj, pkM_one, pk_crd]
  decide +kernel

theorem crd_conj_a : ∀ x : Fin 16, refa * crd x * refa⁻¹ = crd (lin refA x) := by
  simp only [← pkM_inj, pkM_mul, pk_crd, pk_refa, pk_refaI]
  decide +kernel

theorem crd_conj_b : ∀ x : Fin 16, refb * crd x * refb⁻¹ = crd (lin refB x) := by
  simp only [← pkM_inj, pkM_mul, pk_crd, pk_refb, pk_refbI]
  decide +kernel

theorem cwP_nodup : cwP.Nodup := by decide +kernel

theorem cWords_inj : ∀ s ∈ cWords, ∀ t ∈ cWords, cOfWord s = cOfWord t → s = t := by
  have h := cwP_nodup
  rw [← cwP_map] at h
  intro s hs t ht e
  exact List.inj_on_of_nodup_map h hs ht (congrArg pkM e)

theorem cwP_closed : ∀ P ∈ cwP,
    (∃ Q ∈ cwP, pcomp (nat_lit 22) (nat_lit 5) (nat_lit 31) P refaP = Q) ∧
    (∃ Q ∈ cwP, pcomp (nat_lit 22) (nat_lit 5) (nat_lit 31) P refbP = Q) ∧
    ∃ Q ∈ cwP, pcomp (nat_lit 22) (nat_lit 5) (nat_lit 31) P refbIP = Q := by
  decide +kernel

theorem cWords_closed : ∀ s ∈ cWords, (∃ t ∈ cWords, cOfWord s * refa = cOfWord t) ∧
    (∃ t ∈ cWords, cOfWord s * refb = cOfWord t) ∧
      ∃ t ∈ cWords, cOfWord s * refb⁻¹ = cOfWord t := by
  have h := cwP_closed
  rw [← cwP_map] at h
  simp only [List.forall_mem_map, exists_mem_map'] at h
  simp only [← pkM_inj, pkM_mul, pk_refa, pk_refb, pk_refbI]
  exact h

theorem cwP_crd : ∀ P ∈ cwP, ∀ x : Fin 16, P = crdP.getD x.val 0 → x = 0 := by
  decide +kernel

theorem cWords_crd : ∀ s ∈ cWords, ∀ x : Fin 16, cOfWord s = crd x → x = 0 := by
  have h := cwP_crd
  rw [← cwP_map] at h
  simp only [List.forall_mem_map] at h
  simp only [← pkM_inj, pk_crd]
  exact h

theorem pk_gen' : ∀ j : Fin 5, pkM (gen j) = genP.getD j.val 0 := pk_gen
theorem pk_genI' : ∀ j : Fin 5, pkM (gen j)⁻¹ = genIP.getD j.val 0 := pk_genI

theorem crd_conj_gen : ∀ j : Fin 5, j ≠ 4 → ∀ x : Fin 16, ∃ y : Fin 16,
    gen j * crd x * (gen j)⁻¹ = crd y := by
  simp only [← pkM_inj, pkM_mul, pk_crd, pk_gen', pk_genI']
  decide +kernel

theorem cWords_one : cOfWord "" = 1 := by
  decide +kernel

theorem card_barC : cWords.Nodup ∧ cWords.length = 60 := by
  decide +kernel

end CertificateChecks.KernelLC.Witt

end
