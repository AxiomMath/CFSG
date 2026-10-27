module

public import Certificates.Kernel.SporSch.J1.Chain2165
public import Certificates.Kernel.SporSch.J1.Gen
public import Certificates.Kernel.SporSch.GenPerms
public import CFSG.Certificates.Kernel.SporSch.J1VecSound
public import CFSG.Sporadic.Schreier.J1VecCheckInputs
public meta import CFSG.Sporadic.Schreier.J1CertLit
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.J1

meta def vecsM : Array (Array Nat) := (CFSG.Sporadic.Schreier.j1VecsLit.map List.toArray).toArray

end CertificateChecks.KernelSporSch.J1

#kss_perms CertificateChecks.KernelSporSch.J1V 4 CertificateChecks.KernelSporSch.J1.vecsM

#kss_sortorder CertificateChecks.KernelSporSch.J1O 4 CertificateChecks.KernelSporSch.J1.vecsM

namespace CertificateChecks.KernelSporSch.J1

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.J1Vec
open CFSG.Sporadic.Schreier CFSG.ProperTwoGeneratedCore CFSG.Monster.B.Mathieu Matrix

@[expose] def MP1 : Nat := 1201695450996210055023234375256575189561039091404721789296

@[expose] def MP2 : Nat := 58288780428934443338682154398748644057433705475408958685557

theorem vb : vbindK j1VecsLit J1V 3080 = true := by quickRfl

theorem vs : sortK J1V J1O 3080 = true := by quickRfl

theorem vnz : nzK J1V 3080 = true := by quickRfl

theorem mv1 : mvK MP1 J1V (J1C.S 0) 3080 = true := by quickRfl

theorem mv2 : mvK MP2 J1V (J1C.S 1) 3080 = true := by quickRfl

theorem hM1 : ∀ r c : Fin 7, j1_first_matrix r c = ((me MP1 r c : Nat) : ZMod 11) := by
  intro r c
  fin_cases r <;> fin_cases c <;> decide

theorem hM2 : ∀ r c : Fin 7, j1_second_matrix r c = ((me MP2 r c : Nat) : ZMod 11) := by
  intro r c
  fin_cases r <;> fin_cases c <;> decide

set_option maxRecDepth 100000 in
theorem vectors_eq : J1Certificate.vectors = j1VecsLit := by
  delta J1Certificate j1CertLit
  rfl

theorem vec_eq (i : Fin 3080) : j1Vec i = fun j : Fin 7 => ((vf (J1V i) j : Nat) : ZMod 11) := by
  funext j
  unfold j1Vec
  rw [vectors_eq, ((vbindK_sound vb).2 i i.2).2.1 j j.2]

theorem gen_get (k : Nat) (hk : k < 2) (i : Nat) (hi : i < 3080) :
    (J1Certificate.chain.generators.getD k []).getD i 0 = pg 12 (mask 12) (J1C.S k) i := by
  have hb := (bAnd_iff _ _).1 (allN_spec genOK k hk)
  have hl : (j1Chain.generators.getD k []).length = 3080 := by
    rw [← lenK_eq]
    exact Nat.eq_of_beq_eq_true hb.1
  rw [chain_eq, List.getD_eq_getElem _ _ (by rw [hl]; exact hi),
    bindFromK_spec hb.2 i (by rw [hl]; exact hi), Nat.zero_add]

theorem pg_lt (k : Nat) (hk : k < 4) (i : Nat) (hi : i < 3080) :
    pg 12 (mask 12) (J1C.S k) i < 3080 := by
  have hc : canonK 3080 12 (mask 12) (3080 * 12) (J1C.S k) = true :=
    ((bAnd_iff _ _).1 (allN_spec canonOK k hk)).1
  unfold canonK at hc
  have ha : allN 3080 (fun i => Nat.blt (pg 12 (mask 12) (J1C.S k) i) 3080) = true :=
    ((bAnd_iff _ _).1 ((bAnd_iff (szOK 3080 12) _).1 hc).2).2
  have h4 := allN_spec ha i hi
  simpa only [Nat.blt_eq] using h4

theorem idx_eq (k : Nat) (hk : k < 2) (i : Fin 3080) :
    (j1Idx (J1Certificate.chain.generators.getD k []) i : Nat) = pg 12 (mask 12) (J1C.S k) i := by
  simp only [j1Idx]
  rw [gen_get k hk i i.2, Nat.mod_eq_of_lt (pg_lt k (by omega) i i.2)]

theorem mulVec_of {M : Matrix (Fin 7) (Fin 7) (ZMod 11)} {MP : Nat} {k : Nat} (hk : k < 2)
    (hM : ∀ r c : Fin 7, M r c = ((me MP r c : Nat) : ZMod 11))
    (h : mvK MP J1V (J1C.S k) 3080 = true) (i : Fin 3080) :
    M *ᵥ j1Vec i = j1Vec (j1Idx (J1Certificate.chain.generators.getD k []) i) := by
  rw [vec_eq, vec_eq, idx_eq k hk]
  exact mvK_sound hM h i i.2

theorem basis_eq : j1BasisMat = Matrix.of fun r c : Fin 7 => ((vf (J1V c) r : Nat) : ZMod 11) := by
  ext r c
  unfold j1BasisMat
  rw [Matrix.of_apply, Matrix.of_apply, vec_eq]
  rfl

theorem vecFacts : (J1Certificate.vectors.Nodup)
    ∧ (∀ i : Fin 3080, j1Vec i ≠ 0)
    ∧ (∀ i : Fin 3080, j1_first_matrix *ᵥ j1Vec i = j1Vec (j1Idx j1A1List i))
    ∧ (∀ i : Fin 3080, j1_second_matrix *ᵥ j1Vec i = j1Vec (j1Idx j1A2List i))
    ∧ (j1BasisMat * j1BasisInv = 1) := by
  refine ⟨?_, fun i => ?_, mulVec_of (k := 0) (by norm_num) hM1 mv1,
    mulVec_of (k := 1) (by norm_num) hM2 mv2, ?_⟩
  · rw [vectors_eq]
    exact nodup_sound vb vs
  · rw [vec_eq]
    exact nzK_sound vnz i i.2
  · rw [basis_eq]
    ext r c
    fin_cases r <;> fin_cases c <;> decide

end CertificateChecks.KernelSporSch.J1

end
