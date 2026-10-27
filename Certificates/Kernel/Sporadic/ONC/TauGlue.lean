module

public import Certificates.Kernel.Sporadic.ONC.Tau
public import CFSG.Certificates.Kernel.Spor.ONTauSound
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONCoverInputs
public import CFSG.Sporadic.Recognition.ONMultiplierTables
import Certificates.Kernel.Sporadic.ONC.ChainBase

public section

namespace CertificateChecks.KernelSpor.ONC

open CFSG.KS.ONC CFSG.Sporadic.ON CFSG.Sporadic.Recognition.ONMultiplier
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONCover

@[expose] noncomputable def matJ :
    J →* Matrix (Fin 154) (Fin 154) (ZMod 3) :=
  (Units.coeHom _).comp J.subtype

theorem matJ_injective : Function.Injective matJ :=
  fun _ _ e => Subtype.ext (Units.ext e)

theorem genG_eq : genG = seedG ga gb := rfl

theorem onGenWords_getD (k : ℕ) : onGenWords.toList.getD k [] = onGenWords[k]! := by
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, getElem!_def]
  cases onGenWords[k]? <;> rfl

theorem onG_pairs :
    ∀ p ∈ tauPairs, (p.1.map onG).prod = (p.2.map onG).prod := by
  have hFA : ∀ c < 154, PV (FA c) := fun c hc =>
    pv_of_canon (CertificateChecks.KernelSpor.ON.canon_of CertificateChecks.KernelSpor.ON2.colsAK2
      (CertificateChecks.KernelSpor.ON.list_eq ONW.LA ONW.CA
        (CFSG.KS.allN_spec CertificateChecks.KernelSpor.ON2.listA2)) c hc)
  have hFB : ∀ c < 154, PV (FB c) := fun c hc =>
    pv_of_canon (CertificateChecks.KernelSpor.ON.canon_of CertificateChecks.KernelSpor.ON2.colsBK2
      (CertificateChecks.KernelSpor.ON.list_eq ONW.LB ONW.CB
        (CFSG.KS.allN_spec CertificateChecks.KernelSpor.ON2.listB2)) c hc)
  have h := relsK_sound (φ := matJ) (gA := ga) (gB := gb) tau_ok hFA hFB (fun r c => colA r c)
    (fun r c => colB r c)
  intro p hp
  have hlt : ∀ i ∈ p.1 ++ p.2, i < onGenWords.toList.length := by
    revert p
    decide
  have e : ∀ i, CFSG.Sporadic.Th.wordG (seedG ga gb) (onGenWords.toList.getD i []) = onG i := by
    intro i
    rw [onGenWords_getD, ← genG_eq]
    rfl
  have := matJ_injective (h p hp hlt)
  simpa only [e] using this

theorem lift_onGF_tauWords :
    ∀ w ∈ tauWords, FreeGroup.lift onGF (FreeGroup.mk w) = 1 := by
  have k0 := mul_inv_eq_one.2 (onG_pairs _ (List.mem_cons_self))
  have k1 := mul_inv_eq_one.2 (onG_pairs _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have k2 := mul_inv_eq_one.2
    (onG_pairs _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  simp only [tauPairs, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    mul_inv_rev, mul_assoc] at k0 k1 k2
  intro w hw
  simp only [tauWords, List.mem_cons, List.mem_nil_iff, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · simpa [ofCodes, FreeGroup.lift_mk, onGF, mul_assoc] using k0
  · simpa [ofCodes, FreeGroup.lift_mk, onGF, mul_assoc] using k1
  · simpa [ofCodes, FreeGroup.lift_mk, onGF, mul_assoc] using k2

end CertificateChecks.KernelSpor.ONC

end
