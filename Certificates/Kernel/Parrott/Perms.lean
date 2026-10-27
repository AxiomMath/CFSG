module

public import Certificates.Kernel.Parrott.All
public import Certificates.Kernel.Misc.Coset.C10009

public section

namespace CertificateChecks.KernelParrott

open CFSG.KC.MiscCoset CFSG.Literature.ParrottTits CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2
  CFSG.Certificates CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KAct.P2004
open CertificateChecks.KernelMiscCoset.C10009 (signedProd_map wordIn_eq permOfArr_eq)

theorem perms : ∃ x : ℕ → Equiv.Perm (Fin 1755),
    (∀ w ∈ parrottWords, FreeGroup.lift (fun i : Fin 10 => x i) (FreeGroup.mk w) = 1) ∧
    ∀ j < 2, permOfArr 1755 titsDerivedArrs[j]! =
      wordIn 10 x ([parrottD0Word, parrottD1Word].getD j []) := by
  have hpt := Act.pointOK_of_allR all
  obtain ⟨σ, hσ⟩ := Act.exists_rep hpt
  have hw := Act.relsAt_sound hσ permWords rfl (fun x hx => Act.relsAt_of_pointOK (hpt x hx))
  have hb := Act.allR_spec bind
  have hδ : ∀ j (hj : j < 2), permOfArr 1755 titsDerivedArrs[j]! = σ (e2 ⟨j, hj⟩) := by
    intro j hj
    rw [CertificateChecks.KernelMisc.TitsText.titsDerivedArrs_get (by omega)]
    apply permOfArr_eq
    intro x
    have hx := hb x.val (Nat.zero_le _) (by simpa using x.2)
    simp only [Act.andB_eq, Bool.and_eq_true] at hx
    rw [unpack, getElem!_ofFn_nat _ x.2]
    have hr := (hσ (e2 ⟨j, hj⟩) x).1
    interval_cases j
    · exact (Nat.eq_of_beq_eq_true hx.1).symm.trans hr
    · exact (Nat.eq_of_beq_eq_true hx.2).symm.trans hr
  let x : ℕ → Equiv.Perm (Fin 1755) := fun i => if h : i < 10 then σ (sh ⟨i, h⟩) else 1
  have hx : (fun h : Fin 10 => x h) = fun h => σ (sh h) := by
    funext h
    simp [x, h.isLt]
  refine ⟨x, fun w hw' => ?_, fun j hj => ?_⟩
  · have h1 := hw _ (List.mem_append_left _ (List.mem_map.2 ⟨w, hw', rfl⟩))
    rw [signedProd_map] at h1
    rw [lift_mk_eq_signedProd, hx, h1]
  · have h1 := hw _ (List.mem_append_right _ (List.mem_map.2 ⟨⟨j, hj⟩, List.mem_finRange _, rfl⟩))
    rw [signedProd_cons, signedProd_map] at h1
    simp only [Bool.false_eq_true, ↓reduceIte] at h1
    rw [hδ j hj, wordIn_eq, hx, inv_mul_eq_one.1 h1]

end CertificateChecks.KernelParrott

end
