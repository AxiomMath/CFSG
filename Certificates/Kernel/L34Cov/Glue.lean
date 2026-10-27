
module

public import CFSG.Certificates.Kernel.L34Cov.CovSound
public import Certificates.Kernel.Multipliers.L34Lower
public import Certificates.Kernel.L34Cov.Checks

public section

namespace CertificateChecks.KernelL34Cov

open CFSG.KC CFSG.KC.L34Cov CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable
open CFSG.Certificates.CosetEnumeration CFSG.Certificates.L34Cov CertificateChecks.KernelL34
open CFSG.ComponentClassification.GrSLit.L34Facts

theorem monoModel_of {T C : ℕ → ℕ} {a₁ a₂ : ZMod 4}
    (hp : Mono.paramsOK 960 4 C rels.length = true)
    (h : ∀ x < 960,
      Mono.pointOK T 2 960 4 C CFSG.KC.L34Alt.relCodes CFSG.KC.L34Alt.coverCodes x = true)
    (hx : (C 1 : ZMod 4) = 0 ∧ (C 0 : ZMod 4) + C 5 = a₁ ∧ (C 0 : ZMod 4) + C 6 = a₂ ∧
      (C 0 : ZMod 4) + C 0 = 0) :
    MonoModel T a₁ a₂ := by
  obtain ⟨ψ, hrel, hwalk⟩ := mono_model rels (fun i => commWords (coverPairs i)) relCodes_eq
    coverCodes_eq hp h
  have hR : ∀ k < 7, IsTr (ψ (PresentedGroup.mk _ (FreeGroup.mk (rels.getD k [])))) (C k) := by
    intro k hk p
    rw [List.getD_eq_getElem _ _ (by rw [rels_length]; exact hk)]
    exact hrel k _ p
  have hpair : ∀ i j, i < 7 → j < 7 →
      IsTr (ψ (PresentedGroup.mk _ (FreeGroup.mk (rels.getD i [] ++ rels.getD j []))))
        ((C i : ZMod 4) + C j) := by
    intro i j hi hj
    rw [← FreeGroup.mul_mk, map_mul, map_mul]
    exact (hR i hi).mul (hR j hj)
  have e1 : bFive = rels.getD 1 [] := by decide +kernel
  have e5 : zOne = rels.getD 0 [] ++ rels.getD 5 [] := by decide +kernel
  have e6 : zTwo = rels.getD 0 [] ++ rels.getD 6 [] := by decide +kernel
  have e0 : zThree = rels.getD 0 [] ++ rels.getD 0 [] := by decide +kernel
  have h40 : (4 : ZMod 4) = 0 := by decide
  obtain ⟨φ, hφ⟩ := descend ψ (fun r hr => by
    simp only [extraWs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [e1]
      exact (hx.1 ▸ hR 1 (by norm_num)).eq_one
    · rw [mk_wpow, map_pow, map_pow, e5]
      have := (hpair 0 5 (by norm_num) (by norm_num)).pow 4
      rw [Nat.cast_ofNat, h40, zero_mul] at this
      exact this.eq_one
    · rw [mk_wpow, map_pow, map_pow, e6]
      have := (hpair 0 6 (by norm_num) (by norm_num)).pow 4
      rw [Nat.cast_ofNat, h40, zero_mul] at this
      exact this.eq_one
    · rw [mk_wpow, map_pow, map_pow, e0]
      have := (hpair 0 0 (by norm_num) (by norm_num)).pow 3
      rw [hx.2.2.2, mul_zero] at this
      exact this.eq_one)
  refine ⟨φ, ?_, ?_, ?_, fun u x => ?_⟩
  · change IsTr (φ (PresentedGroup.mk _ (FreeGroup.mk zOne))) a₁
    rw [hφ, e5, ← hx.2.1]
    exact hpair 0 5 (by norm_num) (by norm_num)
  · change IsTr (φ (PresentedGroup.mk _ (FreeGroup.mk zTwo))) a₂
    rw [hφ, e6, ← hx.2.2.1]
    exact hpair 0 6 (by norm_num) (by norm_num)
  · change IsTr (φ (PresentedGroup.mk _ (FreeGroup.mk zThree))) 0
    rw [hφ, e0, ← hx.2.2.2]
    exact hpair 0 0 (by norm_num) (by norm_num)
  · change _ = ((φ (PresentedGroup.mk _ (FreeGroup.mk u))).unop (x, 0)).1.val +
      Nat.shiftLeft ((φ (PresentedGroup.mk _ (FreeGroup.mk u))).unop (x, 0)).2.val 16
    rw [hφ]
    exact hwalk u x

theorem modelA : MonoModel CFSG.KD.L34F4a.Tab 3 2 :=
  monoModel_of CFSG.KD.L34F4a.sQ pointsF4a (by decide +kernel)

theorem modelB : MonoModel CFSG.KD.L34F4b.Tab 0 1 :=
  monoModel_of CFSG.KD.L34F4b.sQ pointsF4b (by decide +kernel)

theorem cv_eq_of_cvId {w : List (Fin 2 × Bool)} {c₁ c₂ c₃ : ℕ}
    (h : cvId w c₁ c₂ c₃ = true) : cv w = z₁ ^ c₁ * z₂ ^ c₂ * z₃ ^ c₃ :=
  cv_eq_of_cvIdOK vt_k modelA modelB h

theorem zz_eq :
    cv (wpow zOne 2 ++ wpow zTwo 2) = z₁ ^ 2 * z₂ ^ 2 * z₃ ^ 0 :=
  cv_eq_of_cvId zz_k

theorem cover_eq :
    cv ((0, false) :: commWords (coverPairs 0)) = z₁ ^ 0 * z₂ ^ 0 * z₃ ^ 0 :=
  cv_eq_of_cvId cover_k.1

end CertificateChecks.KernelL34Cov

end
