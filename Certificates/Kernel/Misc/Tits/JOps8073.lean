
module

public import Certificates.Kernel.Misc.Tits.JVcPts8073

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.TitsJT.V

open CFSG CFSG.Quasithin CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native CFSG.Sporadic.Schreier.Tits
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CertificateChecks.KernelSpor
open CertificateChecks.KernelSpor.Tits2264 CertificateChecks.KernelSpor.Tits2268
open CertificateChecks.KernelEvenBN CertificateChecks.KernelMisc.TitsJT
open scoped commutatorElement

theorem mulT {i j : ℕ} (hi : i < 512) (hj : j < 512) :
    (jMulT[i]!)[j]! < 512 ∧ el (jMulT[i]!)[j]! = el i * el j := by
  obtain ⟨k, hk, ek, ik⟩ := jIdx4_of (mul_mem (el_mem hi) (el_mem hj))
  have e : (jMulT[i]!)[j]! = k := by
    rw [jMulT, getElem!_ofFn_of_lt _ hi, getElem!_ofFn_of_lt _ hj]
    simp only [Fin.getElem!_fin]
    rw [prod_pt hi hj (p := 5) (by norm_num), prod_pt hi hj (p := 1) (by norm_num),
      prod_pt hi hj (p := 24) (by norm_num), prod_pt hi hj (p := 12) (by norm_num)]
    exact ik
  rw [e]
  exact ⟨hk, ek⟩

theorem invT {i : ℕ} (hi : i < 512) : jInvT[i]! < 512 ∧ el jInvT[i]! = (el i)⁻¹ := by
  obtain ⟨k, hk, ek, ik⟩ := jIdx_of (rep_invCandJ (el_rep hi)) (inv_mem (el_mem hi))
  have e : jInvT[i]! = k := by
    rw [jInvT, getElem!_ofFn_of_lt _ hi]
    exact ik
  rw [e]
  exact ⟨hk, ek⟩

theorem oneT : jOneI < 512 ∧ el jOneI = 1 := by
  obtain ⟨k, hk, ek, ik⟩ := jIdx_of rep_idA (one_mem titsJ)
  have e : jOneI = k := ik
  rw [e]
  exact ⟨hk, ek⟩

theorem zT : jZI < 512 ∧ el jZI = titsZ := by
  obtain ⟨k, hk, ek, ik⟩ := jIdx_of (titsZ_rep : Rep 1755 jZArr titsZ) z_mem
  have e : jZI = k := ik
  rw [e]
  exact ⟨hk, ek⟩

theorem cc_norm {x : Equiv.Perm (Fin 1755)} (hx : x ∈ titsJ) : cc * x * cc⁻¹ ∈ titsJ := by
  have h3 : ¬ (3 < 3) := by omega
  have := conj_mem (k := 3) (by omega) hx
  simpa only [gK, h3, ↓reduceIte] using this

theorem hGen_norm {k : ℕ} (hk : k < 3) {x : Equiv.Perm (Fin 1755)} (hx : x ∈ titsJ) :
    hGen k * x * (hGen k)⁻¹ ∈ titsJ := by
  have := conj_mem (k := k) (by omega) hx
  simpa only [gK, hk, ↓reduceIte] using this

theorem ccT {i : ℕ} (hi : i < 512) : jCcT[i]! < 512 ∧ el jCcT[i]! = cc * el i * cc⁻¹ := by
  have r := rep_compA (rep_compA cFacts.2.2.1 (el_rep hi)) (rep_invCandJ cFacts.2.2.1)
  obtain ⟨k, hk, ek, ik⟩ := jIdx_of r (cc_norm (el_mem hi))
  have e : jCcT[i]! = k := by
    rw [jCcT, getElem!_ofFn_of_lt _ hi]
    exact ik
  rw [e]
  exact ⟨hk, ek⟩

theorem cjT {k i : ℕ} (hk : k < 3) (hi : i < 512) :
    (jCjT[k]!)[i]! < 512 ∧ el (jCjT[k]!)[i]! = hGen k * el i * (hGen k)⁻¹ := by
  have ha := (hGenArr hk).2
  have r := rep_compA (rep_compA ha (el_rep hi)) (rep_invCandJ ha)
  obtain ⟨m, hm, em, im⟩ := jIdx_of r (hGen_norm hk (el_mem hi))
  have e : (jCjT[k]!)[i]! = m := by
    rw [jCjT, getElem!_ofFn_of_lt _ hk, getElem!_ofFn_of_lt _ hi]
    simp only [Fin.getElem!_fin]
    rw [genInv_get hk]
    exact im
  rw [e]
  exact ⟨hm, em⟩

theorem fv {n : ℕ} (h : n < 512) : ((finPt 512 n : Fin 512) : ℕ) = n := finPt_val h

theorem elF_inj {i j : Fin 512} (h : el i = el j) : i = j := Fin.ext (el_inj i.2 j.2 h)

theorem mul_val (i j : Fin 512) : (jOps.mul i j : ℕ) = (jMulT[(i : ℕ)]!)[(j : ℕ)]! :=
  fv (mulT i.2 j.2).1

theorem el_mulF (i j : Fin 512) : el (jOps.mul i j) = el i * el j := by
  rw [mul_val]
  exact (mulT i.2 j.2).2

theorem el_invF (i : Fin 512) : el (jOps.inv i) = (el i)⁻¹ := by
  have e : (jOps.inv i : ℕ) = jInvT[(i : ℕ)]! := fv (invT i.2).1
  rw [e]
  exact (invT i.2).2

theorem one_val : (jOps.one : ℕ) = jOneI := fv oneT.1

theorem el_oneF : el jOps.one = 1 := by
  rw [one_val]
  exact oneT.2

theorem el_zF : el jOps.zI = titsZ := by
  have e : (jOps.zI : ℕ) = jZI := fv zT.1
  rw [e]
  exact zT.2

theorem el_ccF (i : Fin 512) : el (jCc i) = cc * el i * cc⁻¹ := by
  have e : (jCc i : ℕ) = jCcT[(i : ℕ)]! := fv (ccT i.2).1
  rw [e]
  exact (ccT i.2).2

theorem cj_val (k : Fin 3) (i : Fin 512) : (jCj k i : ℕ) = (jCjT[(k : ℕ)]!)[(i : ℕ)]! :=
  fv (cjT k.2 i.2).1

theorem el_cjF (k : Fin 3) (i : Fin 512) : el (jCj k i) = hGen k * el i * (hGen k)⁻¹ := by
  rw [cj_val]
  exact (cjT k.2 i.2).2

theorem el_commF (i j : Fin 512) : el (jOps.comm i j) = ⁅el i, el j⁆ := by
  simp only [VOps.comm, el_mulF, el_invF, commutatorElement_def]

theorem elF_mem (i : Fin 512) : el i ∈ titsJ := el_mem i.2

theorem elF_surj {g : Equiv.Perm (Fin 1755)} (hg : g ∈ titsJ) : ∃ i : Fin 512, el i = g := by
  obtain ⟨i, hi, e⟩ := el_surj hg
  exact ⟨⟨i, hi⟩, e⟩

theorem jEB_eq (i : Fin 512) :
    jEB i = true ↔ ∀ j : Fin 512, jOps.comm i j = jOps.one ∨ jOps.comm i j = jOps.zI := by
  unfold jEB jEBarr
  rw [getElem!_ofFn_of_lt _ i.2]
  exact decide_eq_true_iff

theorem jFB_eq (i : Fin 512) :
    jFB i = true ↔ ∀ e : Fin 512, jEB e = true → jOps.mul i e = jOps.mul e i := by
  unfold jFB jFBarr
  rw [getElem!_ofFn_of_lt _ i.2]
  exact decide_eq_true_iff

theorem mem_Esub {x : Equiv.Perm (Fin 1755)} :
    x ∈ Esub ↔ x ∈ titsJ ∧ ∀ y ∈ titsJ, Grp.Z0 titsZ ⁅x, y⁆ := Iff.rfl

theorem Esub_le {x : Equiv.Perm (Fin 1755)} (hx : x ∈ Esub) : x ∈ titsJ := hx.1

theorem jEB_iff (i : Fin 512) : jEB i = true ↔ el i ∈ Esub := by
  rw [jEB_eq, mem_Esub]
  constructor
  · intro h
    refine ⟨elF_mem i, fun y hy => ?_⟩
    obtain ⟨j, rfl⟩ := elF_surj hy
    rcases h j with e | e
    · left
      rw [← el_commF, e, el_oneF]
    · right
      rw [← el_commF, e, el_zF]
  · rintro ⟨-, h⟩ j
    rcases h (el j) (elF_mem j) with e | e
    · left
      exact elF_inj (by rw [el_commF, el_oneF, e])
    · right
      exact elF_inj (by rw [el_commF, el_zF, e])

theorem jFB_iff (i : Fin 512) : jFB i = true ↔ ∀ e ∈ Esub, Commute (el i) e := by
  rw [jFB_eq]
  constructor
  · intro h e he
    obtain ⟨k, rfl⟩ := elF_surj (Esub_le he)
    have := h k ((jEB_iff k).2 he)
    unfold Commute SemiconjBy
    rw [← el_mulF, ← el_mulF, this]
  · intro h e he
    exact elF_inj (by rw [el_mulF, el_mulF]; exact h _ ((jEB_iff e).1 he))

end CertificateChecks.KernelMisc.TitsJT.V

end
