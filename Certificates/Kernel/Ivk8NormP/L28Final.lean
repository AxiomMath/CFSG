module

public import Certificates.Kernel.Ivk8NormP.L28
public import CFSG.Certificates.Kernel.Ivk8NormPCGlue
public import CFSG.GH74.KGroups.L28
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12Norm

public section

namespace CFSG.KS.Ivk8NormP.L28

open CFSG.Certificates.Kernel.PkEnum CFSG.KS.Ivk8Norm CFSG.KS.Ivk8NormP CFSG.Sporadic.Schreier
  CFSG.Certificates CFSG.KS.PK Subgroup CFSG.GH74.KGroups.L28

theorem gens_eq : gens.map pkp = [pa, pb, sg] := by
  rw [eq_of_vals (l₂ := [codeV pa, codeV pb, codeV sg]) ch5253_l28_gens]
  simp [pkp_codeV]

theorem a_eq : pkp a = pa := by
  change pkp (gens.getD 0 (oneV 9)) = _
  rw [eq_of_vals (l₂ := [codeV pa, codeV pb, codeV sg]) ch5253_l28_gens]
  simp [pkp_codeV]

theorem QA_eq : QA.originalSubgroup = closure {pa, pb, sg} := by
  rw [QA, certificate_originalSubgroup]
  congr 1
  ext g
  simp

theorem gens_mem : ∀ g ∈ [pa, pb, sg], g ∈ QA.originalSubgroup := fun g hg => by
  rw [QA_eq]
  exact subset_closure (by simpa using hg)

theorem ev_mem (w : List ℤ) : pkp (evV gens w) ∈ QA.originalSubgroup := by
  rw [pkp_evV, gens_eq]
  exact evalCodes_mem _ gens_mem w

theorem ev_memP (w : List ℤ) (hw : ∀ z ∈ w, z ≠ 0 ∧ z.natAbs ≤ 2) :
    pkp (evV gens w) ∈ QP.originalSubgroup := by
  rw [pkp_evV, gens_eq, QP_closure]
  refine CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.evalCodes_mem_prefix (m := 2) (fun i hi => ?_) w hw
  interval_cases i
  · exact subset_closure (by simp)
  · exact subset_closure (by simp)

theorem strong_eq : QA.strong.toList = strong.map pkp := by
  have e1 : QA = certificate (by decide) (gens.map pkp) qaWords #v[0, 1, 2, 3] (by decide) := by
    rw [gens_eq]
    rfl
  rw [e1]
  exact certificate_strong_eq _ _ _ _ _ _ rfl

theorem mem_iff (y : Equiv.Perm (Fin 9)) :
    y ∈ QA.originalSubgroup ↔ y ∈ (enumV strong #v[0, 1, 2, 3]).map pkp := by
  rw [← mem_enumeration_iff QA QA_ok, enumeration_eq_enumV QA strong strong_eq]
  rfl

theorem mem_ps {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ∣ 1512) : p ∈ [3, 7] := by
  have hpm : p ∈ Nat.primeFactorsList 1512 :=
    (Nat.mem_primeFactorsList (by norm_num)).2 ⟨hp, h⟩
  have hf : Nat.primeFactorsList 1512 = [2, 2, 2, 3, 3, 3, 7] := by norm_num
  rw [hf] at hpm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpm ⊢
  omega

theorem l28_noP {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∀ P W : Subgroup (Equiv.Perm (Fin 9)), P ≤ QP.originalSubgroup → W ≤ QA.originalSubgroup →
      Nat.card P = 2 ^ 3 → IsPGroup p W → P ≤ normalizer (W : Set (Equiv.Perm (Fin 9))) →
      W = ⊥ := by
  have hwd : wd 9 = 4 := by decide
  have hcardA : Nat.card QA.originalSubgroup = 1512 := by
    rw [← QA.orderCertificate_eq_card QA_ok, QA_valid.2]
  have hcardP : Nat.card QP.originalSubgroup = 504 := by
    rw [← QP.orderCertificate_eq_card QP_ok, QP_valid.2]
  have hS₀G : QP.originalSubgroup ≤ QA.originalSubgroup := by
    rw [QP_closure, QA_eq]
    refine closure_mono ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg ⊢
    rcases hg with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hw : chkPC 9 (wd 9) a.1.1 [3, 7] [witsF (oneV 9) xs, witsF c1 xs, witsF c2 xs]
      ((enumV strong #v[0, 1, 2, 3]).map fun y => y.1.1) = true := by
    rw [hwd]
    exact ch5253_l28_w
  have hb : b' ∈ xs := List.mem_cons_of_mem _ (List.mem_map_of_mem (by simp [wX]))
  refine noP_of_chkPC (by norm_num) (by rw [hwd]; norm_num) hS₀G hp hp2 ch5253_l28_xs ?_
    List.mem_cons_self hb ch5253_l28_klein (ev_mem wCB) (ev_mem wCAB) ch5253_l28_conj
    (fun y hy => List.mem_map.1 ((mem_iff y).1 hy)) ?_ hw ?_
  · intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · rw [a_eq, QP_closure]
      exact subset_closure (by simp)
    · obtain ⟨w, hw', rfl⟩ := List.mem_map.1 hx
      refine ev_memP w ?_
      simp only [wX, List.mem_cons, List.not_mem_nil, or_false] at hw'
      rcases hw' with rfl | rfl <;> decide
  · intro y hy hyo
    refine mem_ps hp hp2 ?_
    rw [← hcardA, ← hyo, ← Subgroup.orderOf_mk y hy]
    exact orderOf_dvd_natCard _
  · rw [hcardP]
    norm_num

end CFSG.KS.Ivk8NormP.L28

end
