module

public import Certificates.Kernel.Ivk8NormP.M23Klein
public import Certificates.Kernel.Ivk8Norm.Final
public import CFSG.Certificates.Kernel.Ivk8NormPGlue
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12NormP
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.M23
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Defs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1AutModel
public import CFSG.Perm.CentralizerOrbit
public import CFSG.Sporadic.Ly.ThreeBCount
public import CFSG.Sporadic.Th.CertificateBase
public import CFSG.Sporadic.Th.CertificateBase1
public import CFSG.Sporadic.Th.KernelContractBase
public import CFSG.Sporadic.ThSchreier.FullAutCoreBase
public import CFSG.Sporadic.ThSchreier.KernelAutBase
public import CFSG.Sporadic.ThSchreier.KernelAutBase1

public section

namespace CFSG.KS.Ivk8NormP.M23

open CFSG.Certificates.Kernel.PkEnum CFSG.KS.Ivk8Norm CFSG.KS.Ivk8NormP CFSG.Sporadic.Schreier
  CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.KS.PK Subgroup

theorem gens_eq : gens.map pkp = [m23PermA, m23PermB] := by
  rw [eq_of_vals (l₂ := [codeV m23PermA, codeV m23PermB]) ch5253_m23_gens]
  simp [pkp_codeV]

theorem gens_mem : ∀ g ∈ [m23PermA, m23PermB], g ∈ CFSG.Blueprint.NativeSporadic.M23 := by
  rw [← m23Certificate_originalSubgroup]
  exact m23_gens_mem

theorem ev_mem (w : List ℤ) : pkp (evV gens w) ∈ CFSG.Blueprint.NativeSporadic.M23 := by
  rw [pkp_evV, gens_eq]
  exact evalCodes_mem _ gens_mem w

theorem a_eq : pkp a = m23PermA := by
  change pkp (gens.getD 0 (oneV 23)) = _
  rw [eq_of_vals (l₂ := [codeV m23PermA, codeV m23PermB]) ch5253_m23_gens]
  simp [pkp_codeV]

theorem strong_eq : m23CentQ1.strong.toList = strong.map pkp := by
  have e1 : m23CentQ1 = certificate (by decide) ((m23CentWords1.map (evV gens)).map pkp)
      m23CentChainWords1 #v[2, 0, 5, 4] (by decide) := by
    rw [← map_evalCodes, gens_eq]
    rfl
  rw [e1]
  exact certificate_strong_eq _ _ _ _ _ _ rfl

theorem mem_K_iff (y : Equiv.Perm (Fin 23)) :
    y ∈ m23CentQ1.originalSubgroup ↔ y ∈ (enumV strong #v[2, 0, 5, 4]).map pkp := by
  rw [← mem_enumeration_iff m23CentQ1 m23_oddcore_cent1.1,
    enumeration_eq_enumV m23CentQ1 strong strong_eq]
  rfl

theorem prime_dvd_2688 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ∣ 2688) : p = 3 ∨ p = 7 := by
  have e : (2688 : ℕ) = 2 ^ 7 * (3 * 7) := by norm_num
  rw [e] at h
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)) hp2
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h)

theorem xs_facts : (∀ x ∈ xs, pkp x * pkp x = 1) ∧
    ∀ x ∈ xs, ∀ y ∈ xs, pkp x * pkp y = pkp y * pkp x := by
  have h := ch5253_m23_xs
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · have := eq_of_not_difV (h.1 x hx)
    rwa [pkp_mulV, pkp_oneV] at this
  · have := eq_of_not_difV (h.2 x hx y hy)
    rwa [pkp_mulV, pkp_mulV] at this

theorem m23_noP
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∀ P W : Subgroup (Equiv.Perm (Fin 23)), P ≤ CFSG.Blueprint.NativeSporadic.M23 →
      W ≤ CFSG.Blueprint.NativeSporadic.M23 → Nat.card P = 2 ^ 7 → IsPGroup p W →
      P ≤ normalizer (W : Set (Equiv.Perm (Fin 23))) → W = ⊥ := by
  classical
  set S : Set (Equiv.Perm (Fin 23)) := {x | x ∈ xs.map pkp} with hS
  obtain ⟨hinv, hcomm⟩ := xs_facts
  have hinvS : ∀ x ∈ S, x * x = 1 := by
    rintro _ hz
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz
    exact hinv x hx
  have hcommS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    rintro _ hz _ hz'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz'
    exact hcomm x hx y hy
  have hxsH : ∀ x ∈ xs, pkp x ∈ closure S := fun x hx =>
    subset_closure (List.mem_map_of_mem hx)
  have haxs : a ∈ xs := List.mem_cons_self ..
  have hbxs : b' ∈ xs := List.mem_cons_of_mem _ (List.mem_map_of_mem (by simp [wH]))
  have hHS : closure S ≤ CFSG.Blueprint.NativeSporadic.M23 := by
    rw [closure_le]
    rintro _ hz
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz
    rcases List.mem_cons.1 hx with rfl | hx
    · rw [a_eq]
      exact gens_mem _ (by simp)
    · obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
      exact ev_mem w
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := kleinOK_spec ch5253_m23_klein
  have hHc : ∀ h ∈ closure S, h * pkp a = pkp a * h ∧ h * pkp b' = pkp b' * h := fun h hh =>
    ⟨comm_of_mem_closure hcommS h hh _ (hxsH a haxs),
      comm_of_mem_closure hcommS h hh _ (hxsH b' hbxs)⟩
  have hcent := CFSG.ClassicalInvolution.m23_cover_and_centralizers.2 _
    (List.mem_singleton_self _)
  have hrep : m23Rep1 = m23PermA := by
    simp [m23Rep1, m23InvReps, m23InvRepWords, evalCodes]
  have hK : ∀ x ∈ CFSG.Blueprint.NativeSporadic.M23, x * pkp a = pkp a * x →
      x ∈ m23CentQ1.originalSubgroup := by
    intro x hx hxr
    rw [a_eq] at hxr
    simp only at hcent
    rw [← hcent, hrep, m23Certificate_originalSubgroup]
    exact mem_centralizerIn.2 ⟨hx, hxr⟩
  have hKc : Nat.card m23CentQ1.originalSubgroup = 2688 := m23_rep_data1.2.2.2.1
  have hpK : ¬ p ^ 2 ∣ Nat.card m23CentQ1.originalSubgroup := by
    rw [hKc]
    intro h
    rcases prime_dvd_2688 hp hp2 ((dvd_pow_self p two_ne_zero).trans h) with rfl | rfl <;>
      norm_num at h
  have hcs : ∀ c ∈ [oneV 23, c1, c2].map pkp, c ∈ CFSG.Blueprint.NativeSporadic.M23 := by
    intro c hc
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · rw [pkp_oneV]
      exact one_mem _
    · exact ev_mem wC1
    · exact ev_mem wC2
  have hconj := ch5253_m23_conj
  simp only [Bool.and_eq_true] at hconj
  have hc1 := eq_of_not_difV hconj.1
  have hc2 := eq_of_not_difV hconj.2
  rw [pkp_conjV] at hc1 hc2
  rw [pkp_mulV] at hc2
  have hcov : ∀ e ∈ [pkp a, pkp b', pkp a * pkp b'], ∃ c ∈ [oneV 23, c1, c2].map pkp,
      c * pkp a * c⁻¹ = e := by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact ⟨pkp (oneV 23), by simp, by rw [pkp_oneV]; group⟩
    · exact ⟨pkp c1, by simp, hc1⟩
    · exact ⟨pkp c2, by simp, hc2⟩
  have hw := ch5253_m23_w
  simp only [wAll, Bool.and_eq_true] at hw
  have hwd : wd 23 = 5 := by decide
  have hN : ∀ y ∈ m23CentQ1.originalSubgroup, ∀ c ∈ [oneV 23, c1, c2].map pkp, orderOf y = p →
      ∃ h ∈ closure S, h ∉ normalizer (zpowers (c * y * c⁻¹) : Set (Equiv.Perm (Fin 23))) := by
    intro y hy c hc hyo
    have hp37 : p = 3 ∨ p = 7 := by
      refine prime_dvd_2688 hp hp2 ?_
      rw [← hKc, ← hyo, ← Subgroup.orderOf_mk y hy]
      exact orderOf_dvd_natCard _
    obtain ⟨y', hy', rfl⟩ := List.mem_map.1 ((mem_K_iff y).1 hy)
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hc
    have key : ∀ c' : VP 23, (chkP 23 5 p (wits c' xs) enum = true) →
        ∃ h ∈ closure S, h ∉ normalizer
          (zpowers (pkp c' * pkp y' * (pkp c')⁻¹) : Set (Equiv.Perm (Fin 23))) := by
      intro c' hck
      rw [← hwd] at hck
      exact hN_of_chkP (by norm_num) (by rw [hwd]; norm_num) hp hxsH c' hck y' hy' hyo
    rcases hp37 with rfl | rfl <;> rcases hc with rfl | rfl | rfl
    · exact key _ hw.1.1.1.1.1
    · exact key _ hw.1.1.1.2
    · exact key _ hw.1.2
    · exact key _ hw.1.1.1.1.2
    · exact key _ hw.1.1.2
    · exact key _ hw.2
  have hS₀ : ¬ 2 ^ (7 + 1) ∣ Nat.card CFSG.Blueprint.NativeSporadic.M23 := by
    rw [m23_card]
    norm_num
  exact CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.noP_of_cent le_rfl hp hp2 (hxsH a haxs)
    (hxsH b' hbxs) h1 h2 h3 h4 h5 h6 (isPGroup_two_closure hinvS hcommS) hHS hHc hK hpK hcs hcov
    hN hS₀

end CFSG.KS.Ivk8NormP.M23

end
