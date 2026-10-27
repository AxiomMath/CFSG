
module

public import Certificates.Kernel.Fin76bOm.Glue
public import Certificates.Kernel.Fin76bOm.AutE
public import CFSG.Certificates.Kernel.Fin76bOm.Transport
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WJ2Check
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WJ3Check
public import CFSG.Sporadic.SmallOddCore.J2
public import CFSG.Sporadic.SmallOddCore.J3Check

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelC24608

open Equiv Subgroup CFSG.KC.Fin76bOm CFSG.KC.YoshQ CFSG.KC.Enum CFSG.KS
open CFSG.EvenSporadicStandard.Fin76b CFSG.EvenSporadicStandard.Fin76b.W16
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.OddCore

@[expose] def j2OmI (l : ℕ) : ℕ := if l < 4 then 32 + l else 31

@[expose] noncomputable def j2Gs (l : ℕ) : Perm (Fin 315) := tp 315 (j2CentTbl (j2OmI l))

@[expose] noncomputable def j2Rs (l : ℕ) : Perm (Fin 32) := tp 32 (tabN 32 6 (J2OmT l))

theorem j2OmI_lt {l : ℕ} (hl : l < 5) : j2OmI l < 42 := by
  unfold j2OmI
  split <;> omega

theorem j2OmG_eq {l : ℕ} (hl : l < 5) : j2OmG l = J2CentT.F (j2OmI l) := by
  unfold j2OmG
  congr 1
  interval_cases l <;> rfl

theorem j2Gs_lt {l : ℕ} (hl : l < 4) : j2Gs l = tp 315 (j2CentTbl (32 + l)) := by
  rw [j2Gs, j2OmI, if_pos hl]

theorem j2_permOK {k : ℕ} (hk : k < 42) : permOK 315 (j2CentTbl k) = true :=
  List.all_eq_true.1 j2_permOK_all k (List.mem_range.2 hk)

theorem j2Om_permR {l : ℕ} (hl : l < 5) : permOK 32 (tabN 32 6 (J2OmT l)) = true := by
  rcases Nat.lt_or_ge l 4 with h | h
  · have h1 := j2Om_perm.2.1
    rw [Array.all_eq_true'] at h1
    exact h1 _ (List.mem_toArray.2 (List.mem_map.2
      ⟨J2OmT l, List.mem_map.2 ⟨l, List.mem_range.2 h, rfl⟩, rfl⟩))
  · obtain rfl : l = 4 := by omega
    exact j2Om_perm.1

theorem j2_gens_eq : tp 315 '' {x | x ∈ J2.wGensJ2} = j2Gs '' {l | l < 4} := by
  ext σ
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x ∈ [j2CentTbl 32, j2CentTbl 33, j2CentTbl 34, j2CentTbl 35] := List.mem_toArray.1 hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
    rcases hx' with h | h | h | h
    · exact ⟨0, by norm_num, by simp only [j2Gs_lt (l := 0) (by norm_num), h, Nat.reduceAdd]⟩
    · exact ⟨1, by norm_num, by simp only [j2Gs_lt (l := 1) (by norm_num), h, Nat.reduceAdd]⟩
    · exact ⟨2, by norm_num, by simp only [j2Gs_lt (l := 2) (by norm_num), h, Nat.reduceAdd]⟩
    · exact ⟨3, by norm_num, by simp only [j2Gs_lt (l := 3) (by norm_num), h, Nat.reduceAdd]⟩
  · rintro ⟨l, hl, rfl⟩
    have hl' : l < 4 := hl
    refine ⟨j2CentTbl (32 + l), List.mem_toArray.2 ?_, (j2Gs_lt hl').symm⟩
    interval_cases l <;> simp only [Nat.reduceAdd]
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self))

theorem j2Og_eq : tp 32 '' {x | x ∈ j2Og} = j2Rs '' {l | l < 4} := by
  ext σ
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 (List.mem_toArray.1 hx)
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hy
    exact ⟨l, List.mem_range.1 hl, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨_, List.mem_toArray.2 (List.mem_map.2
      ⟨J2OmT l, List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩, rfl⟩), rfl⟩

theorem j2Om_hg : ∀ l < 5, ∀ i : Fin 315,
    ((j2Gs l i : Fin 315) : ℕ) = pg 9 (mask 9) (j2OmG l) i := by
  intro l hl i
  rw [j2OmG_eq hl]
  exact tp_unpack (j2_permOK (j2OmI_lt hl)) (j2CentTbl_eq (j2OmI_lt hl)) i

theorem j2_omega : ∃ Ω : Fin 32 → Fin 315, Function.Injective Ω ∧
    ∀ l < 5, ∀ j, j2Gs l (Ω j) = Ω (j2Rs l j) :=
  restrData_of_checks (w := 9) (m := mask 9) (PT := J2OmP 0) (pw := 9) (pm := mask 9) (rw := 6)
    (rm := mask 6) (P := j2OmG) (R := J2OmT) j2Om_pts (fun l hl => allN_spec j2Om_restr l hl)
    j2Om_hg (fun l hl j => tp_tabN (by norm_num) (j2Om_permR hl) j)

theorem j2Om_card : Nat.card (closure (tp 32 '' {x | x ∈ j2Og})) = 1920 := by
  obtain ⟨hs, hsize⟩ := enumOK_spec (by norm_num) j2Om_recs.enumW
  rw [hs.card, hsize]

theorem j2_data :
    ∃ ht : tp 315 (j2CentTbl 31) ∈ j2P,
      closure (j2Gs '' {l | l < 4}) =
        j2P ⊓ centralizer ({tp 315 (j2CentTbl 31)} : Set (Perm (Fin 315))) ∧
      Nat.card (closure (j2Gs '' {l | l < 4})) = Nat.card (closure (j2Rs '' {l | l < 4})) := by
  obtain ⟨-, -, -, -, -, -, -, -, hrows, -⟩ :=
    centData_spec j2_groupData card_j2P j2_primes j2_sylowOrder j2_centDataOK
  obtain ⟨-, -, h3, h4, h5, -⟩ :=
    hrows _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  dsimp only at h3 h4 h5
  have ht0 : tp 315 (j2CentTbl 31) ∈ j2P := by
    by_contra h
    exact Bool.false_ne_true (h3.2 h)
  have hcg : closure (j2Gs '' {l | l < 4}) =
      j2P ⊓ centralizer ({tp 315 (j2CentTbl 31)} : Set (Perm (Fin 315))) := by
    rw [← j2_gens_eq]
    exact h4
  refine ⟨ht0, hcg, ?_⟩
  rw [← j2Og_eq, j2Om_card, hcg, h5]

theorem j2_eLabelling_t0 :
    ∃ ht : tp 315 (j2CentTbl 31) ∈ j2P, ∃ elt : ℕ → ↥j2P,
      ELabelling (rootGroup ↥j2P ⟨_, ht⟩) ⟨_, ht⟩ mulE0 eT elt := by
  obtain ⟨ht0, hcg, hcard⟩ := j2_data
  obtain ⟨Ω, hΩ, hc5⟩ := j2_omega
  have hc : ∀ l < 4, ∀ j, j2Gs l (Ω j) = Ω (j2Rs l j) := fun l hl => hc5 l (by omega)
  have htO : ∀ j, tp 315 (j2CentTbl 31) (Ω j) = Ω (j2Rs 4 j) := hc5 4 (by norm_num)
  refine ⟨ht0, eLabelling_of_restrict ht0 hΩ hc hcg hcard htO fun hO => ?_⟩
  have hcgY := closure_eq_inf_centralizer ht0 hΩ hc hcg hcard htO
  exact j2Om_recs.eLabelling (X := closure (j2Rs '' {l | l < 4})) hO
    (by rw [j2Og_eq]; exact hcgY) j2Om_facts.2.2.2.2.2.2.1 (tbl_of j2Om_tbl)
    j2Om_facts.2.2.2.2.2.2.2.1 (by decide) j2Om_facts.2.2.2.2.2.2.2.2

theorem j2_rootFactsFor_t0 :
    ∃ ht : tp 315 (j2CentTbl 31) ∈ j2P, RootFactsFor ↥j2P ⟨_, ht⟩ := by
  obtain ⟨ht0, hcg, hcard⟩ := j2_data
  obtain ⟨Ω, hΩ, hc5⟩ := j2_omega
  have hc : ∀ l < 4, ∀ j, j2Gs l (Ω j) = Ω (j2Rs l j) := fun l hl => hc5 l (by omega)
  have htO : ∀ j, tp 315 (j2CentTbl 31) (Ω j) = Ω (j2Rs 4 j) := hc5 4 (by norm_num)
  refine ⟨ht0, rootFactsFor_of_restrict ht0 hΩ hc hcg hcard htO fun hO => ?_⟩
  have hcgY := closure_eq_inf_centralizer ht0 hΩ hc hcg hcard htO
  exact rootFactsFor_of_wCheck (X := closure (j2Rs '' {l | l < 4})) (by norm_num) hO
    (by rw [j2Og_eq]; exact hcgY) j2Om_wCheck

theorem j2_autEFact_t0 :
    ∃ ht : tp 315 (j2CentTbl 31) ∈ j2P, AutEFact ↥(rootGroup ↥j2P ⟨_, ht⟩) := by
  obtain ⟨ht, _, hL⟩ := j2_eLabelling_t0
  exact ⟨ht, autEFact_of_labelling_mulE0 hL⟩

@[expose] def j3OmI (l : ℕ) : ℕ := if l < 5 then 10 + l else 9

@[expose] noncomputable def j3Gs (l : ℕ) : Perm (Fin 6156) := tp 6156 (j3CentTbl (j3OmI l))

@[expose] noncomputable def j3Rs (l : ℕ) : Perm (Fin 80) := tp 80 (tabN 80 7 (J3OmT l))

theorem j3OmI_lt {l : ℕ} (hl : l < 6) : j3OmI l < 31 := by
  unfold j3OmI
  split <;> omega

theorem j3OmG_eq {l : ℕ} (hl : l < 6) : j3OmG l = J3CentP (j3OmI l) := by
  unfold j3OmG
  congr 1
  interval_cases l <;> rfl

theorem j3Gs_lt {l : ℕ} (hl : l < 5) : j3Gs l = tp 6156 (j3CentTbl (10 + l)) := by
  rw [j3Gs, j3OmI, if_pos hl]

theorem j3_permOK {k : ℕ} (hk : k < 31) : permOK 6156 (j3CentTbl k) = true :=
  List.all_eq_true.1 j3_permOK_all k (List.mem_range.2 hk)

theorem j3Om_permR {l : ℕ} (hl : l < 6) : permOK 80 (tabN 80 7 (J3OmT l)) = true := by
  rcases Nat.lt_or_ge l 5 with h | h
  · have h1 := j3Om_perm.2.1
    rw [Array.all_eq_true'] at h1
    exact h1 _ (List.mem_toArray.2 (List.mem_map.2
      ⟨J3OmT l, List.mem_map.2 ⟨l, List.mem_range.2 h, rfl⟩, rfl⟩))
  · obtain rfl : l = 5 := by omega
    exact j3Om_perm.1

theorem j3_gens_eq : tp 6156 '' {x | x ∈ J3.wGensJ3} = j3Gs '' {l | l < 5} := by
  ext σ
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x ∈ [j3CentTbl 10, j3CentTbl 11, j3CentTbl 12, j3CentTbl 13, j3CentTbl 14] :=
      List.mem_toArray.1 hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
    rcases hx' with h | h | h | h | h
    · exact ⟨0, by norm_num, by simp only [j3Gs_lt (l := 0) (by norm_num), h, Nat.reduceAdd]⟩
    · exact ⟨1, by norm_num, by simp only [j3Gs_lt (l := 1) (by norm_num), h, Nat.reduceAdd]⟩
    · exact ⟨2, by norm_num, by simp only [j3Gs_lt (l := 2) (by norm_num), h, Nat.reduceAdd]⟩
    · exact ⟨3, by norm_num, by simp only [j3Gs_lt (l := 3) (by norm_num), h, Nat.reduceAdd]⟩
    · exact ⟨4, by norm_num, by simp only [j3Gs_lt (l := 4) (by norm_num), h, Nat.reduceAdd]⟩
  · rintro ⟨l, hl, rfl⟩
    have hl' : l < 5 := hl
    refine ⟨j3CentTbl (10 + l), List.mem_toArray.2 ?_, (j3Gs_lt hl').symm⟩
    interval_cases l <;> simp only [Nat.reduceAdd]
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self))
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self)))

theorem j3Og_eq : tp 80 '' {x | x ∈ j3Og} = j3Rs '' {l | l < 5} := by
  ext σ
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 (List.mem_toArray.1 hx)
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hy
    exact ⟨l, List.mem_range.1 hl, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨_, List.mem_toArray.2 (List.mem_map.2
      ⟨J3OmT l, List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩, rfl⟩), rfl⟩

theorem j3Om_hg : ∀ l < 6, ∀ i : Fin 6156,
    ((j3Gs l i : Fin 6156) : ℕ) = pg 13 (mask 13) (j3OmG l) i := by
  intro l hl i
  have h1 := tp_unpack (n := 6156) (w := 13) (F := J3CentP (j3OmI l))
    (j3_permOK (j3OmI_lt hl)) (j3CentTbl_eq (j3OmI_lt hl)) i
  rw [j3OmG_eq hl, j3Gs]
  exact h1

theorem j3Gs_five : j3Gs 5 = tp 6156 (j3CentTbl 9) := by
  rw [j3Gs, j3OmI, if_neg (by norm_num)]

theorem j3_omega : ∃ Ω : Fin 80 → Fin 6156, Function.Injective Ω ∧
    ∀ l < 6, ∀ j, j3Gs l (Ω j) = Ω (j3Rs l j) :=
  restrData_of_checks (w := 13) (m := mask 13) (PT := J3OmP 0) (pw := 13) (pm := mask 13)
    (rw := 7) (rm := mask 7) (P := j3OmG) (R := J3OmT) j3Om_pts
    (fun l hl => allN_spec j3Om_restr l hl)
    j3Om_hg (fun l hl j => tp_tabN (by norm_num) (j3Om_permR hl) j)

theorem j3Om_card : Nat.card (closure (tp 80 '' {x | x ∈ j3Og})) = 1920 := by
  obtain ⟨hs, hsize⟩ := enumOK_spec (by norm_num) j3Om_recs.enumW
  rw [hs.card, hsize]

theorem j3_data :
    ∃ ht : tp 6156 (j3CentTbl 9) ∈ j3P,
      closure (j3Gs '' {l | l < 5}) =
        j3P ⊓ centralizer ({tp 6156 (j3CentTbl 9)} : Set (Perm (Fin 6156))) ∧
      Nat.card (closure (j3Gs '' {l | l < 5})) = Nat.card (closure (j3Rs '' {l | l < 5})) := by
  obtain ⟨-, -, -, -, -, -, -, -, hrows, -⟩ := j3_centData
  obtain ⟨-, -, h3, h4, h5, -⟩ := hrows _ List.mem_cons_self
  dsimp only at h3 h4 h5
  have ht0 : tp 6156 (j3CentTbl 9) ∈ j3P := by
    by_contra h
    exact Bool.false_ne_true (h3.2 h)
  have hcg : closure (j3Gs '' {l | l < 5}) =
      j3P ⊓ centralizer ({tp 6156 (j3CentTbl 9)} : Set (Perm (Fin 6156))) := by
    rw [← j3_gens_eq]
    exact h4
  refine ⟨ht0, hcg, ?_⟩
  rw [← j3Og_eq, j3Om_card, hcg, h5]

theorem j3_eLabelling_t0 :
    ∃ ht : tp 6156 (j3CentTbl 9) ∈ j3P, ∃ elt : ℕ → ↥j3P,
      ELabelling (rootGroup ↥j3P ⟨_, ht⟩) ⟨_, ht⟩ mulEJ3 21 elt := by
  obtain ⟨ht0, hcg, hcard⟩ := j3_data
  obtain ⟨Ω, hΩ, hc6⟩ := j3_omega
  have hc : ∀ l < 5, ∀ j, j3Gs l (Ω j) = Ω (j3Rs l j) := fun l hl => hc6 l (by omega)
  have htO : ∀ j, tp 6156 (j3CentTbl 9) (Ω j) = Ω (j3Rs 5 j) := by
    rw [← j3Gs_five]
    exact hc6 5 (by norm_num)
  refine ⟨ht0, eLabelling_of_restrict ht0 hΩ hc hcg hcard htO fun hO => ?_⟩
  have hcgY := closure_eq_inf_centralizer ht0 hΩ hc hcg hcard htO
  exact j3Om_recs.eLabelling (X := closure (j3Rs '' {l | l < 5})) hO
    (by rw [j3Og_eq]; exact hcgY) j3Om_facts.2.2.2.2.2.2.1 (tbl_of j3Om_tbl)
    j3Om_facts.2.2.2.2.2.2.2.1 (by decide) j3Om_facts.2.2.2.2.2.2.2.2

theorem j3_rootFactsFor_t0 :
    ∃ ht : tp 6156 (j3CentTbl 9) ∈ j3P, RootFactsFor ↥j3P ⟨_, ht⟩ := by
  obtain ⟨ht0, hcg, hcard⟩ := j3_data
  obtain ⟨Ω, hΩ, hc6⟩ := j3_omega
  have hc : ∀ l < 5, ∀ j, j3Gs l (Ω j) = Ω (j3Rs l j) := fun l hl => hc6 l (by omega)
  have htO : ∀ j, tp 6156 (j3CentTbl 9) (Ω j) = Ω (j3Rs 5 j) := by
    rw [← j3Gs_five]
    exact hc6 5 (by norm_num)
  refine ⟨ht0, rootFactsFor_of_restrict ht0 hΩ hc hcg hcard htO fun hO => ?_⟩
  have hcgY := closure_eq_inf_centralizer ht0 hΩ hc hcg hcard htO
  exact rootFactsFor_of_wCheck (X := closure (j3Rs '' {l | l < 5})) (by norm_num) hO
    (by rw [j3Og_eq]; exact hcgY) j3Om_wCheck

theorem j3_autEFact_t0 :
    ∃ ht : tp 6156 (j3CentTbl 9) ∈ j3P, AutEFact ↥(rootGroup ↥j3P ⟨_, ht⟩) := by
  obtain ⟨ht, _, hL⟩ := j3_eLabelling_t0
  exact ⟨ht, autEFact_of_labelling_mulEJ3 hL⟩

end CertificateChecks.KernelC24608

end
