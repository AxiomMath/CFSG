module

public import CFSG.Sporadic.SuzOddCore.CTIDefs
public import CFSG.Sporadic.SuzOddCore.CTIChain
public import CFSG.Sporadic.SuzOddCore.ThreeLocalA
public import Certificates.Kernel.Sporadic.OddCore.SuzCTF1

public noncomputable section

namespace CertificateChecks.KernelSpor.SuzCT

open CFSG CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native
  CFSG.ComponentClassification.PSL3Four CFSG.Sporadic.SuzOddCore


section Entry0

variable (h0 : (fixList 0).length = 42)

theorem d_hA : ∀ a ∈ {g | ∃ j < 5, dpermOf h0 j = g}, ∃ j < dGens.size, TabRep dGens[j]! a := by
  rintro _ ⟨j, hj, rfl⟩
  exact ⟨j, by rw [dGens_size]; exact hj, tabRep_dpermOf h0 hj⟩

theorem d_hgens : ∀ j < dGens.size, ∃ a ∈ {g | ∃ j < 5, dpermOf h0 j = g}, TabRep dGens[j]! a := by
  intro j hj
  rw [dGens_size] at hj
  exact ⟨_, ⟨j, hj, rfl⟩, tabRep_dpermOf h0 hj⟩

theorem rho0_enumerates :
    Enumerates (rho0Of h0).range (enumOf 42 (kGens 0) 40320).tabs.toList :=
  cRho_enumerates (by norm_num) h0 facts0.2.1.1

theorem suzD_enumerates : Enumerates (suzDOf h0) (enumOf 42 dGens 20160).tabs.toList :=
  enumerates_closure (d_hA h0) (d_hgens h0) facts0.2.2.1.1

theorem conj_mem_suzD {k : ℕ} (hk : k < 22) {x : Equiv.Perm (Fin 42)} (hx : x ∈ suzDOf h0) :
    kpermOf h0 k * x * (kpermOf h0 k)⁻¹ ∈ suzDOf h0 ∧
      (kpermOf h0 k)⁻¹ * x * kpermOf h0 k ∈ suzDOf h0 := by
  have hgen : ∀ j < 5, kpermOf h0 k * dpermOf h0 j * (kpermOf h0 k)⁻¹ ∈ suzDOf h0 ∧
      (kpermOf h0 k)⁻¹ * dpermOf h0 j * kpermOf h0 k ∈ suzDOf h0 := fun j hj =>
    conj_mem_of_normalOK (suzD_enumerates h0) facts0.2.2.1.2.2
      (by rw [facts0.1.2.1]; exact hk) (by rw [dGens_size]; exact hj) (tabRep_kpermOf h0 hk)
      (tabRep_dpermOf h0 hj)
  induction hx using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨j, hj, rfl⟩ := hg
    exact hgen j hj
  | one => simp
  | mul g h _ _ hg hh =>
    constructor
    · have : kpermOf h0 k * (g * h) * (kpermOf h0 k)⁻¹ =
          (kpermOf h0 k * g * (kpermOf h0 k)⁻¹) * (kpermOf h0 k * h * (kpermOf h0 k)⁻¹) := by
        group
      rw [this]
      exact (suzDOf h0).mul_mem hg.1 hh.1
    · have : (kpermOf h0 k)⁻¹ * (g * h) * kpermOf h0 k =
          ((kpermOf h0 k)⁻¹ * g * kpermOf h0 k) * ((kpermOf h0 k)⁻¹ * h * kpermOf h0 k) := by
        group
      rw [this]
      exact (suzDOf h0).mul_mem hg.2 hh.2
  | inv g _ hg =>
    constructor
    · have : kpermOf h0 k * g⁻¹ * (kpermOf h0 k)⁻¹ = (kpermOf h0 k * g * (kpermOf h0 k)⁻¹)⁻¹ := by
        group
      rw [this]
      exact (suzDOf h0).inv_mem hg.1
    · have : (kpermOf h0 k)⁻¹ * g⁻¹ * kpermOf h0 k = ((kpermOf h0 k)⁻¹ * g * kpermOf h0 k)⁻¹ := by
        group
      rw [this]
      exact (suzDOf h0).inv_mem hg.2

theorem class_orbit {l : ℕ} (hl : l < 10) :
    (∀ t ∈ classOrbits[l]!.tabs.toList, ∃ c ∈ suzDOf h0, TabRep t (c * repPermOf h0 l * c⁻¹)) ∧
      (∀ c ∈ suzDOf h0, ∃ t ∈ classOrbits[l]!.tabs.toList, TabRep t (c * repPermOf h0 l * c⁻¹)) ∧
      classOrbits[l]!.tabs.toList.Nodup :=
  conj_orbit (d_hA h0) (d_hgens h0) (tabRep_repPermOf h0 l) (facts0.2.2.2.1.1 l hl).1

theorem classFun_injective : Function.Injective (classFunOf h0) := by
  intro l l' h
  rw [classFunOf, classFunOf, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff] at h
  obtain ⟨c, hc⟩ := h
  by_contra hne
  have hne' : (l : ℕ) ≠ l' := fun h => hne (Fin.ext h)
  have hcl := congrArg Subtype.val hc
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hcl
  obtain ⟨t, ht, hrep⟩ := (class_orbit h0 l.2).2.1 c c.2
  rw [hcl] at hrep
  exact notInOK_spec (facts0.2.2.2.1.2 l l.2 l' l'.2 hne') (tabRep_repPermOf h0 l') t ht hrep

theorem classFun_surjective : Function.Surjective (classFunOf h0) := by
  intro C
  obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective C
  obtain ⟨t, ht, hrep⟩ := (suzD_enumerates h0).complete x x.2
  obtain ⟨k, hk, rfl⟩ := exists_getElem!_of_mem ht
  obtain ⟨l, hl, hf⟩ := facts0.2.2.2.2 k hk
  obtain ⟨c, hc, hrep'⟩ := (class_orbit h0 hl).1 _ (mem_of_found hf)
  refine ⟨⟨l, hl⟩, ?_⟩
  rw [classFunOf, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
  refine ⟨⟨c, hc⟩, Subtype.ext ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact (hrep'.perm_eq hrep)

theorem card_class (l : Fin 10) : Nat.card (classFunOf h0 l).carrier = classSizes.getD l 0 := by
  have hset : (Subtype.val '' (classFunOf h0 l).carrier : Set (Equiv.Perm (Fin 42))) =
      {y | ∃ c ∈ suzDOf h0, c * repPermOf h0 l * c⁻¹ = y} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [ConjClasses.mem_carrier_iff_mk_eq, classFunOf, ConjClasses.mk_eq_mk_iff_isConj,
        isConj_iff] at hx
      obtain ⟨c, hc⟩ := hx
      refine ⟨(c : Equiv.Perm (Fin 42))⁻¹, (suzDOf h0).inv_mem c.2, ?_⟩
      have := congrArg Subtype.val hc
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
      rw [← this]
      group
    · rintro ⟨c, hc, rfl⟩
      refine ⟨⟨c * repPermOf h0 l * c⁻¹, (suzDOf h0).mul_mem ((suzDOf h0).mul_mem hc
        (repPermOf_mem h0 l)) ((suzDOf h0).inv_mem hc)⟩, ?_, rfl⟩
      rw [ConjClasses.mem_carrier_iff_mk_eq, classFunOf, ConjClasses.mk_eq_mk_iff_isConj,
        isConj_iff]
      refine ⟨⟨c, hc⟩⁻¹, Subtype.ext ?_⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      group
  rw [← Nat.card_image_of_injective Subtype.val_injective, hset]
  obtain ⟨hs, hc, hn⟩ := class_orbit h0 l.2
  rw [card_set_of_tabs (L := classOrbits[(l : ℕ)]!.tabs.toList) (fun t ht => by
    obtain ⟨c, hc', hr⟩ := hs t ht
    exact ⟨_, ⟨c, hc', rfl⟩, hr⟩) (by rintro _ ⟨c, hc', rfl⟩; exact hc c hc') hn,
    Array.length_toList, (facts0.2.2.2.1.1 l l.2).2]

theorem entry0 :
    Enumerates (rho0Of h0).range (enumOf 42 (kGens 0) 40320).tabs.toList ∧
      Nat.card (rho0Of h0).range = 40320 ∧
      Nat.card (suzDOf h0) = 20160 ∧
      (∀ k < 22, ∀ x ∈ suzDOf h0, kpermOf h0 k * x * (kpermOf h0 k)⁻¹ ∈ suzDOf h0 ∧
        (kpermOf h0 k)⁻¹ * x * kpermOf h0 k ∈ suzDOf h0) ∧
      Function.Injective (classFunOf h0) ∧ Function.Surjective (classFunOf h0) ∧
      ∀ l, Nat.card (classFunOf h0 l).carrier = classSizes.getD l 0 := by
  refine ⟨rho0_enumerates h0, ?_, ?_, fun k hk x hx => conj_mem_suzD h0 hk hx,
    classFun_injective h0, classFun_surjective h0, card_class h0⟩
  · rw [(rho0_enumerates h0).card, Array.length_toList, facts0.2.1.2]
  · rw [(suzD_enumerates h0).card, Array.length_toList, facts0.2.2.1.2.1]

end Entry0

section Entry1

variable (h1 : (fixList 1).length = 54)

theorem range_rho1_eq : (rho1Of h1).range = Subgroup.closure {g | ∃ k < 10, kperm1Of h1 k = g} := by
  rw [rho1Of, range_cRho]
  apply congrArg Subgroup.closure
  ext g
  simp only [kGenSet, Set.mem_ofPred_eq, kperm1Of, rho1Of, invInnerGenArrs_size1]

theorem k1Base_eq : k1Base = (([0, 1, 2, 3, 4, 6] : List (Fin 54)).map Fin.val).toArray := rfl

theorem card_range_rho1 : Nat.card (rho1Of h1).range = 1658880 := by
  have h := facts1.2.2.1
  have hsz : (kGens 1).size = 10 := facts1.1.2.1
  have hc := card_closure_of_rawChainOK_tabRep (n := 54) (by norm_num) (O := kGens 1)
    (S := k1Strong) (base := [0, 1, 2, 3, 4, 6]) (by decide)
    (by rw [k1Strong, pushStrong_size]; omega) (fun i hi => pushStrong_get 54 _ _ hi)
    (by rw [hsz, ← k1Base_eq]; exact h.1) (f := kperm1Of h1)
    (fun k hk => tabRep_kperm1Of h1 (by rw [hsz] at hk; exact hk))
  rw [← k1Base_eq, h.2, hsz] at hc
  rw [range_rho1_eq, hc]

theorem qbar_enumerates : Enumerates (suzQbarOf h1) (enumOf 54 qGens 64).tabs.toList := by
  refine enumerates_closure ?_ ?_ facts1.2.1.1
  · rintro _ ⟨j, hj, rfl⟩
    exact ⟨j, by rw [qGens_size]; exact hj, tabRep_qpermOf h1 hj⟩
  · intro j hj
    rw [qGens_size] at hj
    exact ⟨_, ⟨j, hj, rfl⟩, tabRep_qpermOf h1 hj⟩

theorem card_qbar : Nat.card (suzQbarOf h1) = 64 := by
  rw [(qbar_enumerates h1).card, Array.length_toList, facts1.2.1.2.1]

theorem kperm1_mem (k : ℕ) : kperm1Of h1 k ∈ (rho1Of h1).range := ⟨_, rfl⟩

theorem qbar_le : suzQbarOf h1 ≤ (rho1Of h1).range := by
  rw [suzQbarOf, Subgroup.closure_le]
  rintro _ ⟨j, -, rfl⟩
  exact (rho1Of h1).range.list_prod_mem fun x hx => by
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
    exact kperm1_mem h1 k

theorem conj_mem_qbar {k : ℕ} (hk : k < 10) {x : Equiv.Perm (Fin 54)} (hx : x ∈ suzQbarOf h1) :
    kperm1Of h1 k * x * (kperm1Of h1 k)⁻¹ ∈ suzQbarOf h1 := by
  induction hx using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨j, hj, rfl⟩ := hg
    exact (conj_mem_of_normalOK (qbar_enumerates h1) facts1.2.1.2.2
      (by rw [facts1.1.2.1]; exact hk) (by rw [qGens_size]; exact hj) (tabRep_kperm1Of h1 hk)
      (tabRep_qpermOf h1 hj)).1
  | one => simp
  | mul g h _ _ hg hh =>
    have : kperm1Of h1 k * (g * h) * (kperm1Of h1 k)⁻¹ =
        (kperm1Of h1 k * g * (kperm1Of h1 k)⁻¹) * (kperm1Of h1 k * h * (kperm1Of h1 k)⁻¹) := by
      group
    rw [this]
    exact (suzQbarOf h1).mul_mem hg hh
  | inv g _ hg =>
    have : kperm1Of h1 k * g⁻¹ * (kperm1Of h1 k)⁻¹ = (kperm1Of h1 k * g * (kperm1Of h1 k)⁻¹)⁻¹ := by
      group
    rw [this]
    exact (suzQbarOf h1).inv_mem hg

theorem range_le_normalizer : (rho1Of h1).range ≤ Subgroup.normalizer (suzQbarOf h1 : Set _) := by
  rw [range_rho1_eq, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact mem_normalizer_of_conj_mem fun x hx => conj_mem_qbar h1 hk hx

theorem actBase_eq : actBase = (([2, 1, 3, 4, 5] : List (Fin 64)).map Fin.val).toArray := rfl

theorem actGens_size : actGens.size = 10 := by simp [actGens]

theorem actGens_get {k p : ℕ} (hk : k < 10) (hp : p < 64) :
    (actGens[k]!)[p]! =
      qTabs.toList.idxOf (conjTab 54 (kGens 1)[k]! (kInvs 1)[k]! qTabs[p]!) := by
  rw [getElem!_pos actGens k (by rw [actGens_size]; exact hk)]
  simp only [actGens, Array.getElem_ofFn]
  rw [getElem!_pos _ p (by simpa using hp), Array.getElem_ofFn]

theorem tabRep_act {k : ℕ} (hk : k < 10) :
    TabRep actGens[k]! (permOfArr 64 actGens[k]!) := by
  have hF := chainCheckFacts facts1.2.2.2.1.1
  have hs : k < actStrong.size := by
    rw [actStrong, pushStrong_size, actGens_size]
    exact Nat.lt_add_right _ hk
  have hr := (rep_permOfArr (hF.strong_inv k hs)).1
  rw [actStrong, pushStrong_get 64 _ _ (by rw [actGens_size]; exact hk)] at hr
  refine ⟨?_, fun x => hr x⟩
  rw [getElem!_pos actGens k (by rw [actGens_size]; exact hk)]
  simp [actGens]

theorem card_act :
    Nat.card (Subgroup.closure {s | ∃ j < 10, permOfArr 64 actGens[j]! = s}) = 25920 := by
  have h := facts1.2.2.2.1
  have hc := card_closure_of_rawChainOK_tabRep (n := 64) (by norm_num) (O := actGens)
    (S := actStrong) (base := [2, 1, 3, 4, 5]) (by decide)
    (by rw [actStrong, pushStrong_size]; omega) (fun i hi => pushStrong_get 64 _ _ hi)
    (by rw [actGens_size, ← actBase_eq]; exact h.1) (f := fun j => permOfArr 64 actGens[j]!)
    (fun k hk => tabRep_act (by rw [actGens_size] at hk; exact hk))
  rw [← actBase_eq, h.2, actGens_size] at hc
  exact hc

theorem tabRep_actGens {j p : ℕ} (hj : j < 10) (hp : p < 64) {x : Equiv.Perm (Fin 54)}
    (hx : TabRep qTabs[p]! x) :
    TabRep qTabs[((permOfArr 64 actGens[j]! ⟨p, hp⟩ : Fin 64) : ℕ)]!
      (kperm1Of h1 j * x * (kperm1Of h1 j)⁻¹) := by
  rw [← (tabRep_act hj).apply ⟨p, hp⟩, actGens_get hj hp]
  have hlt := facts1.2.2.2.2.1 j hj p hp
  rw [actGens_get hj hp] at hlt
  have hlt' : qTabs.toList.idxOf (conjTab 54 (kGens 1)[j]! (kInvs 1)[j]! qTabs[p]!) <
      qTabs.toList.length := by
    have hq : qTabs.size = 64 := facts1.2.1.2.1
    rw [Array.length_toList, hq]
    exact hlt
  rw [getElem!_pos qTabs _ (by rw [← Array.length_toList]; exact hlt'), ← Array.getElem_toList,
    List.getElem_idxOf hlt']
  exact (tabRep_kperm1Of h1 hj).conjTab hx (tabRep_kperm1Of_inv h1 hj)

theorem qperm_comm {i j : ℕ} (hi : i < 6) (hj : j < 6) :
    qpermOf h1 i * qpermOf h1 j = qpermOf h1 j * qpermOf h1 i := by
  have e := (tabRep_qpermOf h1 hi).comp (tabRep_qpermOf h1 hj)
  rw [facts1.2.2.2.2.2 i hi j hj] at e
  exact e.perm_eq ((tabRep_qpermOf h1 hj).comp (tabRep_qpermOf h1 hi))

theorem qbar_le_centralizer :
    suzQbarOf h1 ≤ Subgroup.centralizer (suzQbarOf h1 : Set (Equiv.Perm (Fin 54))) := by
  rw [suzQbarOf, Subgroup.centralizer_closure, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  rintro _ ⟨j, hj, rfl⟩
  exact qperm_comm h1 hj hi

theorem centralizer_qbar {y : Equiv.Perm (Fin 54)} (hy : y ∈ (rho1Of h1).range)
    (hc : ∀ j < 6, y * qpermOf h1 j = qpermOf h1 j * y) : y ∈ suzQbarOf h1 := by
  have hle := card_mul_card_centralizer_le (H := (rho1Of h1).range) (Q := suzQbarOf h1)
    (E := qTabs) (m := 64) (qbar_enumerates h1) facts1.2.1.2.1 (range_le_normalizer h1)
    (k := 10) (kperm1Of h1) (fun j _ => kperm1_mem h1 j) (fun j => permOfArr 64 actGens[j]!)
    fun j hj p x hx => tabRep_actGens h1 hj p.2 hx
  rw [card_act, card_range_rho1] at hle
  have hC : Nat.card ((Subgroup.centralizer (suzQbarOf h1 : Set (Equiv.Perm (Fin 54)))).subgroupOf
      (rho1Of h1).range) ≤ 64 := by omega
  have hQle : (suzQbarOf h1).subgroupOf (rho1Of h1).range ≤
      (Subgroup.centralizer (suzQbarOf h1 : Set (Equiv.Perm (Fin 54)))).subgroupOf
        (rho1Of h1).range :=
    fun x hx => qbar_le_centralizer h1 hx
  have hQcard : Nat.card ((suzQbarOf h1).subgroupOf (rho1Of h1).range) = 64 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (qbar_le h1)).toEquiv, card_qbar]
  have heq := Subgroup.eq_of_le_of_card_ge hQle (by rw [hQcard]; exact hC)
  have hyC : y ∈ Subgroup.centralizer (suzQbarOf h1 : Set (Equiv.Perm (Fin 54))) := by
    rw [suzQbarOf, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    rintro _ ⟨j, hj, rfl⟩
    exact (hc j hj).symm
  have hm : (⟨y, hy⟩ : (rho1Of h1).range) ∈
      (Subgroup.centralizer (suzQbarOf h1 : Set (Equiv.Perm (Fin 54)))).subgroupOf
        (rho1Of h1).range := hyC
  rw [← heq] at hm
  exact hm

theorem entry1 :
    Nat.card (rho1Of h1).range = 1658880 ∧
      Nat.card (suzQbarOf h1) = 64 ∧
      (∀ k < 10, ∀ x ∈ suzQbarOf h1, kperm1Of h1 k * x * (kperm1Of h1 k)⁻¹ ∈ suzQbarOf h1) ∧
      (∀ i < 6, ∀ j < 6, qpermOf h1 i * qpermOf h1 j = qpermOf h1 j * qpermOf h1 i) ∧
      ∀ y ∈ (rho1Of h1).range, (∀ j < 6, y * qpermOf h1 j = qpermOf h1 j * y) →
        y ∈ suzQbarOf h1 :=
  ⟨card_range_rho1 h1, card_qbar h1, fun k hk x hx => conj_mem_qbar h1 hk hx,
    fun i hi j hj => qperm_comm h1 hi hj, fun y hy hc => centralizer_qbar h1 hy hc⟩

end Entry1

end CertificateChecks.KernelSpor.SuzCT
