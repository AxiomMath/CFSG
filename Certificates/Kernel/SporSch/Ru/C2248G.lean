module

public import CFSG.Sporadic.Schreier.RuChainSpec
public import CFSG.Sporadic.Schreier.RuCheckCentersInputs
meta import Lean.Meta.Tactic.NormCast

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSporSch.RuCG

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.RuSchreier

@[expose] noncomputable def X (i : Nat) : Equiv.Perm (Fin 1920) := permOfArr 1920 (ruEF i)

theorem orig_mem {S : Array (Array Nat)} {k : Nat} {hk : k ≤ S.size}
    {base : List (Fin 1920)} {hb : base.Nodup} {W : Array (List Int)} {j : Nat} (hj : j < k) :
    permOfArr 1920 S[j]! ∈
      (RawSchreierDatum.ofArrays 1920 (by norm_num) S k hk base hb W).originalSubgroup := by
  refine Subgroup.subset_closure ?_
  change permOfArr 1920 S[j]! ∈ (RawSchreierDatum.ofArrays 1920 _ S k hk base hb W).original.toList
  rw [ofArrays_original_toList]
  exact List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩

theorem comm_of {t u : Array Nat} {g h : Equiv.Perm (Fin 1920)} (ht : Rep 1920 t g)
    (hu : Rep 1920 u h) (hc : ruComm1920 t u = true) : g * h = h * g :=
  (eqA_iff (rep_compA ht hu) (rep_compA hu ht)).1 hc

theorem sizeF (f : Nat) : (ruField1920 f).size = (ruLines1920.getD f (0, 0)).2 := by
  rw [ruField1920, Array.size_ofFn]

variable
  (hF : ruChainOK 1920 (ruField1920 0) 2 7 ruCFaithfulBase ruCFaithfulDerivations = true)
  (hK : ruChainOK 1920 (ruField1920 2) 8 10 ruKBase ruKDerivations = true)
  (hcF : rawOrbitSizes 1920 (ruField1920 0) (ruBaseArr 1920 ruCFaithfulBase) = [1920, 128])
  (hcK : rawOrbitSizes 1920 (ruField1920 2) (ruBaseArr 1920 ruKBase) = [512, 4])
  (hKH : ∀ j < 10, ruSift 1920 (ruField1920 0) ruCFaithfulBase (ruField1920 2)[j]! = true)
  (hKX : ∀ j < 10, ∀ i < 7, ruComm1920 (ruField1920 2)[j]! (ruEF i) = true)
  (hX : ∀ i < 7, isInvA 1920 (ruEF i) (invCand 1920 (ruEF i)) = true)
  (tup : Nat → Nat → Array Nat) (par gen : Nat → Nat)
  (h0 : ∀ i < 7, tup 0 i = ruEF i)
  (hs : ∀ k, 1 ≤ k → k < 120 → par k < k ∧ gen k < 2 ∧ ∀ i < 7, tup k i =
    compA 1920 (compA 1920 (ruField1920 0)[gen k]! (tup (par k) i))
      (invCand 1920 (ruField1920 0)[gen k]!))
  (hd : ∀ k < 120, ∀ l < 120, (∀ i < 7, eqA 1920 (tup k i) (tup l i) = true) → k = l)

include hF hK hcF hcK hKH hKX hX h0 hs hd in
theorem cent_le_K {g : Equiv.Perm (Fin 1920)} (hg : g ∈ ruChainCFaithful.originalSubgroup)
    (hc : ∀ i < 7, g * X i = X i * g) : g ∈ ruChainK.originalSubgroup := by
  classical
  set H := ruChainCFaithful.originalSubgroup with hHdef
  set K := ruChainK.originalSubgroup with hKdef
  have rX : ∀ i < 7, Rep 1920 (ruEF i) (X i) := fun i hi => (rep_permOfArr (hX i hi)).1
  have hS0 : (ruField1920 0).size = 7 := by rw [sizeF]; rfl
  have hS2 : (ruField1920 2).size = 10 := by rw [sizeF]; rfl
  have rG : ∀ g < 2, Rep 1920 (ruField1920 0)[g]! (permOfArr 1920 (ruField1920 0)[g]!) ∧
      Rep 1920 (invCand 1920 (ruField1920 0)[g]!) (permOfArr 1920 (ruField1920 0)[g]!)⁻¹ :=
    fun g hg => rep_permOfArr (ruChain_strong_inv hF (by rw [hS0]; omega))
  have hG : ∀ g < 2, permOfArr 1920 (ruField1920 0)[g]! ∈ H := fun g hg => orig_mem hg
  have horb : ∀ k < 120, ∃ h ∈ H, ∀ i < 7, Rep 1920 (tup k i) (h * X i * h⁻¹) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · refine ⟨1, H.one_mem, fun i hi => ?_⟩
        rw [h0 i hi, one_mul, inv_one, mul_one]
        exact rX i hi
      · obtain ⟨hp, hgk, he⟩ := hs k hpos hk
        obtain ⟨h, hh, hr⟩ := ih (par k) hp (by omega)
        refine ⟨permOfArr 1920 (ruField1920 0)[gen k]! * h, H.mul_mem (hG _ hgk) hh,
          fun i hi => ?_⟩
        rw [he i hi]
        have e := rep_compA (rep_compA (rG _ hgk).1 (hr i hi)) (rG _ hgk).2
        have e2 : permOfArr 1920 (ruField1920 0)[gen k]! * (h * X i * h⁻¹) *
            (permOfArr 1920 (ruField1920 0)[gen k]!)⁻¹ =
            permOfArr 1920 (ruField1920 0)[gen k]! * h * X i *
              (permOfArr 1920 (ruField1920 0)[gen k]! * h)⁻¹ := by group
        rwa [e2] at e
  choose hf hfH hfr using horb
  let s : Set (Equiv.Perm (Fin 1920)) := {x | ∃ i < 7, X i = x}
  let C : Subgroup H := (Subgroup.centralizer s).subgroupOf H
  have hmemC : ∀ x : H, x ∈ C ↔ ∀ i < 7, X i * x = x * X i := fun x => by
    change (x : Equiv.Perm (Fin 1920)) ∈ Subgroup.centralizer s ↔ _
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · exact fun h i hi => h _ ⟨i, hi, rfl⟩
    · rintro h _ ⟨i, hi, rfl⟩
      exact h i hi
  have hidx : 120 ≤ Nat.card (H ⧸ C) := by
    let φ : Fin 120 → H ⧸ C := fun k => QuotientGroup.mk ⟨hf k k.2, hfH k k.2⟩
    have hinj : Function.Injective φ := by
      intro k l hkl
      have hq := QuotientGroup.eq.1 hkl
      rw [hmemC] at hq
      refine Fin.ext (hd k k.2 l l.2 fun i hi => ?_)
      rw [eqA_iff (hfr k k.2 i hi) (hfr l l.2 i hi)]
      have hcm := hq i hi
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hcm
      set a := hf k k.2
      set b := hf l l.2
      calc a * X i * a⁻¹ = a * (a⁻¹ * b * X i) * (a⁻¹ * b)⁻¹ * a⁻¹ := by
            rw [← hcm]
            group
        _ = b * X i * b⁻¹ := by group
    have := Nat.card_le_card_of_injective φ hinj
    simpa using this
  have hcardH : Nat.card H = 245760 := by
    have e : Nat.card ruChainCFaithful.originalSubgroup =
        (rawOrbitSizes 1920 (ruField1920 0) (ruBaseArr 1920 ruCFaithfulBase)).prod := ruChain_card hF
    rw [hHdef, e, hcF]
    rfl
  have hcardK : Nat.card K = 2048 := by
    have e : Nat.card ruChainK.originalSubgroup =
        (rawOrbitSizes 1920 (ruField1920 2) (ruBaseArr 1920 ruKBase)).prod := ruChain_card hK
    rw [hKdef, e, hcK]
    rfl
  have hKo : ruChainK.original.toList = (List.range 8).map fun i => permOfArr 1920 (ruField1920 2)[i]! :=
    ofArrays_original_toList
  have hCle : Nat.card C ≤ 2048 := by
    have e := Subgroup.card_mul_index C
    rw [hcardH, Subgroup.index] at e
    nlinarith
  have hKgen : ∀ j < 8, permOfArr 1920 (ruField1920 2)[j]! ∈ H ∧
      ∀ i < 7, X i * permOfArr 1920 (ruField1920 2)[j]! = permOfArr 1920 (ruField1920 2)[j]! * X i := by
    intro j hj
    have hj' : j < (ruField1920 2).size := by
      rw [hS2]
      omega
    have rj := (rep_permOfArr (ruChain_strong_inv (j := j) hK hj')).1
    have hsift : permOfArr 1920 (ruField1920 2)[j]! ∈ ruChainCFaithful.originalSubgroup :=
      (ruChain_sift hF rj).1 (hKH j (by omega))
    exact ⟨hsift,
      fun i hi => (comm_of rj (rX i hi) (hKX j (by omega) i hi)).symm⟩
  have hKH' : K ≤ H := by
    rw [hKdef, RawSchreierDatum.originalSubgroup, Subgroup.closure_le]
    intro y hy
    change y ∈ ruChainK.original.toList at hy
    rw [hKo] at hy
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
    exact (hKgen j (List.mem_range.1 hj)).1
  have hKC : K ≤ Subgroup.centralizer s := by
    rw [hKdef, RawSchreierDatum.originalSubgroup, Subgroup.closure_le]
    intro y hy
    change y ∈ ruChainK.original.toList at hy
    rw [hKo] at hy
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    rintro _ ⟨i, hi, rfl⟩
    exact (hKgen j (List.mem_range.1 hj)).2 i hi
  have hKC' : K.subgroupOf H ≤ C := fun x hx =>
    Subgroup.mem_subgroupOf.2 (hKC (Subgroup.mem_subgroupOf.1 hx))
  have hcardK' : Nat.card (K.subgroupOf H) = 2048 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH').toEquiv, hcardK]
  have heq : K.subgroupOf H = C :=
    Subgroup.eq_of_le_of_card_ge hKC' (by rw [hcardK']; exact hCle)
  have hgC : (⟨g, hg⟩ : H) ∈ C := (hmemC _).2 fun i hi => (hc i hi).symm
  rw [← heq] at hgC
  exact hgC

include hF hK hcF hcK hKH hKX hX h0 hs hd in
theorem ceAll2 : all2 1920 (rawLevels 1920 (ruField1920 0) (ruBaseArr 1920 ruCFaithfulBase))
    (fun g => !(allLt 7 fun i => ruComm1920 g (ruEF i)) ||
      siftA 1920 ruKLevels (ruBaseArr 1920 ruKBase) 0 g) = true := by
  have hA : ChainArrays ruChainCFaithful ((ruField1920 0).extract 0 2) (ruField1920 0)
      (ruBaseArr 1920 ruCFaithfulBase) (ruWordsArr 2 7 ruCFaithfulDerivations) := ruChain_arrays hF
  unfold all2
  rw [allLt_iff]
  intro a ha
  rw [allLt_iff]
  intro b hb
  dsimp only
  have h2 : 2 ≤ ruChainCFaithful.baseCount := by decide
  have rt := chain_rep_prod2A hA hF h2 ha hb
  have hmem := Subgroup.mul_mem _
    (chain_levT_mem_original hA (by norm_num) hF (Nat.lt_of_lt_of_le (by norm_num) h2) ha)
    (chain_levT_mem_original hA (by norm_num) hF (Nat.lt_of_lt_of_le (by norm_num) h2) hb)
  cases hall : allLt 7 fun i => ruComm1920
      (prod2A 1920 (rawLevels 1920 (ruField1920 0) (ruBaseArr 1920 ruCFaithfulBase)) a b) (ruEF i)
  · rfl
  · rw [Bool.not_true, Bool.false_or]
    have hc : ∀ i < 7, _ * X i = X i * _ := fun i hi =>
      comm_of rt (rep_permOfArr (hX i hi)).1 (allLt_iff.1 hall i hi)
    exact (ruChain_sift hK rt).2 (cent_le_K hF hK hcF hcK hKH hKX hX tup par gen h0 hs hd hmem hc)

@[expose] noncomputable def Y (j : Nat) : Equiv.Perm (Fin 1920) := permOfArr 1920 (ruJF j)

include hF hK hcF hcK hKH hKX hX h0 hs hd in
theorem cjAll2 (hJ : ruChainOK 1920 (ruField1920 3) 6 10 ruJBase ruJDerivations = true)
    (hXJ : ∀ i < 7, ruSift 1920 (ruField1920 3) ruJBase (ruEF i) = true)
    (hKJ : all2 1920 ruKLevels (fun g => !(allLt 6 fun j => ruComm1920 g (ruJF j)) ||
      siftA 1920 ruJLevels (ruBaseArr 1920 ruJBase) 0 g) = true) :
    all2 1920 (rawLevels 1920 (ruField1920 0) (ruBaseArr 1920 ruCFaithfulBase))
      (fun g => !(allLt 6 fun j => ruComm1920 g (ruJF j)) ||
        siftA 1920 ruJLevels (ruBaseArr 1920 ruJBase) 0 g) = true := by
  have hS3 : (ruField1920 3).size = 10 := by rw [sizeF]; rfl
  have rY : ∀ j < 6, Rep 1920 (ruJF j) (Y j) := fun j hj =>
    (rep_permOfArr (ruChain_strong_inv (j := j) hJ (by rw [hS3]; omega))).1
  have hJo : ruChainJ.original.toList = (List.range 6).map fun i => permOfArr 1920 (ruField1920 3)[i]! :=
    ofArrays_original_toList
  have hAK : ChainArrays ruChainK ((ruField1920 2).extract 0 8) (ruField1920 2)
      (ruBaseArr 1920 ruKBase) (ruWordsArr 8 10 ruKDerivations) := ruChain_arrays hK
  have hb2 : ruChainK.baseCount = 2 := by decide
  have PK := chain_forall_of_all2 hAK (by norm_num) hK (by omega)
    (fun i h2i hi => absurd hi (by omega))
    (P := fun g => (∀ j < 6, g * Y j = Y j * g) → g ∈ ruChainJ.originalSubgroup)
    (fun t g ht hpt hcomm => by
      have hall : (allLt 6 fun j => ruComm1920 t (ruJF j)) = true :=
        allLt_iff.2 fun j hj => (eqA_iff (rep_compA ht (rY j hj)) (rep_compA (rY j hj) ht)).2
          (hcomm j hj)
      rw [hall, Bool.not_true, Bool.false_or] at hpt
      exact (ruChain_sift hJ ht).1 hpt) hKJ
  have hA : ChainArrays ruChainCFaithful ((ruField1920 0).extract 0 2) (ruField1920 0)
      (ruBaseArr 1920 ruCFaithfulBase) (ruWordsArr 2 7 ruCFaithfulDerivations) := ruChain_arrays hF
  unfold all2
  rw [allLt_iff]
  intro a ha
  rw [allLt_iff]
  intro b hb
  dsimp only
  have h2 : 2 ≤ ruChainCFaithful.baseCount := by decide
  have rt := chain_rep_prod2A hA hF h2 ha hb
  have hmem := Subgroup.mul_mem _
    (chain_levT_mem_original hA (by norm_num) hF (Nat.lt_of_lt_of_le (by norm_num) h2) ha)
    (chain_levT_mem_original hA (by norm_num) hF (Nat.lt_of_lt_of_le (by norm_num) h2) hb)
  cases hall : allLt 6 fun j => ruComm1920
      (prod2A 1920 (rawLevels 1920 (ruField1920 0) (ruBaseArr 1920 ruCFaithfulBase)) a b) (ruJF j)
  · rfl
  · rw [Bool.not_true, Bool.false_or]
    have hcY : ∀ j < 6, _ * Y j = Y j * _ := fun j hj =>
      comm_of rt (rY j hj) (allLt_iff.1 hall j hj)
    have hJC : ruChainJ.originalSubgroup ≤ Subgroup.centralizer
        {ChainArrays.levT 1920 (ruField1920 0) (ruBaseArr 1920 ruCFaithfulBase) 0 a *
          ChainArrays.levT 1920 (ruField1920 0) (ruBaseArr 1920 ruCFaithfulBase) 1 b} := by
      rw [RawSchreierDatum.originalSubgroup, Subgroup.closure_le]
      intro y hy
      change y ∈ ruChainJ.original.toList at hy
      rw [hJo] at hy
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
      have hj' := List.mem_range.1 hj
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      rintro _ rfl
      exact hcY j hj'
    have hc : ∀ i < 7, _ * X i = X i * _ := fun i hi => by
      have hXi : X i ∈ ruChainJ.originalSubgroup :=
        (ruChain_sift hJ (rep_permOfArr (hX i hi)).1).1 (hXJ i hi)
      exact Subgroup.mem_centralizer_iff.1 (hJC hXi) _ rfl
    have hgK := cent_le_K hF hK hcF hcK hKH hKX hX tup par gen h0 hs hd hmem hc
    exact (ruChain_sift hJ rt).2 (PK _ hgK hcY)

end CertificateChecks.KernelSporSch.RuCG

end
