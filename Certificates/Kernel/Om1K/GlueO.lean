module

public import Certificates.Kernel.Om1K.Glue
public import Certificates.Kernel.Om1K.ChecksO
public import Certificates.Kernel.Om1K.ChecksC

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelOm1

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Raw.Orb CFSG.KC.BfsPin CFSG.KC.SetOrb
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check
open CertificateChecks.KernelOm2 (pc2 wAK)
open CertificateChecks.KernelLC.E8 (RT FT NEG)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711 (Om1Facts.E Om1Facts.G Om1Facts.e
  Om1Facts.z Om1Facts.neg Om1Facts.orb)
open scoped Pointwise

def codeSet (len C : Nat) : Set (Fin 240) := {x | ∃ t < len, pg 8 (mask 8) C t = x.val}

theorem mem_codeSet {len C : Nat} {x : Fin 240} :
    x ∈ codeSet len C ↔ ∃ t < len, pg 8 (mask 8) C t = x.val := Iff.rfl

theorem oband {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := CFSG.KC.SetOrb.band h

theorem img_set {len P C C' M M' : Nat} {g : Equiv.Perm (Fin 240)} (hP : PR P g)
    (hC : codeOK 240 8 len C M = true) (hC' : codeOK 240 8 len C' M' = true)
    (h : imgK 8 len P C = M') : g '' codeSet len C = codeSet len C' := by
  obtain ⟨c1, -, -⟩ := codeOK_facts hC
  obtain ⟨-, -, m'⟩ := codeOK_facts hC'
  ext y
  rw [mem_codeSet, ← mem_maskK, m', ← h, mem_imgK]
  constructor
  · rintro ⟨x, ⟨t, ht, hx⟩, rfl⟩
    exact ⟨t, ht, by rw [hx, pr_ip hP]⟩
  · rintro ⟨t, ht, e⟩
    refine ⟨⟨_, c1 t ht⟩, ⟨t, ht, rfl⟩, Fin.ext ?_⟩
    rw [← pr_ip hP]
    exact e

theorem set_neg {len C M m : Nat} (hm : m < 256) (hC : codeOK 240 8 len C M = true)
    (h : Nat.beq (eqMaskK 240 8 (FT m) NEG) M = true) : codeSet len C = Om1Facts.neg m := by
  have hM := Nat.eq_of_beq_eq_true h
  obtain ⟨-, -, hmk⟩ := codeOK_facts hC
  ext x
  rw [mem_codeSet, ← mem_maskK, hmk, ← hM, mem_eqMaskK, pr_ip (pr_e hm), pr_ip pr_z]
  change _ ↔ Om1Facts.e m x = Om1Facts.z x
  rw [Fin.ext_iff]
  exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩

theorem codeSet_ncard (len C : Nat) : (codeSet len C).ncard ≤ len := by
  calc (codeSet len C).ncard = (Fin.val '' codeSet len C).ncard :=
        (Set.ncard_image_of_injective _ Fin.val_injective).symm
    _ ≤ ((fun t => pg 8 (mask 8) C t) '' (Finset.range len : Set ℕ)).ncard := by
        refine Set.ncard_le_ncard ?_ (((Finset.range len).finite_toSet).image _)
        rintro _ ⟨x, ⟨t, ht, hx⟩, rfl⟩
        exact ⟨t, by simpa using ht, hx⟩
    _ ≤ (Finset.range len : Set ℕ).ncard := Set.ncard_image_le (Finset.finite_toSet _)
    _ = len := by rw [Set.ncard_coe_finset, Finset.card_range]

theorem key_of_set {len C C' M M' : Nat} (hC : codeOK 240 8 len C M = true)
    (hC' : codeOK 240 8 len C' M' = true) (h : codeSet len C = codeSet len C') :
    keyK 240 8 len C = keyK 240 8 len C' := by
  obtain ⟨c1, -, -⟩ := codeOK_facts hC
  obtain ⟨c1', -, -⟩ := codeOK_facts hC'
  have hmem : ∀ x, x ∈ (codeArr 8 len C).toList ↔ x ∈ (codeArr 8 len C').toList := by
    intro x
    rw [mem_codeArr, mem_codeArr]
    constructor
    · rintro ⟨t, ht, rfl⟩
      have hx : (⟨pg 8 (mask 8) C t, c1 t ht⟩ : Fin 240) ∈ codeSet len C' := h ▸ ⟨t, ht, rfl⟩
      exact hx
    · rintro ⟨t, ht, rfl⟩
      have hx : (⟨pg 8 (mask 8) C' t, c1' t ht⟩ : Fin 240) ∈ codeSet len C := h.symm ▸ ⟨t, ht, rfl⟩
      exact hx
  have e : codeArr 8 len C = codeArr 8 len C' :=
    Array.ext' (eq_of_pairwise_lt (pairwise_codeArr hC) (pairwise_codeArr hC') hmem)
  rw [← foldl_code 240 8 C len, ← foldl_code 240 8 C' len, e]

theorem set_inj {N len : Nat} {C M S : Nat → Nat}
    (hc : ∀ i < N, codeOK 240 8 len (C i) (M i) = true)
    (hd : distinctK N (fun i => keyK 240 8 len (C i)) S = true) :
    ∀ a < N, ∀ b < N, codeSet len (C a) = codeSet len (C b) → a = b :=
  fun a ha b hb e => distinctK_inj hd a ha b hb (key_of_set (hc a ha) (hc b hb) e)

theorem tree_img {len ng N : Nat} {G C M X D : Nat → Nat} {K : Subgroup (Equiv.Perm (Fin 240))}
    (hG : ∀ k < ng, ∃ g ∈ K, PR (G k) g)
    (hc : ∀ i < N, codeOK 240 8 len (C (X i)) (M (X i)) = true)
    (ht : ∀ i < N, treeK 8 len ng G C M X D i = true) :
    ∀ i < N, ∃ g ∈ K, codeSet len (C (X i)) = g '' codeSet len (C (X 0)) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h
      exact ⟨1, K.one_mem, by simp⟩
    · obtain ⟨hp, hl, e⟩ := treeK_spec (ht i hi) h
      obtain ⟨g, hg, hpg⟩ := ih _ hp (by omega)
      obtain ⟨u, hu, pu⟩ := hG _ hl
      refine ⟨u * g, K.mul_mem hu hg, ?_⟩
      rw [← img_set pu (hc _ (by omega)) (hc i hi) e, hpg, Equiv.Perm.coe_mul, Set.image_comp]

theorem le_ncard {β : Type*} {T : Set β} (hT : T.Finite) {N : Nat} (f : Nat → β)
    (hf : ∀ i < N, f i ∈ T) (hinj : ∀ a < N, ∀ b < N, f a = f b → a = b) : N ≤ T.ncard := by
  have hnd : ((List.range N).map f).Nodup :=
    List.Nodup.map_on (fun a ha b hb e => hinj a (List.mem_range.1 ha) b (List.mem_range.1 hb) e)
      List.nodup_range
  have := hnd.length_le_ncard hT fun x hx => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    exact hf i (List.mem_range.1 hi)
  simpa using this

theorem orb_bound {len ng N : Nat} {G C M D S : Nat → Nat} {K : Subgroup (Equiv.Perm (Fin 240))}
    {S0 : Set (Fin 240)} (hG : ∀ k < ng, ∃ g ∈ K, PR (G k) g)
    (hc : ∀ i < N, codeOK 240 8 len (C i) (M i) = true)
    (ht : ∀ i < N, treeK 8 len ng G C M (fun j => j) D i = true)
    (hd : distinctK N (fun i => keyK 240 8 len (C i)) S = true)
    (h0 : codeSet len (C 0) = S0) : N ≤ (Om1Facts.orb K S0).ncard := by
  refine le_ncard (Set.toFinite _) (fun i => codeSet len (C i)) (fun i hi => ?_) (set_inj hc hd)
  obtain ⟨g, hg, e⟩ := tree_img (X := fun j => j) hG hc ht i hi
  exact ⟨g, hg, by simpa only [h0] using e⟩

theorem orb_eq (K : Subgroup (Equiv.Perm (Fin 240))) (S : Set (Fin 240)) :
    Om1Facts.orb K S = MulAction.orbit K S := by
  ext T
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g, g.2, rfl⟩

section Chain

variable {H β : Type*} [Group H] [Finite H] [MulAction H β]

theorem card_stab_mul_ncard (ω : β) :
    Nat.card (MulAction.stabilizer H ω) * (MulAction.orbit H ω).ncard = Nat.card H := by
  rw [← MulAction.index_stabilizer, Subgroup.card_mul_index]

theorem chain_bound (r F : β) {a b k : Nat} (ha : a ≤ (MulAction.orbit H r).ncard)
    (hb : b ≤ (MulAction.orbit (MulAction.stabilizer H r) F).ncard)
    (hk : (MulAction.orbit (MulAction.stabilizer H F) r).ncard ≤ k) :
    a * b ≤ k * (MulAction.orbit H F).ncard := by
  have e1 := card_stab_mul_ncard (H := H) F
  have e2 := card_stab_mul_ncard (H := H) r
  have e3 := card_stab_mul_ncard (H := MulAction.stabilizer H F) r
  have e4 := card_stab_mul_ncard (H := MulAction.stabilizer H r) F
  let f : MulAction.stabilizer (MulAction.stabilizer H F) r →
      MulAction.stabilizer (MulAction.stabilizer H r) F := fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  have hf : Function.Injective f := by
    intro x y h
    have h1 : x.1.1 = y.1.1 := congrArg (fun z => z.1.1) h
    exact Subtype.ext (Subtype.ext h1)
  have hst := Nat.card_le_card_of_injective f hf
  have ht : 0 < Nat.card (MulAction.stabilizer (MulAction.stabilizer H r) F) := Nat.card_pos
  have h1 : Nat.card (MulAction.stabilizer (MulAction.stabilizer H r) F) * (a * b) ≤
      Nat.card H := by
    calc Nat.card (MulAction.stabilizer (MulAction.stabilizer H r) F) * (a * b)
        = Nat.card (MulAction.stabilizer (MulAction.stabilizer H r) F) * b * a := by ring
      _ ≤ Nat.card (MulAction.stabilizer (MulAction.stabilizer H r) F) *
          (MulAction.orbit (MulAction.stabilizer H r) F).ncard * a := by gcongr
      _ = Nat.card (MulAction.stabilizer H r) * a := by rw [e4]
      _ ≤ Nat.card (MulAction.stabilizer H r) * (MulAction.orbit H r).ncard := by gcongr
      _ = Nat.card H := e2
  have h2 : Nat.card H ≤ Nat.card (MulAction.stabilizer (MulAction.stabilizer H r) F) *
      (k * (MulAction.orbit H F).ncard) := by
    calc Nat.card H = Nat.card (MulAction.stabilizer H F) * (MulAction.orbit H F).ncard := e1.symm
      _ = Nat.card (MulAction.stabilizer (MulAction.stabilizer H F) r) *
          (MulAction.orbit (MulAction.stabilizer H F) r).ncard * (MulAction.orbit H F).ncard := by
        rw [e3]
      _ ≤ Nat.card (MulAction.stabilizer (MulAction.stabilizer H r) F) * k *
          (MulAction.orbit H F).ncard := by gcongr
      _ = Nat.card (MulAction.stabilizer (MulAction.stabilizer H r) F) *
          (k * (MulAction.orbit H F).ncard) := by ring
  exact Nat.le_of_mul_le_mul_left (h1.trans h2) ht

end Chain

theorem orbOK_all : ∀ i < 3150, A.orbOK i = true := by
  intro i hi
  have hc : ∀ c < 63, A.orbOKc c = true := by
    intro c hc

    interval_cases c
    exacts [A.orbOKc0, A.orbOKc1, A.orbOKc2, A.orbOKc3, A.orbOKc4, A.orbOKc5, A.orbOKc6,
      A.orbOKc7, A.orbOKc8, A.orbOKc9, A.orbOKc10, A.orbOKc11, A.orbOKc12, A.orbOKc13,
      A.orbOKc14, A.orbOKc15, A.orbOKc16, A.orbOKc17, A.orbOKc18, A.orbOKc19, A.orbOKc20,
      A.orbOKc21, A.orbOKc22, A.orbOKc23, A.orbOKc24, A.orbOKc25, A.orbOKc26, A.orbOKc27,
      A.orbOKc28, A.orbOKc29, A.orbOKc30, A.orbOKc31, A.orbOKc32, A.orbOKc33, A.orbOKc34,
      A.orbOKc35, A.orbOKc36, A.orbOKc37, A.orbOKc38, A.orbOKc39, A.orbOKc40, A.orbOKc41,
      A.orbOKc42, A.orbOKc43, A.orbOKc44, A.orbOKc45, A.orbOKc46, A.orbOKc47, A.orbOKc48,
      A.orbOKc49, A.orbOKc50, A.orbOKc51, A.orbOKc52, A.orbOKc53, A.orbOKc54, A.orbOKc55,
      A.orbOKc56, A.orbOKc57, A.orbOKc58, A.orbOKc59, A.orbOKc60, A.orbOKc61, A.orbOKc62]
  have h := allN_spec (hc (i / 50) (by omega)) (i % 50) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 50 (i / 50)) (i % 50) = i := Nat.div_add_mod i 50
  rw [e] at h
  exact h

theorem oaOK_all : ∀ i < 3780, A.oaOK i = true := by
  intro i hi
  have hc : ∀ c < 63, A.oaOKc c = true := by
    intro c hc
    interval_cases c
    exacts [A.oaOKc0, A.oaOKc1, A.oaOKc2, A.oaOKc3, A.oaOKc4, A.oaOKc5, A.oaOKc6,
      A.oaOKc7, A.oaOKc8, A.oaOKc9, A.oaOKc10, A.oaOKc11, A.oaOKc12, A.oaOKc13,
      A.oaOKc14, A.oaOKc15, A.oaOKc16, A.oaOKc17, A.oaOKc18, A.oaOKc19, A.oaOKc20,
      A.oaOKc21, A.oaOKc22, A.oaOKc23, A.oaOKc24, A.oaOKc25, A.oaOKc26, A.oaOKc27,
      A.oaOKc28, A.oaOKc29, A.oaOKc30, A.oaOKc31, A.oaOKc32, A.oaOKc33, A.oaOKc34,
      A.oaOKc35, A.oaOKc36, A.oaOKc37, A.oaOKc38, A.oaOKc39, A.oaOKc40, A.oaOKc41,
      A.oaOKc42, A.oaOKc43, A.oaOKc44, A.oaOKc45, A.oaOKc46, A.oaOKc47, A.oaOKc48,
      A.oaOKc49, A.oaOKc50, A.oaOKc51, A.oaOKc52, A.oaOKc53, A.oaOKc54, A.oaOKc55,
      A.oaOKc56, A.oaOKc57, A.oaOKc58, A.oaOKc59, A.oaOKc60, A.oaOKc61, A.oaOKc62]
  have h := allN_spec (hc (i / 60) (by omega)) (i % 60) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 60 (i / 60)) (i % 60) = i := Nat.div_add_mod i 60
  rw [e] at h
  exact h

theorem ocOK_all : ∀ i < 3780, A.ocOK i = true := by
  intro i hi
  have hc : ∀ c < 63, A.ocOKc c = true := by
    intro c hc
    interval_cases c
    exacts [A.ocOKc0, A.ocOKc1, A.ocOKc2, A.ocOKc3, A.ocOKc4, A.ocOKc5, A.ocOKc6,
      A.ocOKc7, A.ocOKc8, A.ocOKc9, A.ocOKc10, A.ocOKc11, A.ocOKc12, A.ocOKc13,
      A.ocOKc14, A.ocOKc15, A.ocOKc16, A.ocOKc17, A.ocOKc18, A.ocOKc19, A.ocOKc20,
      A.ocOKc21, A.ocOKc22, A.ocOKc23, A.ocOKc24, A.ocOKc25, A.ocOKc26, A.ocOKc27,
      A.ocOKc28, A.ocOKc29, A.ocOKc30, A.ocOKc31, A.ocOKc32, A.ocOKc33, A.ocOKc34,
      A.ocOKc35, A.ocOKc36, A.ocOKc37, A.ocOKc38, A.ocOKc39, A.ocOKc40, A.ocOKc41,
      A.ocOKc42, A.ocOKc43, A.ocOKc44, A.ocOKc45, A.ocOKc46, A.ocOKc47, A.ocOKc48,
      A.ocOKc49, A.ocOKc50, A.ocOKc51, A.ocOKc52, A.ocOKc53, A.ocOKc54, A.ocOKc55,
      A.ocOKc56, A.ocOKc57, A.ocOKc58, A.ocOKc59, A.ocOKc60, A.ocOKc61, A.ocOKc62]
  have h := allN_spec (hc (i / 60) (by omega)) (i % 60) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 60 (i / 60)) (i % 60) = i := Nat.div_add_mod i 60
  rw [e] at h
  exact h

theorem orb_parts {i : Nat} (hi : i < 3150) :
    codeOK 240 8 24 (A.Orb.C i) (A.Orb.M i) = true ∧
      closK 8 24 7 3150 A.XG.G A.Orb.C A.Orb.M (fun j => j) A.Orb.E i = true ∧
      treeK 8 24 7 A.XG.G A.Orb.C A.Orb.M (fun j => j) A.Orb.D i = true ∧ A.covK i = true := by
  have h := orbOK_all i hi
  unfold A.orbOK at h
  obtain ⟨h1, h⟩ := oband h
  obtain ⟨h2, h⟩ := oband h
  obtain ⟨h3, h4⟩ := oband h
  exact ⟨h1, h2, h3, h4⟩

theorem orb_code : ∀ i < 3150, codeOK 240 8 24 (A.Orb.C i) (A.Orb.M i) = true :=
  fun _ hi => (orb_parts hi).1

theorem orb_inj : ∀ a < 3150, ∀ b < 3150,
    codeSet 24 (A.Orb.C a) = codeSet 24 (A.Orb.C b) → a = b :=
  set_inj orb_code A.kDist

theorem F0_eq : codeSet 24 (A.Orb.C 0) = Om1Facts.neg 15 :=
  set_neg (by norm_num) (orb_code 0 (by norm_num)) A.kF0

theorem xg_mem : ∀ k < 7, ∃ g ∈ Om1Facts.G wX, PR (A.XG.G k) g := fun k hk =>
  ⟨_, E_mem_G (getD_mem (by rw [A.kLens.2.2.2.2.2.1]; exact hk)), pr_XG hk⟩

theorem tgO_mem : ∀ k < 7, ∃ g ∈ Om1Facts.G wT, PR (A.TG.G k) g := fun k hk =>
  ⟨_, E_mem_G (getD_mem (by rw [A.kLens.2.1]; exact hk)), pr_TG hk⟩

theorem orb15_bound : 3150 ≤ (Om1Facts.orb (Om1Facts.G wX) (Om1Facts.neg 15)).ncard :=
  orb_bound xg_mem orb_code (fun i hi => (orb_parts hi).2.2.1) A.kDist F0_eq

theorem oa_code : ∀ i < 3780, codeOK 240 8 4 (A.OA.C i) (A.OA.M i) = true :=
  fun i hi => (oband (oaOK_all i hi)).1

theorem orb3_bound : 3780 ≤ (Om1Facts.orb (Om1Facts.G wX) (Om1Facts.neg 3)).ncard :=
  orb_bound xg_mem oa_code (fun i hi => (oband (oaOK_all i hi)).2) A.kDistA
    (set_neg (by norm_num) (oa_code 0 (by norm_num)) A.kFa)

theorem orb_gen : ∀ k < 7, ∀ i < 3150, ∃ j < 3150,
    Om1Facts.E (wX.getD k []) '' codeSet 24 (A.Orb.C i) = codeSet 24 (A.Orb.C j) := by
  intro k hk i hi
  obtain ⟨j, hj, e⟩ := closK_spec (orb_parts hi).2.1 k hk
  exact ⟨j, hj, img_set (pr_XG hk) (orb_code i hi) (orb_code j hj) e⟩

theorem orb_closed : ∀ g ∈ Om1Facts.G wX, ∀ i < 3150, ∃ j < 3150,
    g '' codeSet 24 (A.Orb.C i) = codeSet 24 (A.Orb.C j) := by
  intro g hg
  unfold Om1Facts.G at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    obtain ⟨k, hk, rfl⟩ := mem_getD hw
    rw [A.kLens.2.2.2.2.2.1] at hk
    exact orb_gen k hk
  | one =>
    intro i hi
    exact ⟨i, hi, by simp⟩
  | mul x y _ _ hx hy =>
    intro i hi
    obtain ⟨j, hj, ej⟩ := hy i hi
    obtain ⟨l, hl, el⟩ := hx j hj
    exact ⟨l, hl, by rw [Equiv.Perm.coe_mul, Set.image_comp, ej, el]⟩
  | inv x _ hx =>
    intro i hi
    choose! f hf hfe using hx
    let F : Fin 3150 → Fin 3150 := fun a => ⟨f a, hf a a.2⟩
    have hF : Function.Injective F := by
      intro a b hab
      have hab' : f a = f b := congrArg Fin.val hab
      have e : codeSet 24 (A.Orb.C a) = codeSet 24 (A.Orb.C b) :=
        (Set.image_injective.2 x.injective) (by rw [hfe a a.2, hfe b b.2, hab'])
      exact Fin.ext (orb_inj a a.2 b b.2 e)
    obtain ⟨a, ha⟩ := (Finite.injective_iff_surjective.1 hF) ⟨i, hi⟩
    have ha' : f a = i := congrArg Fin.val ha
    refine ⟨a, a.2, ?_⟩
    rw [← ha', ← hfe a a.2, Set.image_image]
    simp

theorem sub_case {N : Nat} {X D Y : Nat → Nat} {s : Nat} (hs : s < 8)
    (hsub : A.subOK N X D (A.WS.G s) = true) {j : Nat} (hj : A.inSub N X Y j = true) :
    ∃ w ∈ wSub, ∃ u ∈ Om1Facts.G wT,
      codeSet 24 (A.Orb.C j) = (u * Om1Facts.E w) '' Om1Facts.neg 15 := by
  unfold A.subOK at hsub
  obtain ⟨ht, h⟩ := oband hsub
  obtain ⟨hlt, hr⟩ := oband h
  unfold A.inSub at hj
  rw [Bool.and_eq_true] at hj
  have hY := Nat.blt_eq.mp hj.1
  have hX := Nat.eq_of_beq_eq_true hj.2
  have hc : ∀ i < N, codeOK 240 8 24 (A.Orb.C (X i)) (A.Orb.M (X i)) = true :=
    fun i hi => orb_code (X i) (Nat.blt_eq.mp (allN_spec hlt i hi))
  obtain ⟨u, hu, e⟩ := tree_img tgO_mem hc (allN_spec ht) (Y j) hY
  have himg := img_set (pr_WS hs) (orb_code 0 (by norm_num)) (hc 0 (by omega))
    (Nat.eq_of_beq_eq_true hr)
  refine ⟨wSub.getD s [], getD_mem (by rw [A.kLens.2.2.2.2.1]; exact hs), u, hu, ?_⟩
  rw [← hX, e, ← himg, F0_eq, Equiv.Perm.coe_mul, Set.image_comp]

theorem cover_fact : ∀ g ∈ Om1Facts.G wX, g '' Om1Facts.neg 15 = Om1Facts.neg 15 ∨
    g '' Om1Facts.neg 15 = Om1Facts.E wG1 '' Om1Facts.neg 15 ∨
    ∃ w ∈ wSub, ∃ s ∈ Om1Facts.G wT, g '' Om1Facts.neg 15 = (s * Om1Facts.E w) '' Om1Facts.neg 15 := by
  intro g hg
  obtain ⟨j, hj, e⟩ := orb_closed g hg 0 (by norm_num)
  rw [F0_eq] at e
  rw [e]
  have hcov := (orb_parts hj).2.2.2
  unfold A.covK at hcov
  simp only [Bool.or_eq_true, or_assoc] at hcov
  rcases hcov with h | h | h | h | h | h | h | h | h | h
  · left
    rw [Nat.eq_of_beq_eq_true h, F0_eq]
  · right
    left
    rw [← img_set pr_g1 (orb_code 0 (by norm_num)) (orb_code j hj) (Nat.eq_of_beq_eq_true h),
      F0_eq]
  · exact Or.inr (Or.inr (sub_case (s := 0) (by norm_num) A.kSub0 h))
  · exact Or.inr (Or.inr (sub_case (s := 1) (by norm_num) A.kSub1 h))
  · exact Or.inr (Or.inr (sub_case (s := 2) (by norm_num) A.kSub2 h))
  · exact Or.inr (Or.inr (sub_case (s := 3) (by norm_num) A.kSub3 h))
  · exact Or.inr (Or.inr (sub_case (s := 4) (by norm_num) A.kSub4 h))
  · exact Or.inr (Or.inr (sub_case (s := 5) (by norm_num) A.kSub5 h))
  · exact Or.inr (Or.inr (sub_case (s := 6) (by norm_num) A.kSub6 h))
  · exact Or.inr (Or.inr (sub_case (s := 7) (by norm_num) A.kSub7 h))

theorem tr_bound {N : Nat} {X Y D : Nat → Nat} {s : Nat} (hs : s < 8) (hN : N = 3150)
    (h : A.transOK N X Y D (A.WS.G s) = true) :
    3150 ≤ (Om1Facts.orb (Om1Facts.G (wT ++ [wSub.getD s []])) (Om1Facts.neg 15)).ncard := by
  subst hN
  unfold A.transOK at h
  obtain ⟨ht, h⟩ := oband h
  obtain ⟨hinv, h0⟩ := oband h
  have hX : ∀ i < 3150, invK X Y i = true ∧ X i < 3150 := fun i hi => by
    obtain ⟨a, b⟩ := oband (allN_spec hinv i hi)
    exact ⟨a, Nat.blt_eq.mp b⟩
  have hc : ∀ i < 3150, codeOK 240 8 24 (A.Orb.C (X i)) (A.Orb.M (X i)) = true :=
    fun i hi => orb_code _ (hX i hi).2
  have hG : ∀ k < 8, ∃ g ∈ Om1Facts.G (wT ++ [wSub.getD s []]), PR (A.tgR (A.WS.G s) k) g := by
    intro k hk
    unfold A.tgR
    cases hb : Nat.blt k 7
    · exact ⟨_, E_mem_G (List.mem_append_right _ (List.mem_singleton_self _)), pr_WS hs⟩
    · have hk7 := Nat.blt_eq.mp hb
      exact ⟨_, E_mem_G (List.mem_append_left _ (getD_mem (by rw [A.kLens.2.1]; exact hk7))),
        pr_TG hk7⟩
  have htree := tree_img hG hc (allN_spec ht)
  have hX0 : X 0 = 0 := Nat.eq_of_beq_eq_true h0
  refine le_ncard (Set.toFinite _) (fun i => codeSet 24 (A.Orb.C (X i))) (fun i hi => ?_)
    (fun a ha b hb e => ?_)
  · obtain ⟨g, hg, e⟩ := htree i hi
    exact ⟨g, hg, by rw [e, hX0, F0_eq]⟩
  · have hab := orb_inj _ (hX a ha).2 _ (hX b hb).2 e
    have ia : Y (X a) = a := Nat.eq_of_beq_eq_true (hX a ha).1
    have ib : Y (X b) = b := Nat.eq_of_beq_eq_true (hX b hb).1
    rw [← ia, ← ib, hab]

theorem trans_fact : ∀ w ∈ wSub,
    3150 ≤ (Om1Facts.orb (Om1Facts.G (wT ++ [w])) (Om1Facts.neg 15)).ncard := by
  intro w hw
  obtain ⟨s, hs, rfl⟩ := mem_getD hw
  rw [A.kLens.2.2.2.2.1] at hs
  interval_cases s
  · exact tr_bound (by norm_num) A.kTrN.1 A.kTr0
  · exact tr_bound (by norm_num) A.kTrN.2.1 A.kTr1
  · exact tr_bound (by norm_num) A.kTrN.2.2.1 A.kTr2
  · exact tr_bound (by norm_num) A.kTrN.2.2.2.1 A.kTr3
  · exact tr_bound (by norm_num) A.kTrN.2.2.2.2.1 A.kTr4
  · exact tr_bound (by norm_num) A.kTrN.2.2.2.2.2.1 A.kTr5
  · exact tr_bound (by norm_num) A.kTrN.2.2.2.2.2.2.1 A.kTr6
  · exact tr_bound (by norm_num) A.kTrN.2.2.2.2.2.2.2 A.kTr7

theorem ro_code : ∀ i < 240, codeOK 240 8 1 (A.RO.C i) (A.RO.M i) = true :=
  fun i hi => (oband (allN_spec A.kRO i hi)).1

theorem ro_tree : ∀ i < 240, treeK 8 1 7 A.XG.G A.RO.C A.RO.M (fun j => j) A.RO.D i = true :=
  fun i hi => (oband (allN_spec A.kRO i hi)).2

theorem rootK_lt : A.rootK < 240 := (codeOK_facts (ro_code 0 (by norm_num))).1 0 (by norm_num)

noncomputable def rO : Fin 240 := ⟨A.rootK, rootK_lt⟩

theorem R_eq : codeSet 1 (A.RO.C 0) = {rO} := by
  ext x
  rw [mem_codeSet, Set.mem_singleton_iff]
  constructor
  · rintro ⟨t, ht, e⟩
    have h0 : t = 0 := by omega
    subst h0
    exact Fin.ext e.symm
  · rintro rfl
    exact ⟨0, by norm_num, rfl⟩

theorem oc_code : ∀ i < 3780, codeOK 240 8 8 (A.OC.C i) (A.OC.M i) = true :=
  fun i hi => (oband (ocOK_all i hi)).1

theorem Fc_eq : codeSet 8 (A.OC.C 0) = Om1Facts.neg 23 :=
  set_neg (by norm_num) (oc_code 0 (by norm_num)) A.kFc

theorem r_mem : rO ∈ Om1Facts.neg 23 := by
  rw [← Fc_eq]
  exact ⟨0, by norm_num, (Nat.eq_of_beq_eq_true A.kRoot).symm⟩

theorem not_beq_zero {p : Nat} (h : 0 < p) : Nat.beq p 0 = false := by
  cases e : Nat.beq p 0
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) (by omega)

theorem tt_mem : ∀ p < 240, (∃ g ∈ Om1Facts.G wX, PR (A.TT.G p) g) ∧
    ∃ g ∈ Om1Facts.G wX, PR (A.TI.G p) g := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro hp
    have h := allN_spec A.kTT p hp
    unfold A.ttOK at h
    rcases Nat.eq_zero_or_pos p with h0 | h0
    · subst h0
      rw [show Nat.beq 0 0 = true from rfl] at h
      have h' : Nat.beq (A.TT.G 0) (pidn 240 8) = true ∧ Nat.beq (A.TI.G 0) (pidn 240 8) = true :=
        oband h
      obtain ⟨a, b⟩ := h'
      refine ⟨⟨1, one_mem _, ?_⟩, ⟨1, one_mem _, ?_⟩⟩
      · rw [Nat.eq_of_beq_eq_true a]
        exact pr_pid
      · rw [Nat.eq_of_beq_eq_true b]
        exact pr_pid
    · rw [not_beq_zero h0] at h
      obtain ⟨e1, e2⟩ := oband h
      obtain ⟨hpar, hlab, -⟩ := treeK_spec (ro_tree p hp) h0
      obtain ⟨⟨a, ha, pa⟩, ⟨b, hb, pb⟩⟩ := ih _ hpar (by omega)
      have hw := E_mem_G (getD_mem (ws := wX) (by rw [A.kLens.2.2.2.2.2.1]; exact hlab))
      refine ⟨⟨_, mul_mem hw ha, ?_⟩, ⟨_, mul_mem hb (inv_mem hw), ?_⟩⟩
      · rw [Nat.eq_of_beq_eq_true e1]
        exact pr_pc (pr_XG hlab) pa
      · rw [Nat.eq_of_beq_eq_true e2]
        exact pr_pc pb (pr_XIinv hlab)

noncomputable abbrev Kr : Subgroup (Equiv.Perm (Fin 240)) :=
  Om1Facts.G wX ⊓ MulAction.stabilizer (Equiv.Perm (Fin 240)) (codeSet 1 (A.RO.C 0))

theorem sg_mem : ∀ j < 10, ∃ g ∈ Kr, PR (A.SG.G j) g := by
  intro j hj
  have h := allN_spec A.kSG j hj
  unfold A.sgOK at h
  simp only [CFSG.KC.SetOrb.strictB_eq] at h
  obtain ⟨hq, h⟩ := oband h
  obtain ⟨hk, h⟩ := oband h
  obtain ⟨hp, h⟩ := oband h
  obtain ⟨he, hfix⟩ := oband h
  obtain ⟨a, ha, pa⟩ := (tt_mem _ (Nat.blt_eq.mp hp)).1
  obtain ⟨b, hb, pb⟩ := (tt_mem _ (Nat.blt_eq.mp hq)).2
  have hk7 := Nat.blt_eq.mp hk
  have hP : PR (A.SG.G j) (b * (Om1Facts.E (wX.getD (pg 8 (mask 8) (A.IX.G j) 1) []) * a)) := by
    rw [Nat.eq_of_beq_eq_true he]
    exact pr_pc pb (pr_pc (pr_XG hk7) pa)
  refine ⟨_, Subgroup.mem_inf.2 ⟨mul_mem hb (mul_mem (E_mem_G (getD_mem
    (by rw [A.kLens.2.2.2.2.2.1]; exact hk7))) ha), ?_⟩, hP⟩
  rw [MulAction.mem_stabilizer_iff]
  change _ '' _ = _
  rw [R_eq, Set.image_singleton, Set.singleton_eq_singleton_iff]
  refine Fin.ext ?_
  rw [Equiv.Perm.smul_def, ← pr_ip hP]
  exact Nat.eq_of_beq_eq_true hfix

theorem ro_bound : 240 ≤ (Om1Facts.orb (Om1Facts.G wX) (codeSet 1 (A.RO.C 0))).ncard :=
  orb_bound xg_mem ro_code ro_tree A.kDistR rfl

theorem oc_bound : 3780 ≤ (Om1Facts.orb Kr (Om1Facts.neg 23)).ncard :=
  orb_bound sg_mem oc_code (fun i hi => (oband (ocOK_all i hi)).2) A.kDistC Fc_eq

theorem orb23_bound : 113400 ≤ (Om1Facts.orb (Om1Facts.G wX) (Om1Facts.neg 23)).ncard := by
  have ha : 240 ≤ (MulAction.orbit (Om1Facts.G wX) (codeSet 1 (A.RO.C 0))).ncard := by
    rw [← orb_eq]
    exact ro_bound
  have hb : 3780 ≤ (MulAction.orbit (MulAction.stabilizer (Om1Facts.G wX) (codeSet 1 (A.RO.C 0)))
      (Om1Facts.neg 23)).ncard := by
    refine oc_bound.trans (Set.ncard_le_ncard ?_ (Set.toFinite _))
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.1 hg
    exact ⟨⟨⟨g, hg1⟩, MulAction.mem_stabilizer_iff.2 (MulAction.mem_stabilizer_iff.1 hg2)⟩, rfl⟩
  have hk : (MulAction.orbit (MulAction.stabilizer (Om1Facts.G wX) (Om1Facts.neg 23))
      (codeSet 1 (A.RO.C 0))).ncard ≤ 8 := by
    have hsub : MulAction.orbit (MulAction.stabilizer (Om1Facts.G wX) (Om1Facts.neg 23))
        (codeSet 1 (A.RO.C 0)) ⊆ (fun x => ({x} : Set (Fin 240))) '' Om1Facts.neg 23 := by
      rintro _ ⟨g, rfl⟩
      have hgF : (g.1.1 : Equiv.Perm (Fin 240)) '' Om1Facts.neg 23 = Om1Facts.neg 23 :=
        MulAction.mem_stabilizer_iff.1 g.2
      refine ⟨g.1.1 rO, ?_, ?_⟩
      · have hm := Set.mem_image_of_mem (g.1.1 : Equiv.Perm (Fin 240)) r_mem
        rwa [hgF] at hm
      · change _ = (g.1.1 : Equiv.Perm (Fin 240)) '' codeSet 1 (A.RO.C 0)
        rw [R_eq, Set.image_singleton]
    calc _ ≤ ((fun x => ({x} : Set (Fin 240))) '' Om1Facts.neg 23).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ (Om1Facts.neg 23).ncard := Set.ncard_image_le (Set.toFinite _)
      _ ≤ 8 := by
          rw [← Fc_eq]
          exact codeSet_ncard 8 _
  have := chain_bound (H := Om1Facts.G wX) _ _ ha hb hk
  rw [orb_eq]
  omega

theorem orbit_fact : 3150 ≤ (Om1Facts.orb (Om1Facts.G wX) (Om1Facts.neg 15)).ncard ∧
    3780 ≤ (Om1Facts.orb (Om1Facts.G wX) (Om1Facts.neg 3)).ncard ∧
    113400 ≤ (Om1Facts.orb (Om1Facts.G wX) (Om1Facts.neg 23)).ncard :=
  ⟨orb15_bound, orb3_bound, orb23_bound⟩

end CertificateChecks.KernelOm1

end
