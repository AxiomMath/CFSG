module

public import Certificates.Kernel.UnitarySix.Sec3.G3602Chk
public import Certificates.Kernel.UnitarySix.Sec3.Chains3602
public import Certificates.Kernel.UnitarySix.Sec3.G3601
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.RankThree.Native

theorem wordGA_get : ∀ w : List ℕ, (∀ k ∈ w, k < 18) → ∀ {p : ℕ}, p < 693 →
    pg 10 (mask 10) (wordGA sec3G w) p = ptW w p
  | [], _, p, hp => by
    have e : wordGA sec3G [] = pidn 693 10 := rfl
    rw [e, ← unpack_get hp, ← idA_eq_pidn, CFSG.Monster.B.Co2.idA_get hp]
    rfl
  | k :: w, hw, p, hp => by
    have hk := hw k List.mem_cons_self
    have hw' : ∀ j ∈ w, j < 18 := fun j hj => hw j (List.mem_cons_of_mem _ hj)
    have e : wordGA sec3G (k :: w) = pcomp 693 10 (mask 10) (sec3G k) (wordGA sec3G w) := by
      simp only [wordGA, List.foldr_cons]
    rw [e, comp_get (hc k hk) (wA_unpack hG hc hid hidA w hw').2 hp, wordGA_get w hw' hp]
    rfl

theorem wA_get {w : List ℕ} (hw : ∀ k ∈ w, k < 18) {p : ℕ} (hp : p < 693) :
    (wA w)[p]! = ptW w p := by
  rw [(wK_spec hw).1, unpack_get hp]
  exact wordGA_get w hw hp

theorem key3_wA {w : List ℕ} (hw : ∀ k ∈ w, k < 18) : key3 (wA w) = key3W w := by
  rw [key3, key3W, wA_get hw (by norm_num), wA_get hw (by norm_num), wA_get hw (by norm_num)]
  rfl

theorem keyA3_wA {w : List ℕ} (hw : ∀ k ∈ w, k < 18) : keyA3 (wA w) = keyA3W w := by
  rw [keyA3, keyA3W, wA_get hw (by norm_num), wA_get hw (by norm_num)]
  rfl

theorem yKeys_k : yKeysCheck = true := by
  obtain ⟨h2, h1, h3, hs, -⟩ := tabs_lt
  have h1' : ∀ p ∈ a1Tab, ∀ k ∈ cjW p.1 a1Reps[p.2]!, k < 18 := fun p hp k hk =>
    h1 p hp k (List.mem_append_left _ hk)
  have hs' : ∀ s ∈ singReps, ∀ k ∈ s, k < 18 := fun s hs0 k hk =>
    hs s hs0 k (List.mem_append_left _ hk)
  unfold yKeysCheck
  rw [List.map_congr_left fun p hp => key3_wA (h2 p hp),
    List.map_congr_left fun p hp => wA_get (h1' p hp) (by norm_num : 1 < 693),
    List.map_congr_left fun p hp => wA_get (h1 p hp) (by norm_num : 1 < 693),
    List.map_congr_left fun p hp => keyA3_wA (h3 p hp),
    List.map_congr_left fun s hs0 => wA_get (hs' s hs0) (by norm_num : 1 < 693),
    List.map_congr_left fun s hs0 => wA_get (hs s hs0) (by norm_num : 1 < 693)]
  exact kKeys

theorem gA14_get : (gA 14)[1]! = pg 10 (mask 10) (sec3G 14) 1 := by
  rw [hG 14 (by norm_num), unpack_get (by norm_num)]

theorem a1Reps_k : a1RepsCheck = true := by
  unfold a1RepsCheck
  rw [wA_get (by decide) (by norm_num), wA_get (by decide) (by norm_num), gA14_get]
  exact kReps

theorem singGen_k : singGenCheck = true := by
  unfold singGenCheck
  rw [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, kSingNodup⟩
  refine List.all_eq_true.2 fun s hs => ?_
  rw [wA_get (tabs_lt.2.2.2.2 s hs) (by norm_num)]
  exact List.all_eq_true.1 kSing s hs

theorem forceL_eq : ∀ (L acc : List ℕ) (k : List ℕ → Bool), forceL L acc k = k (L.reverse ++ acc)
  | [], acc, k => rfl
  | h :: t, acc, k => by
    have e : forceL (h :: t) acc k = strictB h fun h' => forceL t (h' :: acc) k := rfl
    rw [e, strictB_eq, forceL_eq t, List.reverse_cons, List.append_assoc, List.singleton_append]

theorem zCls_k : zClsCheck = true := by
  obtain ⟨hc, hm⟩ := zCls_lt'
  unfold zClsCheck
  rw [Bool.and_eq_true]
  refine ⟨?_, List.all_eq_true.2 fun j hj => ?_⟩
  · have hk0 := kZC1
    rw [forceL_eq, List.append_nil] at hk0
    unfold zConjK at hk0
    rw [chK2_K.O_all]
    refine List.all_eq_true.2 fun j hj => ?_
    have hj' := chK2_P j (List.mem_range.1 hj)
    have hk := List.all_eq_true.1 hk0 j hj
    unfold zClsA
    rw [List.all_toArray', List.all_map]
    refine List.all_eq_true.2 fun c hcm => ?_
    have h1 := List.all_eq_true.1 hk (wK c)
      (List.mem_reverse.2 (List.mem_map.2 ⟨c, hcm, rfl⟩))
    rw [strictB_eq] at h1
    simp only [Function.comp_apply]
    rw [(wK_spec (hc c hcm)).1, conj_unpack hj' (wK_spec (hc c hcm)).2, List.any_toArray',
      List.any_map]
    obtain ⟨C', hC', he⟩ := List.any_eq_true.1 h1
    obtain ⟨c', hc', rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hC')
    refine List.any_eq_true.2 ⟨c', hc', ?_⟩
    simp only [Function.comp_apply]
    rw [(wK_spec (hc c' hc')).1, eq_unpack (conj_canon (wK_spec (hc c hcm)).2 hj')
      (wK_spec (hc c' hc')).2]
    exact he
    all_goals rfl
  · have hj' := List.mem_range.1 hj
    obtain ⟨m1, m2, m3, m4⟩ := hm j hj'
    have hk : (Nat.beq (wK (zMs[j]! ++ [14])) (wK ([14] ++ zMs[j]!)) &&
        Nat.beq (wK (cjW zMs[j]! zCls[1]!)) (wK zCls[j + 1]!)) = true := by
      rcases Nat.lt_or_ge j 10 with h | h
      · exact List.all_eq_true.1 kZC2 j (List.mem_range.2 h)
      · have := List.all_eq_true.1 kZC3 (j - 10) (List.mem_range.2 (by omega))
        rwa [Nat.sub_add_cancel h] at this
    rw [Bool.and_eq_true] at hk ⊢
    exact ⟨(eqA_wA m1 m2).trans hk.1, (eqA_wA m3 m4).trans hk.2⟩

end CertificateChecks.KernelU6.Sec3
