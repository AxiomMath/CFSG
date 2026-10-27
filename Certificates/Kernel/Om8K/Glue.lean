module

public import Certificates.Data.Kernel.Om8K.Defs
public import Certificates.Kernel.Om8K.Data
import Certificates.Kernel.Om8K.Check
import CFSG.Certificates.Kernel.Om8KSound

public section

namespace CFSG.KC.Om8K

open CFSG.CGT.Harada80 CFSG.CGT.Harada80.OmegaEight CFSG.Quasithin.SteinbergCB.G2Two
  CFSG.Quasithin.SteinbergCB.I16

theorem nsCodes_lt : ∀ u ∈ nsCodes, u < 256 := by decide +kernel

theorem nsCheck_eq : nsCheck = true := by
  have hK := nsK_ok
  unfold nsK nsKW at hK
  unfold nsCheck
  rw [List.all_eq_true] at hK ⊢
  intro c hc
  have h := Nat.eq_of_beq_eq_true (hK c hc)
  rw [nsMask_bit] at h
  have key : CFSG.PGLModel.minusQuadForm 3 (1 : ZMod 2) 1 (vec 3 c) ≠ 0 ↔ c ∈ nsCodes := by
    rw [q_iff]
    change qS c % 2 = _ at h
    by_cases hm : c ∈ nsCodes <;> simp [hm] at h <;> simp [h, hm]
  have : decide (CFSG.PGLModel.minusQuadForm 3 (1 : ZMod 2) 1 (vec 3 c) ≠ 0) =
      nsCodes.contains c := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff, List.contains_iff_mem]
    exact key
  rw [this]
  exact beq_self_eq_true _

theorem reflChain_lt (L : List ℕ) {x : ℕ} (hx : x < 256) : reflChain 3 L x < 256 := by
  cases L with
  | nil => exact hx
  | cons u L =>
    have := reflCode_lt 3 u (reflChain 3 L x)
    change reflCode 3 u (reflChain 3 L x) < 256
    simpa using this

theorem reflChain_eq (L : List ℕ) (hL : ∀ u ∈ L, u < 256) {x : ℕ} (hx : x < 256) :
    reflChain 3 L x = List.rec (motive := fun _ => ℕ) x (fun u _ ih => reflK u ih) L := by
  induction L with
  | nil => rfl
  | cons u L ih =>
    change reflCode 3 u (reflChain 3 L x) = reflK u (List.rec (motive := fun _ => ℕ) x
      (fun u _ ih => reflK u ih) L)
    rw [reflK_eq (hL u List.mem_cons_self) (reflChain_lt L hx),
      ih (fun v hv => hL v (List.mem_cons_of_mem _ hv))]

theorem genCheck_eq : genCheck = true := by
  have hK := genK_ok
  unfold genK genKW at hK
  unfold genCheck
  rw [List.all_eq_true] at hK ⊢
  intro i hi
  have hKi := hK i hi
  rw [List.all_eq_true] at hKi ⊢
  intro x hx
  have h := Nat.eq_of_beq_eq_true (hKi x hx)
  have hi' := List.mem_range.1 hi
  have hL : ∀ u ∈ sChain i, u < 256 := fun u hu => nsCodes_lt u (sChain_mem ⟨i, hi'⟩ u hu)
  rw [beq_iff_eq, ← mAppK_eq, h, reflChain_eq _ hL (List.mem_range.1 hx)]

theorem relCheck_eq : relCheck = true := relCheck_ok

theorem words_eq : words = WS.chars.map
    (fun cs => cs.map fun c => if c = '1' then (1 : Fin 2) else 0) := by
  unfold words
  rw [WS.eq, List.map_map]
  apply List.map_congr_left
  intro cs _
  simp [wordOf, String.toList_ofList]

theorem wordCheck_eq : wordCheck = true := by
  have hK := wordsK_ok
  unfold wordsK at hK
  rw [Bool.and_eq_true] at hK
  obtain ⟨hlen, hall⟩ := hK
  unfold wordCheck
  rw [words_eq, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [List.length_map, Nat.eq_of_beq_eq_true hlen]
    exact beq_self_eq_true _
  · rw [List.zip_map_right, List.all_map, List.all_eq_true]
    rw [List.all_eq_true] at hall
    intro p hp
    have hw := Nat.eq_of_beq_eq_true (hall p hp)
    have hu : p.1 < 256 := nsCodes_lt _ (List.of_mem_zip hp).1
    have hv : v0Code < 256 := by decide
    simp only [Function.comp, Prod.map, id]
    rw [List.all_eq_true]
    intro x hx
    have hx' := List.mem_range.1 hx
    rw [beq_iff_eq, reflK_eq hv hx', reflK_eq hu (reflK_lt hv hx')]
    refine lin_eq (f := fun x => mApp (wordCols 8 sCols
        (p.2.map fun c => if c = '1' then (1 : Fin 2) else 0)) x)
      (g := fun x => reflK p.1 (reflK v0Code x)) (fun a b => mApp_xor _ a b)
      (fun a b => by simp only [reflK_xor]) (fun j hj => ?_) x hx'
    rw [← wordLanes_lane p.2 hj, hw, target_lane hu hj]

theorem foxCheck_eq : foxCheck = true := by
  have hK := foxB_ok
  unfold foxB at hK
  unfold foxCheck
  rw [List.all_eq_true] at hK ⊢
  intro v₀ hv₀
  rw [List.all_eq_true]
  intro v₁ hv₁
  by_cases hr : (rels.all fun r => foxCode sCols [v₀, v₁] r == 0) = true
  · rw [List.all_eq_true] at hr
    have h0 : foxK 0 v₀ = 0 := by
      have := hr [0, 0, 0, 0, 0] (by simp [rels])
      rw [beq_iff_eq, fox0] at this
      exact this
    have h1 : foxK 1 v₁ = 0 := by
      have := hr [1, 1, 1, 1, 1] (by simp [rels])
      rw [beq_iff_eq, fox1] at this
      exact this
    have hK0 := hK v₀ hv₀
    rw [h0, Bool.or_eq_true, List.all_eq_true] at hK0
    have hb : bK bmap (v₀ * 256 + v₁) = 1 := by
      rcases hK0 with hK0 | hK0
      · simp at hK0
      · have := hK0 v₁ hv₁
        rw [h1] at this
        simp only [Nat.beq_refl, Bool.not_true, Bool.false_or] at this
        exact Nat.eq_of_beq_eq_true this
    obtain ⟨x, hx, hk⟩ := bmap_bit hb
    have ha : mApp (sCols.getD 0 []) x ^^^ x < 256 :=
      Nat.xor_lt_two_pow (n := 8) (mApp_lt_pow _ (sCols_lt 0) x) hx
    have hb' : mApp (sCols.getD 1 []) x ^^^ x < 256 :=
      Nat.xor_lt_two_pow (n := 8) (mApp_lt_pow _ (sCols_lt 1) x) hx
    have hv₀' := List.mem_range.1 hv₀
    have hv₁' := List.mem_range.1 hv₁
    have e0 : v₀ = mApp (sCols.getD 0 []) x ^^^ x := by omega
    have e1 : v₁ = mApp (sCols.getD 1 []) x ^^^ x := by omega
    rw [Bool.or_eq_true]
    right
    rw [List.any_eq_true]
    exact ⟨x, List.mem_range.2 hx, by
      simp only [Bool.and_eq_true, beq_iff_eq]
      exact ⟨e0, e1⟩⟩
  · simp [hr]

end CFSG.KC.Om8K

end
