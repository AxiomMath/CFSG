module

public import Certificates.Kernel.Misc.YamakiAut.FinalS

public section

namespace CFSG.KD.YamakiAutM

open CFSG.KC.YamakiAutM CFSG.KC.YamakiAut CFSG.KD.YamakiAut CFSG.KD.YamakiRepF CFSG.KD.YamakiRep
  CFSG.KC.YamakiS0 CFSG.KC.YamakiA0 CFSG.KD.YamakiA0 CFSG.KD.BfsK CFSG.KC.BfsEnum
  CFSG.KC.YamakiRep CFSG.ClassicalInvolution.Solomon73.Yamaki
open CFSG.KD.Sp62 (MULF ONE)

theorem wordA_of (gs : Array (Array ℕ)) (c : ℕ → ℕ) :
    ∀ w : List ℕ, (∀ i ∈ w, gs[i]! = arrN (c i)) → wordA gs w = arrN (wordN c w)
  | [], _ => by rw [wordA, wordN, arrN_one]
  | i :: w, h => by
    rw [wordA, wordN, h i List.mem_cons_self,
      wordA_of gs c w fun j hj => h j (List.mem_cons_of_mem _ hj), arrN_mul]

@[expose] def cyOf (a b : ℕ) : ℕ → ℕ := fun i => if i = 0 then a else b

@[expose] noncomputable def stepsK (cg cy : ℕ → ℕ) : List ℕ → List (Bool × List ℕ × List ℕ) → Bool
  | cur, [] => Nat.beq (wordN cg cur) (MULF (RX 5) (RX 4))
  | cur, (kind, w, nxt) :: rest =>
    (if kind then wordsIn idxHhat [w] &&
        Nat.beq (MULF (wordN RX w) (wordN cg nxt)) (MULF (wordN cg cur) (wordN RX w))
      else wordsIn idxN0 [w] &&
        Nat.beq (MULF (wordN RX w) (wordN cy nxt)) (MULF (wordN cy cur) (wordN RX w))) &&
      stepsK cg cy nxt rest

theorem gA_of {w : List ℕ} (h : ∀ i ∈ w, i < 12) : ∀ i ∈ w, (genA ())[i]! = arrN (RX i) :=
  fun i hi => genA_eq12 yfX_gens (h i hi)

theorem gX_of {w : List ℕ} (h : ∀ i ∈ w, i < 2) :
    ∀ i ∈ w, (gX ())[i]! = arrN (RX (12 + i)) := by
  intro i hi
  rcases (by have := h i hi; omega : i = 0 ∨ i = 1) with rfl | rfl
  · exact gX_get0
  · exact gX_get1

theorem ys_of {a b : ℕ} {w : List ℕ} (h : ∀ i ∈ w, i < 2) :
    ∀ i ∈ w, (#[arrN a, arrN b] : Array (Array ℕ))[i]! = arrN (cyOf a b i) := by
  intro i hi
  rcases (by have := h i hi; omega : i = 0 ∨ i = 1) with rfl | rfl
  · rfl
  · rfl

theorem steps_eq (a b : ℕ) : ∀ (l : List (Bool × List ℕ × List ℕ)) (cur : List ℕ),
    (∀ i ∈ cur, i < 2) → (∀ s ∈ l, (∀ i ∈ s.2.1, i < 12) ∧ ∀ i ∈ s.2.2, i < 2) →
      stepsOK (genA ()) (gX ()) #[arrN a, arrN b] cur l =
        stepsK (fun i => RX (12 + i)) (cyOf a b) cur l
  | [], cur, hc, _ => by
    rw [stepsOK, stepsK, wordA_of _ _ cur (gX_of hc), genA_eq12 yfX_gens (by norm_num),
      genA_eq12 yfX_gens (by norm_num), arrN_mul,
      decide_arrN (wordN_lt _) (CFSG.KC.Sp62.MULF_lt _ _)]
  | (kind, w, nxt) :: rest, cur, hc, hl => by
    obtain ⟨hw, hn⟩ := hl _ List.mem_cons_self
    have ih := steps_eq a b rest nxt hn fun s hs => hl s (List.mem_cons_of_mem _ hs)
    cases kind
    · simp only [stepsOK, stepsK, Bool.false_eq_true, ↓reduceIte]
      rw [wordA_of _ _ w (gA_of hw), wordA_of _ _ nxt (ys_of hn), wordA_of _ _ cur (ys_of hc),
        arrN_mul, arrN_mul, decide_arrN (CFSG.KC.Sp62.MULF_lt _ _) (CFSG.KC.Sp62.MULF_lt _ _), ih]
    · simp only [stepsOK, stepsK, ↓reduceIte]
      rw [wordA_of _ _ w (gA_of hw), wordA_of _ _ nxt (gX_of hn), wordA_of _ _ cur (gX_of hc),
        arrN_mul, arrN_mul, decide_arrN (CFSG.KC.Sp62.MULF_lt _ _) (CFSG.KC.Sp62.MULF_lt _ _), ih]

theorem chain_lt : ∀ k < 8, (∀ i ∈ (chainData[k]!).1, i < 2) ∧
    ∀ s ∈ (chainData[k]!).2, (∀ i ∈ s.2.1, i < 12) ∧ ∀ i ∈ s.2.2, i < 2 := by
  decide

theorem ya550712_chain : ∀ k < 8, wordN (fun i => RX (12 + i)) (chainData[k]!).1 = RX 4 ∧
    stepsK (fun i => RX (12 + i)) (cyOf (repC (8 + k)).1 (repC (8 + k)).2) (chainData[k]!).1
      (chainData[k]!).2 = true := by
  unfold repC
  decide +kernel

theorem chainCheck_holds : chainCheck () = true := by
  unfold chainCheck
  dsimp only
  simp only [Bool.and_eq_true, decide_eq_true_eq, allLt_iff]
  refine ⟨by decide, fun k hk => ?_⟩
  obtain ⟨hc, hl⟩ := chain_lt k hk
  obtain ⟨e1, e2⟩ := ya550712_chain k hk
  rw [repsA_get (by omega), steps_eq _ _ _ _ hc hl, wordA_of _ _ _ (gX_of hc),
    genA_eq12 yfX_gens (by norm_num), e1]
  exact ⟨rfl, e2⟩

end CFSG.KD.YamakiAutM

end
