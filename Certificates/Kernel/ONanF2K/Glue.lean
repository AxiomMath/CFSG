module

public import Certificates.Data.ONanF2Quot
import Certificates.Kernel.ONanF2K.Check
import CFSG.Certificates.Kernel.ONanF2KSound

public section

namespace CFSG.KC.ONanF2K

open CFSG.OddStandard.ONanRec.F2 AlpE CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23

theorem bfs_mem_closure {G : Type*} [Group G] [DecidableEq G] (gens : List G) (M : Submonoid G)
    (hg : ∀ g ∈ gens, g ∈ M) :
    ∀ (n : ℕ) (vis fr : List G), (∀ x ∈ vis, x ∈ M) → (∀ x ∈ fr, x ∈ M) →
      ∀ x ∈ bfs gens n vis fr, x ∈ M
  | 0, vis, fr, hv, _ => by simpa [bfs] using hv
  | n + 1, vis, fr, hv, hf => by
    have hnew : ∀ y ∈ ((fr.flatMap fun x => gens.map (x * ·)).dedup.filter fun y => y ∉ vis),
        y ∈ M := by
      intro y hy
      rw [List.mem_filter, List.mem_dedup, List.mem_flatMap] at hy
      obtain ⟨⟨x, hx, hy⟩, _⟩ := hy
      rw [List.mem_map] at hy
      obtain ⟨g, hg', rfl⟩ := hy
      exact M.mul_mem (hf x hx) (hg g hg')
    simp only [bfs]
    split
    · exact hv
    · refine bfs_mem_closure gens M hg n _ _ ?_ hnew
      intro x hx
      rcases List.mem_append.1 hx with h | h
      · exact hv x h
      · exact hnew x h

theorem hom_of_gens {G H : Type*} [Group G] [Monoid H] (f : G → H) (L gens : List G)
    (hL : ∀ x ∈ L, ∀ g ∈ gens, x * g ∈ L) (hf : ∀ x ∈ L, ∀ g ∈ gens, f (x * g) = f x * f g)
    (h1 : f 1 = 1) (h1L : (1 : G) ∈ L) (hcl : ∀ b ∈ L, b ∈ Submonoid.closure {g | g ∈ gens}) :
    ∀ a ∈ L, ∀ b ∈ L, f (a * b) = f a * f b := by
  have key : ∀ b ∈ Submonoid.closure {g | g ∈ gens}, ∀ a ∈ L,
      a * b ∈ L ∧ f (a * b) = f a * f b := by
    intro b hb
    induction hb using Submonoid.closure_induction with
    | mem g hg => exact fun a ha => ⟨hL a ha g hg, hf a ha g hg⟩
    | one => exact fun a ha => ⟨by rwa [mul_one], by rw [mul_one, h1, mul_one]⟩
    | mul x y _ _ ihx ihy =>
      intro a ha
      obtain ⟨hax, hfx⟩ := ihx a ha
      obtain ⟨haxy, hfy⟩ := ihy (a * x) hax
      have hxL : x ∈ L := by simpa using (ihx 1 h1L).1
      have hxy := (ihy x hxL).2
      refine ⟨by rwa [← mul_assoc], ?_⟩
      rw [← mul_assoc, hfy, hfx, hxy, mul_assoc]
  exact fun a ha b hb => (key b (hcl b hb) a ha).2

theorem ballMaxL_one : ballMaxL.getD 1 [] = ballFix (genMaxE 1) := by
  have h : (List.finRange 7)[1]? = some 1 := by decide
  simp only [ballMaxL, List.getD_eq_getElem?_getD, List.getElem?_map, h, Option.map_some,
    Option.getD_some]

theorem factP0_holds : factP0 := by
  have hP0 : ballMaxL.getD 1 [] = (unpackL P0T 256).map decN := eq_of_beq p0_beq
  have hN : ballNE = (unpackL NT 4).map decN := eq_of_beq n_beq
  have hQ8 : ballQ8E = (unpackL Q8T 32).map decN := eq_of_beq q8_beq
  have hG : genMaxE 1 = gP0.map decN := eq_of_beq genMax1_beq
  have hel := elts_beq
  simp only [Bool.and_eq_true, beq_iff_eq] at hel
  obtain ⟨hx, hst⟩ := hel
  have hinv := decN_inv expK_true
  have hlt0 := unpackL_lt 256 P0T
  have hltN := unpackL_lt 4 NT
  have hltQ := unpackL_lt 32 Q8T
  have hltG : ∀ g ∈ gP0, g < 512 := by decide
  have hF : ∀ c, fE (decN c) = tcDec (lane fT (c % 512) 6) := by
    intro c
    rw [← decN_mod c]
    exact eq_of_beq (List.all_eq_true.1 fE_all (c % 512)
      (List.mem_range.2 (Nat.mod_lt _ (by norm_num))))
  have hclosed : ∀ x ∈ ballMaxL.getD 1 [], ∀ g ∈ genMaxE 1, x * g ∈ ballMaxL.getD 1 [] := by
    rw [hP0, hG]
    simp only [List.forall_mem_map]
    intro c hc g hg
    rw [decN_mul, mem_map_decN hlt0]
    simpa using List.all_eq_true.1 (List.all_eq_true.1 p0_closed c hc) g hg
  have hballP0 : ballMaxL.getD 1 [] = ballFix (genMaxE 1) := ballMaxL_one
  refine ⟨of_decide_eq_true (by decide +kernel), ⟨hballP0, ?_, ?_, hclosed⟩, ?_, ?_, ?_, ?_,
    by decide +kernel, of_decide_eq_true (by decide +kernel), of_decide_eq_true (by decide +kernel),
    of_decide_eq_true (by decide +kernel), ?_, of_decide_eq_true (by decide +kernel)⟩
  · rw [hP0, List.length_map, p0_len]
  · rw [hP0]
    refine p0_nodup.map_on fun a ha b hb h => ?_
    rwa [decN_eq_iff, Nat.mod_eq_of_lt (hlt0 a ha), Nat.mod_eq_of_lt (hlt0 b hb)] at h
  · intro g
    obtain ⟨c, hc, rfl⟩ := exists_decN g
    rw [hx, hN, decN_mul, hinv, decN_mul, mem_map_decN hltN]
    simpa using List.all_eq_true.1 p0_conjx c (List.mem_range.2 hc)
  · refine hom_of_gens fE _ _ hclosed ?_ ?_ ?_ ?_
    · rw [hP0, hG]
      simp only [List.forall_mem_map]
      intro c hc g hg
      rw [decN_mul, hF, hF, hF, Nat.mod_eq_of_lt (hlt0 c hc), Nat.mod_eq_of_lt (hltG g hg)]
      exact eq_of_beq (List.all_eq_true.1 (List.all_eq_true.1 p0_hom c hc) g hg)
    · rw [← decN_zero, hF]
      decide +kernel
    · rw [hP0, ← decN_zero, mem_map_decN hlt0]
      decide +kernel
    · intro b hb
      rw [hballP0] at hb
      refine bfs_mem_closure (genMaxE 1) _ (fun g hg => Submonoid.subset_closure hg) 64 [1] [1]
        ?_ ?_ b hb
      · intro x hx
        rw [List.mem_singleton.1 hx]
        exact Submonoid.one_mem _
      · intro x hx
        rw [List.mem_singleton.1 hx]
        exact Submonoid.one_mem _
  · rw [hP0]
    simp only [List.forall_mem_map]
    intro c hc
    rw [hF, hN, mem_map_decN hltN, Nat.mod_eq_of_lt (hlt0 c hc)]
    have h := List.all_eq_true.1 p0_ker c hc
    by_cases h1 : tcDec (lane fT c 6) = 1 <;> by_cases h2 : c ∈ unpackL NT 4 <;> simp_all
  · intro y
    obtain ⟨k, hk, rfl⟩ := tc_surj y
    obtain ⟨c, hc, hck⟩ := List.any_eq_true.1 (List.all_eq_true.1 p0_surj k hk)
    refine ⟨decN c, by rw [hP0]; exact List.mem_map_of_mem hc, ?_⟩
    rw [hF, Nat.mod_eq_of_lt (hlt0 c hc), Nat.eq_of_beq_eq_true hck]
  · rw [hP0]
    simp only [List.forall_mem_map]
    intro c hc
    rw [hst, hN, hQ8, decN_mul, hinv, decN_mul, decN_mul, mem_map_decN hltN, mem_map_decN hltQ,
      Nat.mod_eq_of_lt (hlt0 c hc)]
    simpa using List.all_eq_true.1 p0_q8 c hc

theorem factT_holds : factT := of_decide_eq_true factT_true

theorem f2QuotCheck_true : f2QuotCheck = true := by
  simp only [f2QuotCheck, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨factP0_holds, factT_holds⟩

end CFSG.KC.ONanF2K
