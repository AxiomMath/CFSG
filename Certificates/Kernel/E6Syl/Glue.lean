
module

public import Certificates.Kernel.E6Syl.Check
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6WeylFixBase
public import CFSG.Certificates.Kernel.WordsSSound

public section

namespace Certificates.Kernel.E6Syl

open CFSG.HardMathSupport.Timmesfeld.Tables.T1b CFSG.AGLEmbedding.R3

theorem forceN_eq {β : Sort _} (y : ℕ) (k : ℕ → β) : forceN y k = k y := by
  cases y <;> rfl

theorem forceL_eq {β : Sort _} : ∀ (l : List ℕ) (k : List ℕ → β), forceL l k = k l
  | [], _ => rfl
  | x :: l, k => by rw [forceL, forceN_eq, forceL_eq]

theorem forceLL_eq {β : Sort _} : ∀ (L : List (List ℕ)) (k : List (List ℕ) → β), forceLL L k = k L
  | [], _ => rfl
  | l :: L, k => by rw [forceLL, forceL_eq, forceLL_eq]

theorem map_getD_eq {A : List ℕ} {n : ℕ} (h : A.length = n) : (List.range n).map (A.getD · 0) = A := by
  subst h
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp [List.getD_eq_getElem?_getD, h2]

theorem mmulF_map (g h : ℕ → ℕ) :
    mmulF ((List.range 36).map g) ((List.range 36).map h) =
      mmulL 3 6 ((List.range 36).map g) ((List.range 36).map h) := by
  rw [mmulF, forceLL_eq]
  rfl

theorem mmulF_eq {A B : List ℕ} (hA : A.length = 36) (hB : B.length = 36) :
    mmulF A B = mmulL 3 6 A B := by
  have h := mmulF_map (A.getD · 0) (B.getD · 0)
  rwa [map_getD_eq hA, map_getD_eq hB] at h

theorem matVecR_map (g h : ℕ → ℕ) :
    matVecR (rows6 ((List.range 36).map g)) ((List.range 6).map h) =
      matVecA6 ((List.range 36).map g).toArray ((List.range 6).map h) := by
  rfl

theorem matVecR_eq {A v : List ℕ} (hA : A.length = 36) (hv : v.length = 6) :
    matVecR (rows6 A) v = matVecA6 A.toArray v := by
  have h := matVecR_map (A.getD · 0) (v.getD · 0)
  rwa [map_getD_eq hA, map_getD_eq hv] at h

theorem length_e6WordL (ω : List ℕ) : (e6WordL ω).length = 36 := by
  cases ω with
  | nil => exact length_midL 3 6
  | cons i ω => exact length_mmulL 3 6 _ _

theorem length_e6ReflL {i : ℕ} (hi : i < 6) : (e6ReflL.getD i []).length = 36 := by
  interval_cases i <;> rfl

theorem wordF_eq : ∀ ω : List ℕ, (∀ i ∈ ω, i < 6) → wordF ω = e6WordL ω
  | [], _ => rfl
  | i :: ω, h => by
    have ih := wordF_eq ω fun j hj => h j (List.mem_cons_of_mem _ hj)
    change mmulF (e6ReflL.getD i []) (wordF ω) = mmulL 3 6 (e6ReflL.getD i []) (e6WordL ω)
    rw [ih, mmulF_eq (length_e6ReflL (h i List.mem_cons_self)) (length_e6WordL ω)]

theorem gensF_eq : gensF = e6SylWords.map e6WordL :=
  List.map_congr_left fun ω hω => wordF_eq ω fun i hi => by
    revert i
    revert ω
    decide

theorem mpowF_eq {A : List ℕ} (hA : A.length = 36) : ∀ e : ℕ, mpowF A e = mpowL 3 6 A e
  | 0 => rfl
  | e + 1 => by
    rw [mpowF, mpowL, mpowF_eq hA e, mmulF_eq hA (length_mpowL 3 6 A e)]

theorem flatMap_congr_mem {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ x ∈ l, f x = g x) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h a List.mem_cons_self,
      ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem wordsF_eq : ∀ As : List (List ℕ), (∀ A ∈ As, A.length = 36) → wordsF As = wordsL 3 6 As
  | [], _ => rfl
  | A :: As, h => by
    have hA := h A List.mem_cons_self
    rw [wordsF, wordsL, wordsF_eq As fun B hB => h B (List.mem_cons_of_mem _ hB)]
    refine flatMap_congr_mem fun M hM => List.map_congr_left fun a _ => ?_
    rw [mpowF_eq hA, mmulF_eq (length_mpowL 3 6 A a) (wordsL_spec 3 6 (by norm_num) As M hM).1]

theorem wordsF_gensF : wordsF gensF = e6SylL () := by
  rw [gensF_eq, wordsF_eq _ fun A hA => ?_]
  · rfl
  · obtain ⟨ω, -, rfl⟩ := List.mem_map.1 hA
    exact length_e6WordL ω

theorem memN_iff (x : ℕ) : ∀ L : List ℕ, memN x L = true ↔ x ∈ L
  | [] => by simp [memN]
  | y :: L => by
    rw [memN, Bool.or_eq_true, Nat.beq_eq, memN_iff x L, List.mem_cons]

theorem isO3F_eq {A : List ℕ} (hA : A.length = 36) : isO3F (midL 3 6) A = isO3L A := by
  rw [isO3F, isO3L, mmulF_eq hA hA, mmulF_eq (length_mmulL 3 6 A A) hA]

theorem nfixR_eq {A : List ℕ} (hA : A.length = 36) :
    forceLL (rows6 A) (nfixR (allVecs 3 6)) = nfix6 A := by
  rw [forceLL_eq, nfixR, nfix6]
  congr 1
  refine List.filter_congr fun v hv => ?_
  rw [matVecR_eq hA ((mem_allVecs 3 6 v).1 hv).1]

theorem nfixesF_eq :
    nfixesF (allVecs 3 6) (midL 3 6) (e6SylL ()) = ((e6SylL ()).filter isO3L).map nfix6 := by
  rw [nfixesF, List.filter_congr fun A hA => isO3F_eq (e6SylL_spec A hA).1]
  refine List.map_congr_left fun A hA => nfixR_eq (e6SylL_spec A (List.mem_filter.1 hA).1).1

theorem mul_mem_of_gens
    (h : ∀ A ∈ e6SylWords.map e6WordL, ∀ B ∈ e6SylL (), mmulL 3 6 A B ∈ e6SylL ()) :
    ∀ A ∈ e6SylL (), ∀ B ∈ e6SylL (), mmulL 3 6 A B ∈ e6SylL () := by
  let T : Submonoid (Matrix (Fin 6) (Fin 6) (ZMod 3)) :=
    { carrier := {M | ∀ B ∈ e6SylL (), ∃ C ∈ e6SylL (), toMatL 3 6 C = M * toMatL 3 6 B}
      one_mem' := fun B hB => ⟨B, hB, (one_mul _).symm⟩
      mul_mem' := by
        intro M N hM hN B hB
        obtain ⟨C, hC, hCe⟩ := hN B hB
        obtain ⟨D, hD, hDe⟩ := hM C hC
        exact ⟨D, hD, by rw [hDe, hCe, mul_assoc]⟩ }
  intro A hA B hB
  have hT := toMatL_mem_of_mem_wordsL T _ (fun G hG B hB =>
    ⟨_, h G hG B hB, toMatL_mmulL 3 6 G B⟩) A hA B hB
  obtain ⟨C, hC, hCe⟩ := hT
  rw [← toMatL_mmulL] at hCe
  rwa [← toMatL_inj6 (e6SylL_spec C hC) (mmulL_spec A B) hCe]

theorem e6SylCheck_eq_true : e6SylCheck () = true := by
  have h := chk_ok
  rw [chk, forceLL_eq, forceLL_eq, forceL_eq, forceLL_eq, forceL_eq, wordsF_gensF] at h
  simp only [chkCore, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hlen, hnd⟩, hmul⟩, hnc⟩, hb⟩ := h
  have hgl : ∀ A ∈ gensF, A.length = 36 := fun A hA => by
    rw [gensF_eq] at hA
    obtain ⟨ω, -, rfl⟩ := List.mem_map.1 hA
    exact length_e6WordL ω
  have hgen : ∀ A ∈ e6SylWords.map e6WordL, ∀ B ∈ e6SylL (), mmulL 3 6 A B ∈ e6SylL () := by
    intro A hA B hB
    rw [← gensF_eq] at hA
    have hm := (memN_iff _ _).1 (hmul A hA B hB)
    obtain ⟨C, hC, hCe⟩ := List.mem_map.1 hm
    rw [mmulF_eq (hgl A hA) (e6SylL_spec B hB).1] at hCe
    rwa [CFSG.KS.WordsS.codeL_inj 3 C _ (by rw [(e6SylL_spec C hC).1, (mmulL_spec A B).1])
      (e6SylL_spec C hC).2 (mmulL_spec A B).2 hCe] at hC
  have hG : gensF = e6WordL (e6SylWords.getD 0 []) :: e6WordL (e6SylWords.getD 1 []) ::
      (e6SylWords.drop 2).map e6WordL := by
    rw [gensF_eq]
    rfl
  rw [hG, noncommF, bne_iff_ne, ne_eq, mmulF_eq (length_e6WordL _) (length_e6WordL _),
    mmulF_eq (length_e6WordL _) (length_e6WordL _)] at hnc
  rw [forceL_eq, nfixesF_eq, boundsF, Bool.and_eq_true, List.all_eq_true] at hb
  simp only [e6SylCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.contains_iff_mem, bne_iff_ne, ne_eq]
  refine ⟨⟨⟨⟨⟨hlen, ?_⟩, mul_mem_of_gens hgen⟩, hnc⟩, fun n hn => of_decide_eq_true (hb.1 n hn)⟩,
    of_decide_eq_true hb.2⟩
  refine CFSG.Decide.nodup_of_bitsetNodup (fun A => codeL 3 A % 100003) ?_
  rwa [List.map_map] at hnd

end Certificates.Kernel.E6Syl
