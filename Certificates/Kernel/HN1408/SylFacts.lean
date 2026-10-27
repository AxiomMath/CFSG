module

public import Certificates.Kernel.HN1408.FixRGlue
public import Certificates.Kernel.HN1408.SylChk
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.FixPrime
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.FixFacts

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.FixR

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.KD.HN1408.Tr2 (genC)

theorem tree_closure {yws : List (List Nat)} {YG Y YI YP : Nat → Nat} {nY : Nat}
    (hl : ∀ l < yws.length, lettersOK (yws.getD l []) = true) (hg : yGenF yws YG = true)
    (h : yTreeF YG Y YI YP yws.length nY = true) :
    ∀ k < nY, ∃ y ∈ genC yws, RepC (Y k) y := by
  unfold yTreeF at h
  obtain ⟨h0, hall⟩ := mkA h
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have hk' := allN_spec hall k hk
    simp only [strictB_app] at hk'
    obtain ⟨-, hk'⟩ := mkA hk'
    obtain ⟨-, hk'⟩ := mkA hk'
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact ⟨1, one_mem _, by rw [Nat.eq_of_beq_eq_true h0]; exact repC_idK'⟩
    · rcases mkIf hk' with ⟨hc0, -⟩ | ⟨-, hk'⟩
      · exact absurd (Nat.eq_of_beq_eq_true hc0) (by omega)
      obtain ⟨hp, hk'⟩ := mkA hk'
      obtain ⟨hl', he⟩ := mkA hk'
      have hp' := Nat.blt_eq.mp hp
      have hl'' := Nat.blt_eq.mp hl'
      obtain ⟨y, hyS, hy⟩ := ih _ hp' (by omega)
      have hG : RepC (YG (f16 (YP k) 1)) (elemW (yws.getD (f16 (YP k) 1) [])) := by
        rw [Nat.eq_of_beq_eq_true (allN_spec hg _ hl'')]
        exact repC_word (hl _ hl'')
      refine ⟨elemW (yws.getD (f16 (YP k) 1) []) * y, mul_mem (Tr2.gen_mem hl'') hyS, ?_⟩
      rw [Nat.eq_of_beq_eq_true he]
      exact repC_pc hG hy

theorem keyS_eq {X : Nat} {g : Equiv.Perm (Fin 1408)} (hX : RepC X g) : keyS X = keyQ g := by
  unfold keyS keyQ
  rw [repC_pt hX (by norm_num : 1 < 1408), repC_pt hX (by norm_num : 2 < 1408),
    repC_pt hX (by norm_num : 3 < 1408), repC_pt hX (by norm_num : 4 < 1408)]
  simp only [Nat.add_eq, Nat.mul_eq]
  omega

theorem sub_spec {yws : List (List Nat)} {YG Y YI YP C D : Nat → Nat} {nY : Nat}
    (hl : ∀ l < yws.length, lettersOK (yws.getD l []) = true) (hg : yGenF yws YG = true)
    (ht : yTreeF YG Y YI YP yws.length nY = true) (hc : closF YG Y C yws.length nY = true)
    (hd : distF Y D nY = true) (hn : 0 < nY) :
    Nat.card (genC yws) = nY ∧ ∀ g ∈ genC yws, ∃ k < nY, RepC (Y k) g := by
  classical
  have hmem := tree_closure hl hg ht
  unfold closF at hc
  have hstep : ∀ l < yws.length, ∀ g : Equiv.Perm (Fin 1408), (∃ k < nY, RepC (Y k) g) →
      ∃ k < nY, RepC (Y k) (elemW (yws.getD l []) * g) := by
    rintro l hl' g ⟨k, hk, hkg⟩
    have h1 := allN_spec (allN_spec hc k hk) l hl'
    simp only [strictB_app] at h1
    obtain ⟨a, b⟩ := mkA h1
    refine ⟨_, Nat.blt_eq.mp a, ?_⟩
    rw [← Nat.eq_of_beq_eq_true b]
    have hG : RepC (YG l) (elemW (yws.getD l [])) := by
      rw [Nat.eq_of_beq_eq_true (allN_spec hg l hl')]
      exact repC_word (hl l hl')
    exact repC_pc hG hkg
  have hgen : ∀ s ∈ elemW '' {w | w ∈ yws}, ∀ g : Equiv.Perm (Fin 1408),
      (∃ k < nY, RepC (Y k) g) → ∃ k < nY, RepC (Y k) (s * g) := by
    rintro _ ⟨w, hw, rfl⟩ g hQ
    have hw' : w ∈ yws := hw
    obtain ⟨l, hl', e⟩ := List.getElem_of_mem hw'
    have e2 : yws.getD l [] = w := by rw [List.getD_eq_getElem _ _ hl', e]
    rw [← e2]
    exact hstep l hl' g hQ
  have hpow : ∀ s ∈ elemW '' {w | w ∈ yws}, ∀ j : Nat, ∀ g : Equiv.Perm (Fin 1408),
      (∃ k < nY, RepC (Y k) g) → ∃ k < nY, RepC (Y k) (s ^ j * g) := by
    intro s hs j
    induction j with
    | zero =>
      intro g hQ
      rwa [pow_zero, one_mul]
    | succ j ih =>
      intro g hQ
      rw [pow_succ', mul_assoc]
      exact hgen s hs _ (ih g hQ)
  have hQ1 : ∃ k < nY, RepC (Y k) (1 : Equiv.Perm (Fin 1408)) := by
    unfold yTreeF at ht
    obtain ⟨h0, -⟩ := mkA ht
    exact ⟨0, hn, by rw [Nat.eq_of_beq_eq_true h0]; exact repC_idK'⟩
  have hall : ∀ g ∈ genC yws, ∃ k < nY, RepC (Y k) g := by
    intro g hg'
    induction hg' using Subgroup.closure_induction_left with
    | one => exact hQ1
    | mul_left a ha g _ ih => exact hgen a ha g ih
    | inv_mul_cancel a ha g _ ih =>
      have h1 : a ^ (orderOf a - 1) * a = 1 := by
        rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos a), pow_orderOf_eq_one]
      rw [← eq_inv_of_mul_eq_one_left h1]
      exact hpow a ha _ g ih
  refine ⟨?_, hall⟩
  have HY : ∀ k, ∃ y : Equiv.Perm (Fin 1408), k < nY → y ∈ genC yws ∧ RepC (Y k) y := by
    intro k
    by_cases hk : k < nY
    · obtain ⟨y, h1, h2⟩ := hmem k hk
      exact ⟨y, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨1, fun h => absurd h hk⟩
  choose yy hyy using HY
  unfold distF at hd
  have hD : ∀ m < nY, f16 (D m) 0 < nY := by
    intro m hm
    have h1 := allN_spec hd m hm
    simp only [strictB_app] at h1
    exact Nat.blt_eq.mp (mkA h1).1
  let e : Nat → Equiv.Perm (Fin 1408) := fun m => yy (f16 (D m) 0)
  have hsucc : ∀ m, m + 1 < nY → keyQ (e m) < keyQ (e (m + 1)) := by
    intro m hm
    have h1 := allN_spec hd m (by omega)
    simp only [strictB_app] at h1
    obtain ⟨-, h1⟩ := mkA h1
    rw [Nat.blt_eq.mpr hm] at h1
    dsimp only [e]
    rw [← keyS_eq (hyy _ (hD m (by omega))).2, ← keyS_eq (hyy _ (hD (m + 1) hm)).2]
    exact Nat.blt_eq.mp h1
  have hmono : ∀ m m', m < m' → m' < nY → keyQ (e m) < keyQ (e m') := by
    intro m m' hlt hm'
    induction m' with
    | zero => omega
    | succ m' ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with h' | h'
      · exact (ih h' (by omega)).trans (hsucc m' hm')
      · rw [h']
        exact hsucc m' hm'
  have hinj : Set.InjOn e ↑(Finset.range nY) := by
    intro m hm m' hm' hee
    have hm1 : m < nY := Finset.mem_range.1 hm
    have hm2 : m' < nY := Finset.mem_range.1 hm'
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have h1 := hmono m m' hlt hm2
      rw [hee] at h1
      exact lt_irrefl _ h1
    · have h1 := hmono m' m hlt hm1
      rw [hee] at h1
      exact lt_irrefl _ h1
  have hc' : Nat.card (genC yws) = (genC yws : Set (Equiv.Perm (Fin 1408))).ncard :=
    Nat.card_coe_set_eq _
  rw [hc']
  apply le_antisymm
  · have hsub : (genC yws : Set (Equiv.Perm (Fin 1408))) ⊆ ↑((Finset.range nY).image yy) := by
      intro g hg'
      obtain ⟨k, hk, hkg⟩ := hall g hg'
      rw [Finset.coe_image]
      exact ⟨k, Finset.mem_range.2 hk, eq_of_repC (hyy k hk).2 hkg⟩
    calc (genC yws : Set (Equiv.Perm (Fin 1408))).ncard
        ≤ (↑((Finset.range nY).image yy) : Set (Equiv.Perm (Fin 1408))).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = ((Finset.range nY).image yy).card := Set.ncard_coe_finset _
      _ ≤ (Finset.range nY).card := Finset.card_image_le
      _ = nY := Finset.card_range nY
  · have hsub : (↑((Finset.range nY).image e) : Set (Equiv.Perm (Fin 1408))) ⊆
        (genC yws : Set (Equiv.Perm (Fin 1408))) := by
      intro g hg'
      rw [Finset.coe_image] at hg'
      obtain ⟨m, hm, rfl⟩ := hg'
      exact (hyy _ (hD m (Finset.mem_range.1 hm))).1
    calc nY = ((Finset.range nY).image e).card := by
          rw [Finset.card_image_of_injOn hinj, Finset.card_range]
      _ = (↑((Finset.range nY).image e) : Set (Equiv.Perm (Fin 1408))).ncard :=
          (Set.ncard_coe_finset _).symm
      _ ≤ (genC yws : Set (Equiv.Perm (Fin 1408))).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)

theorem cov_spec {Y W : Nat → Nat} {nY : Nat} {wit : Nat → Nat → Nat → Nat → Bool}
    {Q : Equiv.Perm (Fin 1408) → Prop}
    (hw : ∀ c X i j, wit c X i j = true → ∀ g, RepC X g → Q g) (h : covF Y W nY wit = true) :
    ∀ k < nY, 0 < k → ∀ g, RepC (Y k) g → Q g := by
  intro k hk hpos g hg
  unfold covF at h
  have h1 := allN_spec h k hk
  rcases mkIf h1 with ⟨hc0, -⟩ | ⟨-, h1⟩
  · exact absurd (Nat.eq_of_beq_eq_true hc0) (by omega)
  simp only [strictB_app] at h1
  exact hw _ _ _ _ h1 g hg

theorem witF_spec {Y YI R : Nat → Nat} {w : List Nat} {fix nY n cnt X i j : Nat}
    (hrec : RecFacts w fix nY n cnt Y YI R) (h : witF Y YI R nY n X i j = true) :
    ∀ g, RepC X g → g ∈ conjClass P1408 (elemW w) := by
  unfold witF at h
  obtain ⟨a, h⟩ := mkA h
  obtain ⟨b, c⟩ := mkA h
  intro g hg
  rw [Nat.eq_of_beq_eq_true c] at hg
  exact hrec.2.2 i (Nat.blt_eq.mp a) j (Nat.blt_eq.mp b) g hg

theorem factorization_eq_of_decomp {p k m N : ℕ} (hp : p.Prime) (hN : N = p ^ k * m)
    (hm : ¬ p ∣ m) : N.factorization p = k := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero p)
  rw [hN, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hm0, Finsupp.add_apply,
    hp.factorization_pow, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hm,
    add_zero]

theorem syl_facts {p : Nat} [Fact p.Prime] {ds : List FixData} {yws : List (List Nat)}
    {YG Y YI YP C D W : Nat → Nat} {nY : Nat} {wit : Nat → Nat → Nat → Nat → Bool}
    (hP : Nat.card ↥P1408 = 177408000) (hcent : ∀ d ∈ ds, CentFacts d)
    (hl : ∀ l < yws.length, lettersOK (yws.getD l []) = true) (hg : yGenF yws YG = true)
    (ht : yTreeF YG Y YI YP yws.length nY = true) (hc : closF YG Y C yws.length nY = true)
    (hd : distF Y D nY = true) (hn : 0 < nY)
    (hnY : nY = p ^ (177408000 : Nat).factorization p)
    (hw : ∀ c X i j, wit c X i j = true → ∀ g, RepC X g →
      ∃ d ∈ ds, g ∈ conjClass P1408 (elemW d.rep))
    (hcov : covF Y W nY wit = true) : PrimeFacts p ds := by
  obtain ⟨hcard, hall⟩ := sub_spec hl hg ht hc hd hn
  have hY0 : RepC (Y 0) 1 := by
    unfold yTreeF at ht
    rw [Nat.eq_of_beq_eq_true (mkA ht).1]
    exact repC_idK'
  refine ⟨fun d hd => hcent d hd, fun t ht' => isConj_of_fixPrimeOK (sw := yws) ?_ ?_ ht'⟩
  · rw [hP]
    exact hcard.trans hnY
  · intro y hy
    obtain ⟨k, hk, hky⟩ := hall y hy
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact Or.inl (eq_of_repC hky hY0)
    · exact Or.inr (cov_spec hw hcov k hk hpos y hky)

theorem syl3_letters : ∀ l < sylow3Words.length, lettersOK (sylow3Words.getD l []) = true := by
  intro l hl
  have hl' : l < 2 := hl
  interval_cases l <;> decide

theorem syl7_letters : ∀ l < sylow7Words.length, lettersOK (sylow7Words.getD l []) = true := by
  intro l hl
  have hl' : l < 1 := hl
  interval_cases l
  decide

theorem prime3 (hP : Nat.card ↥P1408 = 177408000) : PrimeFacts 3 [fix3] := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine syl_facts (yws := sylow3Words) (W := Syl3.W) (wit := wit3) hP
    (fun d hd => by
      rw [List.mem_singleton] at hd
      rw [hd]
      exact cent3_facts hP)
    syl3_letters s3_gen s3_tree s3_clos s3_dist (by norm_num) ?_
    (fun c X i j h g hg => ⟨fix3, List.mem_singleton_self _,
      witF_spec rec3 (by unfold wit3 at h; exact h) g hg⟩) s3_cov
  rw [factorization_eq_of_decomp (k := 2) (m := 19712000) Nat.prime_three (by norm_num)
    (by norm_num)]
  norm_num

theorem prime7 (hP : Nat.card ↥P1408 = 177408000) : PrimeFacts 7 [fix7] := by
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  refine syl_facts (yws := sylow7Words) (W := Syl7.W) (wit := wit7) hP
    (fun d hd => by
      rw [List.mem_singleton] at hd
      rw [hd]
      exact cent7_facts hP)
    syl7_letters s7_gen s7_tree s7_clos s7_dist (by norm_num) ?_
    (fun c X i j h g hg => ⟨fix7, List.mem_singleton_self _,
      witF_spec rec7 (by unfold wit7 at h; exact h) g hg⟩) s7_cov
  rw [factorization_eq_of_decomp (k := 1) (m := 25344000) Nat.prime_seven (by norm_num)
    (by norm_num)]
  norm_num

theorem headF_parts {ws yws : List (List Nat)} {w : List Nat} {fix nY : Nat}
    {G GI YG Y YI YP R : Nat → Nat} (h : headF ws yws w fix nY G GI YG Y YI YP R = true) :
    yGenF yws YG = true ∧ yTreeF YG Y YI YP yws.length nY = true := by
  unfold headF at h
  obtain ⟨-, h⟩ := mkA h
  obtain ⟨hg, h⟩ := mkA h
  exact ⟨hg, (mkA h).1⟩

theorem prime5 (hP : Nat.card ↥P1408 = 177408000) : PrimeFacts 5 [fix5A, fix5B, fix5C] := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hh : headF cw7 sylow5Words fix7.rep fix7.fix 125 Fix7.G Fix7.GI Fix7.YG Fix7.Y Fix7.YI
      Fix7.YP Fix7.R = true := f7_head
  obtain ⟨hyg, hyt⟩ := headF_parts hh
  refine syl_facts (yws := sylow5Words) (W := Syl5.W) (wit := wit5) hP
    (fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl
      · exact cent5a_facts hP
      · exact cent5b_facts hP
      · exact cent5c_facts hP)
    syl5_letters hyg hyt s5_clos s5_dist (by norm_num) ?_
    (fun c X i j h g hg => by
      unfold wit5 at h
      rcases mkIf h with ⟨-, h⟩ | ⟨-, h⟩
      · exact ⟨fix5A, by simp, witF_spec rec5a h g hg⟩
      rcases mkIf h with ⟨-, h⟩ | ⟨-, h⟩
      · exact ⟨fix5B, by simp, witF_spec rec5b h g hg⟩
      · exact ⟨fix5C, by simp, witF_spec rec5c h g hg⟩) s5_cov
  rw [factorization_eq_of_decomp (k := 3) (m := 1419264) Nat.prime_five (by norm_num)
    (by norm_num)]
  norm_num

theorem fix_facts : FixFacts where
  trans := Trans.trans_K
  p3 := prime3
  p5 := prime5
  p7 := prime7

end CFSG.KD.HN1408.FixR

end
