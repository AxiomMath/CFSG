module

public import Certificates.Kernel.HN1408.M11Facts
public import Certificates.Kernel.HN1408.FixRYIDefs
public import Certificates.Kernel.HN1408.FixRDefs

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.FixR

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

theorem repC_idK' : RepC idK 1 := ⟨cId, by rw [← idT_eq]; exact Rep.idT (by norm_num)⟩

theorem repC_of_pt' {X : Nat} {g : Equiv.Perm (Fin 1408)} (hX : Cn X)
    (h : ∀ x (hx : x < 1408), pt X x = (g ⟨x, hx⟩).val) : RepC X g :=
  ⟨hX, fun x hx => by rw [ap_eq hX hx, h x hx, idx_of_lt g hx, Equiv.Perm.smul_def]⟩

theorem elemW_reverse : ∀ w : List Nat, lettersOK w = true → elemW w.reverse = (elemW w)⁻¹
  | [], _ => by
    have h := elemW_append [] []
    rw [List.nil_append] at h
    have h1 : elemW ([] : List Nat) = 1 := by
      calc elemW ([] : List Nat) = (elemW [])⁻¹ * (elemW [] * elemW []) := by group
        _ = (elemW [])⁻¹ * elemW [] := by rw [← h]
        _ = 1 := inv_mul_cancel _
    rw [List.reverse_nil, h1, inv_one]
  | a :: w, h => by
    simp only [lettersOK, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h7⟩, hw⟩ := h
    have ih := elemW_reverse w hw
    have e1 : elemW (a :: w) = elemW [a] * elemW w := by
      rw [← elemW_append]
      rfl
    have ha : [a] = [(a - 1) + 1] := by
      congr 1
      omega
    rw [List.reverse_cons, elemW_append, ih, e1, mul_inv_rev, ha, gen_inv (by omega)]

theorem gHead_parts {ws : List (List Nat)} {G GI : Nat → Nat}
    (hl : ∀ j < ws.length, lettersOK (ws.getD j []) = true) (h : gHeadF ws G GI = true) :
    ∀ j < ws.length, ∃ g ∈ P1408, RepC (G j) g ∧ RepC (GI j) g⁻¹ := by
  intro j hj
  have h1 := allN_spec h j hj
  obtain ⟨a, b⟩ := mkA h1
  have hw := hl j hj
  have hr : lettersOK (ws.getD j []).reverse = true := by
    simp only [lettersOK, List.all_reverse] at hw ⊢
    exact hw
  refine ⟨elemW (ws.getD j []), elemW_mem _, ?_, ?_⟩
  · rw [Nat.eq_of_beq_eq_true a]
    exact repC_word hw
  · rw [Nat.eq_of_beq_eq_true b, ← elemW_reverse _ hw]
    exact repC_word hr

theorem yTree_parts {yws : List (List Nat)} {YG Y YI YP : Nat → Nat} {nY : Nat}
    (hl : ∀ l < yws.length, lettersOK (yws.getD l []) = true) (hg : yGenF yws YG = true)
    (h : yTreeF YG Y YI YP yws.length nY = true) (hi : yInvF Y YI nY = true) :
    ∀ k < nY, ∃ y ∈ P1408, RepC (Y k) y ∧ RepC (YI k) y⁻¹ ∧
      y ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩ := by
  unfold yTreeF at h
  obtain ⟨h0, hall⟩ := mkA h
  have hmem : ∀ k < nY, ∃ y ∈ P1408, RepC (Y k) y := by
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
        obtain ⟨y, hyP, hy⟩ := ih _ hp' (by omega)
        have hG : RepC (YG (f16 (YP k) 1)) (elemW (yws.getD (f16 (YP k) 1) [])) := by
          rw [Nat.eq_of_beq_eq_true (allN_spec hg _ hl'')]
          exact repC_word (hl _ hl'')
        refine ⟨elemW (yws.getD (f16 (YP k) 1) []) * y, mul_mem (elemW_mem _) hyP, ?_⟩
        rw [Nat.eq_of_beq_eq_true he]
        exact repC_pc hG hy
  intro k hk
  obtain ⟨y, hyP, hy⟩ := hmem k hk
  have hk' := allN_spec hall k hk
  simp only [strictB_app] at hk'
  obtain ⟨hfix, -⟩ := mkA hk'
  have hk2 := allN_spec hi k hk
  simp only [strictB_app] at hk2
  obtain ⟨hc, he⟩ := mkA hk2
  refine ⟨y, hyP, hy, repC_of_pt' hc fun x hx => ?_, Fin.ext ?_⟩
  · have hb : pt (YI k) x < 1408 := pt_lt hc hx
    have e1 : pt (Y k) (pt (YI k) x) = x := by
      rw [← pt_pc hy.1 hx, Nat.eq_of_beq_eq_true he, repC_pt repC_idK' hx]
      rfl
    rw [repC_pt hy hb] at e1
    have e2 : y ⟨pt (YI k) x, hb⟩ = ⟨x, hx⟩ := Fin.ext e1
    rw [← e2]
    simp
  · rw [← repC_pt hy (by norm_num)]
    exact Nat.eq_of_beq_eq_true hfix

theorem repF_parts {G GI Y YI R P : Nat → Nat} {nG nY i : Nat}
    (h : repF G GI Y YI R P nG nY i = true) :
    ∃ p k j, p < i ∧ k < nY ∧ j < nG ∧ pt (R i) 0 = 0 ∧
      (R i = pc (pc (G j) (R p)) (GI j) ∨ R i = pc (pc (G j) (cyF Y YI k (R p))) (GI j)) := by
  unfold repF at h
  simp only [strictB_app] at h
  obtain ⟨a, h⟩ := mkA h
  obtain ⟨b, h⟩ := mkA h
  obtain ⟨c, h⟩ := mkA h
  obtain ⟨d, h⟩ := mkA h
  refine ⟨_, _, _, Nat.blt_eq.mp a, Nat.blt_eq.mp b, Nat.blt_eq.mp c, Nat.eq_of_beq_eq_true d, ?_⟩
  rcases mkIf h with ⟨-, h⟩ | ⟨-, h⟩
  · exact Or.inl (Nat.eq_of_beq_eq_true h)
  · exact Or.inr (Nat.eq_of_beq_eq_true h)

theorem reps_memF {G GI Y YI R P : Nat → Nat} {nG nY n : Nat} {x : Equiv.Perm (Fin 1408)}
    (hG : ∀ j < nG, ∃ g ∈ P1408, RepC (G j) g ∧ RepC (GI j) g⁻¹)
    (hY : ∀ k < nY, ∃ y ∈ P1408, RepC (Y k) y ∧ RepC (YI k) y⁻¹ ∧
      y ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩)
    (h0 : RepC (R 0) x) (hx0 : x ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩)
    (hr : ∀ i < n, 0 < i → repF G GI Y YI R P nG nY i = true) :
    ∀ i < n, ∃ c ∈ P1408, RepC (R i) (c * x * c⁻¹) ∧
      (c * x * c⁻¹) ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩ := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact ⟨1, one_mem _, by simpa using h0, by simpa using hx0⟩
    · obtain ⟨p, k, j, hp, hk, hj, hR0, e | e⟩ := repF_parts (hr i hi hpos)
      · obtain ⟨c, hcP, hc, -⟩ := ih p hp (by omega)
        obtain ⟨g, hgP, hgR, hgiR⟩ := hG j hj
        have hR := repC_pc (repC_pc hgR hc) hgiR
        rw [← e] at hR
        have e2 : g * (c * x * c⁻¹) * g⁻¹ = (g * c) * x * (g * c)⁻¹ := by group
        rw [e2] at hR
        refine ⟨g * c, mul_mem hgP hcP, hR, Fin.ext ?_⟩
        rw [← repC_pt hR (by norm_num), hR0]
      · obtain ⟨c, hcP, hc, -⟩ := ih p hp (by omega)
        obtain ⟨g, hgP, hgR, hgiR⟩ := hG j hj
        obtain ⟨y, hyP, hyR, hyiR, -⟩ := hY k hk
        have hR := repC_pc (repC_pc hgR (repC_pc (repC_pc hyR hc) hyiR)) hgiR
        unfold cyF at e
        rw [← e] at hR
        have e2 : g * (y * (c * x * c⁻¹) * y⁻¹) * g⁻¹ = (g * y * c) * x * (g * y * c)⁻¹ := by
          group
        rw [e2] at hR
        refine ⟨g * y * c, mul_mem (mul_mem hgP hyP) hcP, hR, Fin.ext ?_⟩
        rw [← repC_pt hR (by norm_num), hR0]

theorem fx_strictN_app (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

@[expose] def keyQ (g : Equiv.Perm (Fin 1408)) : Nat :=
  (g ⟨1, by norm_num⟩).val + 2048 * (g ⟨2, by norm_num⟩).val +
    4194304 * (g ⟨3, by norm_num⟩).val + 8589934592 * (g ⟨4, by norm_num⟩).val

theorem keyF_eq {Y YI : Nat → Nat} {X k : Nat} {g y : Equiv.Perm (Fin 1408)} (hX : RepC X g)
    (hy : RepC (Y k) y) (hyi : RepC (YI k) y⁻¹) : keyF Y YI X k = keyQ (y * g * y⁻¹) := by
  have hC := repC_pc (repC_pc hy hX) hyi
  have hp : ∀ x (hx : x < 1408), pt (Y k) (pt X (pt (YI k) x)) = ((y * g * y⁻¹) ⟨x, hx⟩).val := by
    intro x hx
    rw [← repC_pt hC hx, pt_pc (X := pc (Y k) X) (canonK_pcomp hy.1 hX.1) hx,
      pt_pc hy.1 (pt_lt hyi.1 hx)]
  unfold keyF keyQ
  simp only [fx_strictN_app]
  rw [hp 1 (by norm_num), hp 2 (by norm_num), hp 3 (by norm_num), hp 4 (by norm_num)]
  simp only [Nat.add_eq, Nat.mul_eq]
  omega

theorem count_geF {Y YI R S : Nat → Nat} {nY n cnt : Nat} {x : Equiv.Perm (Fin 1408)}
    (hY : ∀ k < nY, ∃ y ∈ P1408, RepC (Y k) y ∧ RepC (YI k) y⁻¹ ∧
      y ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩)
    (hreps : ∀ i < n, ∃ c ∈ P1408, RepC (R i) (c * x * c⁻¹) ∧
      (c * x * c⁻¹) ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩)
    (hs : ∀ m < cnt, sortFAt Y YI R S nY n cnt m = true) :
    ∃ M : Finset (Equiv.Perm (Fin 1408)), M.card = cnt ∧
      ∀ z ∈ M, z ∈ conjClass P1408 x ∧ z ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩ := by
  classical
  have HR : ∀ i, ∃ r : Equiv.Perm (Fin 1408), i < n → (∃ c ∈ P1408, r = c * x * c⁻¹) ∧
      RepC (R i) r ∧ r ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩ := by
    intro i
    by_cases hi : i < n
    · obtain ⟨c, hcP, hcR, hc0⟩ := hreps i hi
      exact ⟨_, fun _ => ⟨⟨c, hcP, rfl⟩, hcR, hc0⟩⟩
    · exact ⟨1, fun h => absurd h hi⟩
  choose r hr using HR
  have HY : ∀ k, ∃ y : Equiv.Perm (Fin 1408), k < nY → y ∈ P1408 ∧ RepC (Y k) y ∧
      RepC (YI k) y⁻¹ ∧ y ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩ := by
    intro k
    by_cases hk : k < nY
    · obtain ⟨y, h1, h2, h3, h4⟩ := hY k hk
      exact ⟨y, fun _ => ⟨h1, h2, h3, h4⟩⟩
    · exact ⟨1, fun h => absurd h hk⟩
  choose yy hyy using HY
  have hS : ∀ m < cnt, f16 (S m) 0 < n ∧ f16 (S m) 1 < nY := by
    intro m hm
    have h1 := hs m hm
    unfold sortFAt at h1
    simp only [strictB_app] at h1
    obtain ⟨a, h1⟩ := mkA h1
    obtain ⟨b, -⟩ := mkA h1
    exact ⟨Nat.blt_eq.mp a, Nat.blt_eq.mp b⟩
  let e : Nat → Equiv.Perm (Fin 1408) := fun m =>
    yy (f16 (S m) 1) * r (f16 (S m) 0) * (yy (f16 (S m) 1))⁻¹
  have hkey : ∀ m < cnt, keyF Y YI (R (f16 (S m) 0)) (f16 (S m) 1) = keyQ (e m) := by
    intro m hm
    obtain ⟨-, hy, hyi, -⟩ := hyy _ (hS m hm).2
    exact keyF_eq (hr _ (hS m hm).1).2.1 hy hyi
  have hsucc : ∀ m, m + 1 < cnt → keyQ (e m) < keyQ (e (m + 1)) := by
    intro m hm
    have h1 := hs m (by omega)
    unfold sortFAt at h1
    simp only [strictB_app] at h1
    obtain ⟨-, h1⟩ := mkA h1
    obtain ⟨-, h1⟩ := mkA h1
    have e1 : Nat.blt (m + 1) cnt = true := Nat.blt_eq.mpr hm
    rw [e1] at h1
    rw [← hkey m (by omega), ← hkey (m + 1) hm]
    exact Nat.blt_eq.mp h1
  have hmono : ∀ m m', m < m' → m' < cnt → keyQ (e m) < keyQ (e m') := by
    intro m m' hlt hm'
    induction m' with
    | zero => omega
    | succ m' ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with h' | h'
      · exact (ih h' (by omega)).trans (hsucc m' hm')
      · rw [h']
        exact hsucc m' hm'
  have hinj : Set.InjOn e ↑(Finset.range cnt) := by
    intro m hm m' hm' hee
    have hm1 : m < cnt := Finset.mem_range.1 hm
    have hm2 : m' < cnt := Finset.mem_range.1 hm'
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have h1 := hmono m m' hlt hm2
      rw [hee] at h1
      exact lt_irrefl _ h1
    · have h1 := hmono m' m hlt hm1
      rw [hee] at h1
      exact lt_irrefl _ h1
  refine ⟨(Finset.range cnt).image e, by rw [Finset.card_image_of_injOn hinj, Finset.card_range],
    fun z hz => ?_⟩
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hz
  have hm1 : m < cnt := Finset.mem_range.1 hm
  obtain ⟨⟨c, hcP, hcr⟩, -, hr0⟩ := hr _ (hS m hm1).1
  obtain ⟨hyP, -, -, hy0⟩ := hyy _ (hS m hm1).2
  refine ⟨⟨yy (f16 (S m) 1) * c, mul_mem hyP hcP, ?_⟩, ?_⟩
  · dsimp only [e]
    rw [hcr]
    group
  · dsimp only [e]
    have hyi0 : (yy (f16 (S m) 1))⁻¹ ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩ := by
      rw [Equiv.Perm.inv_eq_iff_eq, hy0]
    simp only [Equiv.Perm.mul_apply, hyi0, hr0, hy0]

end CFSG.KD.HN1408.FixR

end
