module

public import Certificates.Kernel.G23F48.A23Glue

public section

set_option maxRecDepth 400000

namespace CFSG.KC.G23F48

open CFSG.ASVolI CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KD.G23A22
open CFSG.Sporadic.HNOddCore (arrGen)
open MulAction

variable {X P R : Subgroup (Equiv.Perm (Fin 728))}

theorem exists_of_tree3 {a b c : ℕ} {σa σb σc : Equiv.Perm (Fin 728)}
    (ha : Orb.PRep 728 10 a σa) (hb : Orb.PRep 728 10 b σb) (hc : Orb.PRep 728 10 c σc)
    (haP : σa ∈ P) (hbP : σb ∈ P) (hcP : σc ∈ P) {r v : ℕ} {U : List (ℕ × ℕ × ℕ)}
    (hU : reachP 728 10 r [a, b, c] U = true) (hv : v ∈ U.map Prod.fst) :
    ∃ hr : r < 728, ∃ q ∈ P, ((q ⟨r, hr⟩ : Fin 728) : ℕ) = v := by
  have hr := (reachP_spec hU).2.1
  have hσ : ∀ s < [a, b, c].length, Orb.PRep 728 10 ([a, b, c].getD s 0)
      ([σa, σb, σc].getD s 1) ∧ [σa, σb, σc].getD s 1 ∈ P := by
    intro s hs
    have hs3 : s < 3 := hs
    interval_cases s
    exacts [⟨ha, haP⟩, ⟨hb, hbP⟩, ⟨hc, hcP⟩]
  obtain ⟨i, hi, he⟩ := mem_tree hv
  obtain ⟨q, hq, hqe⟩ := reach_of_reachP hσ hU hr i hi
  exact ⟨hr, q, hq, hqe.trans he⟩

theorem eq_of_tree4 {pt : ℕ} (hpt : pt + 364 ≤ 728) {a b c H : ℕ}
    {σa σb σc h : Equiv.Perm (Fin 728)}
    (ha : Orb.PRep 728 10 a σa) (hb : Orb.PRep 728 10 b σb) (hc : Orb.PRep 728 10 c σc)
    (hH : Orb.PRep 728 10 H h) (haP : σa ∈ P) (hbP : σb ∈ P) (hcP : σc ∈ P) (hhR : h ∈ R)
    {T : List (ℕ × ℕ × ℕ)} (hT : reachP 728 10 pt [a, b, c, H] T = true)
    (hC : coverP T pt 364 = true) (hPR : P ≤ R)
    (hPpt : P ≤ stabilizer (Equiv.Perm (Fin 728)) (⟨pt, by omega⟩ : Fin 728))
    (hcX : Nat.card X = 364 * Nat.card P) (hRX : R ≤ X) : R = X := by
  have hσ : ∀ s < [a, b, c, H].length, Orb.PRep 728 10 ([a, b, c, H].getD s 0)
      ([σa, σb, σc, h].getD s 1) ∧ [σa, σb, σc, h].getD s 1 ∈ R := by
    intro s hs
    have hs4 : s < 4 := hs
    interval_cases s
    exacts [⟨ha, hPR haP⟩, ⟨hb, hPR hbP⟩, ⟨hc, hPR hcP⟩, ⟨hH, hhR⟩]
  let f : Fin 364 → Fin 728 := fun x => ⟨pt + x, by omega⟩
  have hf : Function.Injective f := fun x y e => Fin.ext (by simpa [f] using congrArg Fin.val e)
  refine eq_of_orbit364 (Finset.univ.image f) (by rw [Finset.card_image_of_injective _ hf]; simp)
    ?_ hPR hPpt hcX hRX
  intro r hr
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hr
  obtain ⟨i, hi, he⟩ := mem_tree (coverP_mem hC x.2)
  obtain ⟨g, hg, hge⟩ := reach_of_reachP hσ hT (by omega) i hi
  exact ⟨g, hg, Fin.ext (by rw [hge, he])⟩

theorem max_of_trees {pt : ℕ} (hpt : pt + 364 ≤ 728) {a b c : ℕ}
    {σa σb σc : Equiv.Perm (Fin 728)}
    (ha : Orb.PRep 728 10 a σa) (hb : Orb.PRep 728 10 b σb) (hc : Orb.PRep 728 10 c σc)
    (haP : σa ∈ P) (hbP : σb ∈ P) (hcP : σc ∈ P) {r₀ r₁ r₂ : ℕ} {U₀ U₁ U₂ : List (ℕ × ℕ × ℕ)}
    (hU₀ : reachP 728 10 r₀ [a, b, c] U₀ = true) (hU₁ : reachP 728 10 r₁ [a, b, c] U₁ = true)
    (hU₂ : reachP 728 10 r₂ [a, b, c] U₂ = true) (hU : coverP (U₀ ++ U₁ ++ U₂) (pt + 1) 363 = true)
    {Hf : ℕ → ℕ} {hf : ℕ → Equiv.Perm (Fin 728)}
    (hH : ∀ j, Orb.PRep 728 10 (Hf j) (hf j) ∧ hf j ∈ X)
    (hv : [r₀, r₁, r₂] = (List.range 3).map fun j => pg 10 (mask 10) (Hf j) pt)
    {T₀ T₁ T₂ : List (ℕ × ℕ × ℕ)} (hT₀ : reachP 728 10 pt [a, b, c, Hf 0] T₀ = true)
    (hT₁ : reachP 728 10 pt [a, b, c, Hf 1] T₁ = true)
    (hT₂ : reachP 728 10 pt [a, b, c, Hf 2] T₂ = true)
    (hC₀ : coverP T₀ pt 364 = true) (hC₁ : coverP T₁ pt 364 = true)
    (hC₂ : coverP T₂ pt 364 = true)
    (hP : P = X ⊓ stabilizer (Equiv.Perm (Fin 728)) (⟨pt, by omega⟩ : Fin 728))
    (hcX : Nat.card X = 364 * Nat.card P)
    (hrange : ∀ g ∈ X, pt ≤ ((g ⟨pt, by omega⟩ : Fin 728) : ℕ) ∧
      ((g ⟨pt, by omega⟩ : Fin 728) : ℕ) < pt + 364)
    (hlt : P < R) (hRX : R ≤ X) : R = X := by
  set p : Fin 728 := ⟨pt, by omega⟩ with hp
  obtain ⟨g, hgR, hgP⟩ := SetLike.exists_of_lt hlt
  have hgX := hRX hgR
  have hgp : ((g p : Fin 728) : ℕ) ≠ pt := fun he => hgP (by
    rw [hP]
    exact ⟨hgX, mem_stabilizer_iff.2 (by rw [Equiv.Perm.smul_def]; exact Fin.ext he)⟩)
  have hPpt : P ≤ stabilizer (Equiv.Perm (Fin 728)) p := by
    rw [hP]
    exact inf_le_right
  obtain ⟨hr1, hr2⟩ := hrange g hgX
  have hmem := coverP_mem hU (q := (g p : ℕ) - (pt + 1)) (by omega)
  have ev : pt + 1 + ((g p : ℕ) - (pt + 1)) = (g p : ℕ) := by omega
  rw [ev, List.map_append, List.map_append, List.mem_append, List.mem_append] at hmem
  have er : List.range 3 = [0, 1, 2] := rfl
  rw [er] at hv
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hv
  obtain ⟨e₀, e₁, e₂⟩ := hv
  have fin : ∀ j < 3, ∀ (r : ℕ) (U T : List (ℕ × ℕ × ℕ)), r = pg 10 (mask 10) (Hf j) pt →
      reachP 728 10 r [a, b, c] U = true → (g p : ℕ) ∈ U.map Prod.fst →
      reachP 728 10 pt [a, b, c, Hf j] T = true → coverP T pt 364 = true → R = X := by
    intro j _ r U T er hUr hgU hTj hCj
    obtain ⟨hr, q, hq, hqe⟩ := exists_of_tree3 ha hb hc haP hbP hcP hUr hgU
    have hhp : hf j p = ⟨r, hr⟩ := Fin.ext (((hH j).1 p).symm.trans er.symm)
    have hhR : hf j ∈ R :=
      mem_of_fix hP hlt.le hgR hgX hq (hH j).2 (by rw [hhp]; exact Fin.ext hqe)
    exact eq_of_tree4 hpt ha hb hc (hH j).1 haP hbP hcP hhR hTj hCj hlt.le hPpt hcX hRX
  rcases hmem with (h | h) | h
  · exact fin 0 (by norm_num) r₀ U₀ T₀ e₀ hU₀ h hT₀ hC₀
  · exact fin 1 (by norm_num) r₁ U₁ T₁ e₁ hU₁ h hT₁ hC₁
  · exact fin 2 (by norm_num) r₂ U₂ T₂ e₂ hU₂ h hT₂ hC₂

theorem hw_rep (W : List (List (Fin 4 × Bool))) (j : ℕ) :
    Orb.PRep 728 10 (evP 728 10 GP GPI (W.getD j []))
        (burnsideF48s_ev (fun i : Fin 4 => gam i) (W.getD j [])) ∧
      burnsideF48s_ev (fun i : Fin 4 => gam i) (W.getD j []) ∈
        arrGen 728 (burnsideF48t_g23Gens ()) :=
  ev_gam _

theorem P1_max (hX : Nat.card (arrGen 728 (burnsideF48t_g23Gens ())) = 4245696)
    {R : Subgroup (Equiv.Perm (Fin 728))} (hlt : arrGen 728 burnsideF48t_g23P1Arr < R)
    (hRX : R ≤ arrGen 728 (burnsideF48t_g23Gens ())) :
    R = arrGen 728 (burnsideF48t_g23Gens ()) := by
  obtain ⟨hU₀, hU₁, hU₂, hU⟩ := p1_trees
  obtain ⟨hv, hT₀, hT₁, hT₂, hC₀, hC₁, hC₂⟩ := ha_trees
  have hP : arrGen 728 burnsideF48t_g23P1Arr = arrGen 728 (burnsideF48t_g23Gens ()) ⊓
      stabilizer (Equiv.Perm (Fin 728)) (⟨0, by norm_num⟩ : Fin 728) := P1_eq hX
  have hcX : Nat.card (arrGen 728 (burnsideF48t_g23Gens ())) =
      364 * Nat.card (arrGen 728 burnsideF48t_g23P1Arr) := by
    rw [hX, (card_P1_P2_B hX).1]
  have hrange : ∀ g ∈ arrGen 728 (burnsideF48t_g23Gens ()),
      0 ≤ ((g ⟨0, by norm_num⟩ : Fin 728) : ℕ) ∧ ((g ⟨0, by norm_num⟩ : Fin 728) : ℕ) < 0 + 364 :=
    fun g hg => ⟨Nat.zero_le _, X_lt hg (x := ⟨0, by norm_num⟩) (by norm_num)⟩
  exact max_of_trees (X := arrGen 728 (burnsideF48t_g23Gens ()))
    (P := arrGen 728 burnsideF48t_g23P1Arr) (pt := 0) (by norm_num) (prep_letter (i := 0) (by norm_num)).2.1
    (prep_letter (i := 1) (by norm_num)).2.1 (prep_letter (i := 2) (by norm_num)).2.1
    (sig_mem_arrGen (k := 0) (by decide) rfl (by norm_num))
    (sig_mem_arrGen (k := 1) (by decide) rfl (by norm_num))
    (sig_mem_arrGen (k := 2) (by decide) rfl (by norm_num))
    hU₀ hU₁ hU₂ hU (hw_rep burnsideF48t_g23HA) hv hT₀ hT₁ hT₂ hC₀ hC₁ hC₂ hP hcX hrange hlt hRX

theorem P2_max (hX : Nat.card (arrGen 728 (burnsideF48t_g23Gens ())) = 4245696)
    {R : Subgroup (Equiv.Perm (Fin 728))} (hlt : arrGen 728 burnsideF48t_g23P2Arr < R)
    (hRX : R ≤ arrGen 728 (burnsideF48t_g23Gens ())) :
    R = arrGen 728 (burnsideF48t_g23Gens ()) := by
  obtain ⟨hU₀, hU₁, hU₂, hU⟩ := p2_trees
  obtain ⟨hv, hT₀, hT₁, hT₂, hC₀, hC₁, hC₂⟩ := hb_trees
  have hP : arrGen 728 burnsideF48t_g23P2Arr = arrGen 728 (burnsideF48t_g23Gens ()) ⊓
      stabilizer (Equiv.Perm (Fin 728)) (⟨364, by norm_num⟩ : Fin 728) := P2_eq hX
  have hcX : Nat.card (arrGen 728 (burnsideF48t_g23Gens ())) =
      364 * Nat.card (arrGen 728 burnsideF48t_g23P2Arr) := by
    rw [hX, (card_P1_P2_B hX).2.1]
  have hrange : ∀ g ∈ arrGen 728 (burnsideF48t_g23Gens ()),
      364 ≤ ((g ⟨364, by norm_num⟩ : Fin 728) : ℕ) ∧
        ((g ⟨364, by norm_num⟩ : Fin 728) : ℕ) < 364 + 364 :=
    fun g hg => ⟨X_ge hg (x := ⟨364, by norm_num⟩) (by norm_num), (g _).2⟩
  exact max_of_trees (X := arrGen 728 (burnsideF48t_g23Gens ()))
    (P := arrGen 728 burnsideF48t_g23P2Arr) (pt := 364) (by norm_num) (prep_letter (i := 0) (by norm_num)).2.1
    (prep_letter (i := 1) (by norm_num)).2.1 (prep_letter (i := 3) (by norm_num)).2.1
    (sig_mem_arrGen (k := 0) (by decide) rfl (by norm_num))
    (sig_mem_arrGen (k := 1) (by decide) rfl (by norm_num))
    (sig_mem_arrGen (k := 2) (by decide) rfl (by norm_num))
    hU₀ hU₁ hU₂ hU (hw_rep burnsideF48t_g23HB) hv hT₀ hT₁ hT₂ hC₀ hC₁ hC₂ hP hcX hrange hlt hRX

end CFSG.KC.G23F48

end
