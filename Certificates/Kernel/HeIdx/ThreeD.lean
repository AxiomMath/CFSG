
module

public import CFSG.Quasithin.EmptyFaithful.S151S9THeKInputs
public import CFSG.Quasithin.EmptyFaithful.S151S9THeCen
public import CFSG.Quasithin.EmptyFaithful.S151S9TLat
public import CFSG.Quasithin.EmptyFaithful.S151S9TNineW
public import CFSG.Quasithin.EmptyFaithful.S151S9TNineM
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHe
public import CFSG.Quasithin.EmptyFaithful.S151S9TThreeDFact

public section

namespace CFSG.Quasithin.S151S9T

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
  CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.He
  CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.E2P.SporB

@[expose] def heLs : Array ℕ := #[1, 3, 9, 135, 135, 9, 3, 21, 3, 9, 3]

namespace HeAux

section Perm

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)] [FaithfulSMul Γ (Fin n)]
  {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab]

theorem map_Y_idx3_member (C : LatCtx Γ n Lab) {z₀ : Γ} (hz2 : orderOf z₀ = 2)
    (hZ : centerOf C.S = Subgroup.zpowers z₀) (W : Idx3Wit)
    (hok : W.Ok n C.A.act C.Δ C.D (tab n z₀).toArray) {Ls : Array ℕ}
    (hL : C.D.Om.map (fun o => o.lbl.size) = Ls) (hp3 : Ls[W.p]! = 3)
    (hcp : W.czv[W.p]! = false) (hN : C.D.O.lbl.size ≠ 3) (α : MulAut Γ)
    (hα : C.S.map α.toMonoidHom = C.S) :
    ∃ j < Ls.size, (C.Y W.p).map α.toMonoidHom = C.Y j ∧ Ls[j]! = 3 ∧ W.czv[j]! ≠ true := by
  have hz₀ : z₀ ∈ centerOf C.S := hZ ▸ Subgroup.mem_zpowers z₀
  have hpL : W.p < Ls.size := by
    rw [← lat_J_eq C hL]
    exact hok.1
  have hαz := LatAux.autom_fix_central hz2 hZ α hα
  have hSZ : C.S ≤ (C.Y W.p).map α.toMonoidHom :=
    calc C.S = C.S.map α.toMonoidHom := hα.symm
      _ ≤ (C.Y W.p).map α.toMonoidHom := Subgroup.map_mono (C.S_le_Y W.p)
  have hZc : Nat.card ((C.Y W.p).map α.toMonoidHom) = 3 * Nat.card C.S := by
    rw [Subgroup.card_map_of_injective α.injective, lat_card C hL W.p hpL, hp3, C.S_card]
  exact LatAux.exists_member_idx3 C hz₀ W hok hL hN hSZ hZc
    (LatAux.not_map_le_centralizer α hαz (LatAux.not_Y_le_centralizer C hz₀ W hok hcp))

end Perm

end HeAux

theorem he_idx3Data
    [HeOverFacts] (h : heCheckK) :
    Idx3Data CFSG.Sporadic.He.J heCtx.S (heCtx.Y 1) := by
  obtain ⟨z₀, hz2, hZ, hzT⟩ := he_centre
  have hok : heWit1.Ok 8330 heCtx.A.act heCtx.Δ heCtx.D (tab 8330 z₀).toArray := by
    rw [hzT]
    exact h.1
  exact idx3Data_of_lat heCtx he_S_sylow hz2 hZ heWit1 hok he_Om_map (by decide) (by decide)

theorem he_nineData
    [HeOverFacts] (h : heCheckK) :
    NineData CFSG.Sporadic.He.J heCtx.S (heCtx.Y 1) (heCtx.Y 6) (heCtx.Y 2) := by
  obtain ⟨z₀, hz2, hZ, hzT⟩ := he_centre
  have hz₀ : z₀ ∈ centerOf heCtx.S := hZ ▸ Subgroup.mem_zpowers z₀
  have hok : heWit1.Ok 8330 heCtx.A.act heCtx.Δ heCtx.D (tab 8330 z₀).toArray := by
    rw [hzT]
    exact h.1
  have hL : heCtx.D.Om.map (fun o => o.lbl.size) = heLs := he_Om_map
  have hN : heCtx.D.O.lbl.size = 3935925 := he_orbit_card
  have hnc : ¬ heCtx.Y 1 ≤ Subgroup.centralizer ({z₀} : Set CFSG.Sporadic.He.J) :=
    LatAux.not_Y_le_centralizer heCtx hz₀ heWit1 hok (by decide)
  have hY12 : heCtx.Y 1 ≤ heCtx.Y 2 :=
    (he_Y_le_iff (by norm_num) (by norm_num)).mpr (by decide)
  have hY62 : heCtx.Y 6 ≤ heCtx.Y 2 :=
    (he_Y_le_iff (by norm_num) (by norm_num)).mpr (by decide)
  have hY2ne : heCtx.Y 2 ≠ ⊤ := by
    intro htop
    have h1 := congrArg (fun K : Subgroup CFSG.Sporadic.He.J => Nat.card K) htop
    simp only [Subgroup.card_top] at h1
    rw [he_card, he_member_card 2 (by norm_num)] at h1
    revert h1
    decide
  have hbetween : ∀ K : Subgroup CFSG.Sporadic.He.J, heCtx.S ≤ K → K ≤ heCtx.Y 2 →
      ∃ j < 11, K = heCtx.Y j ∧ 2 ∈ heIncl[j]! := by
    intro K hSK hKY
    rcases LatAux.lat_cases heCtx hL hSK with ⟨j, hj, rfl⟩ | rfl
    · have hj11 : j < 11 := by simpa [heLs] using hj
      exact ⟨j, hj11, rfl, (he_Y_le_iff hj11 (by norm_num)).mp hKY⟩
    · exact absurd (top_le_iff.mp hKY) hY2ne
  have hne : heCtx.Y 1 ≠ heCtx.Y 6 := by
    intro h16
    have h61 : heCtx.Y 6 ≤ heCtx.Y 1 := h16.symm.le
    have h1 := (he_Y_le_iff (by norm_num) (by norm_num)).mp h61
    revert h1
    decide
  have hsup : heCtx.Y 1 ⊔ heCtx.Y 6 = heCtx.Y 2 := by
    obtain ⟨j, hj, hK, hj2⟩ := hbetween _ (le_sup_of_le_left (heCtx.S_le_Y 1))
      (sup_le hY12 hY62)
    have h1 := (he_Y_le_iff (by norm_num) hj).mp (le_sup_left.trans hK.le)
    have h6 := (he_Y_le_iff (by norm_num) hj).mp (le_sup_right.trans hK.le)
    have hfin : ∀ j < 11, j ∈ heIncl[1]! → j ∈ heIncl[6]! → 2 ∈ heIncl[j]! → j = 2 := by
      decide
    rw [hK, hfin j hj h1 h6 hj2]
  have hlat : ∀ K : Subgroup CFSG.Sporadic.He.J, heCtx.S ≤ K → K ≤ heCtx.Y 2 →
      K = heCtx.S ∨ K = heCtx.Y 1 ∨ K = heCtx.Y 6 ∨ K = heCtx.Y 2 := by
    intro K hSK hKY
    obtain ⟨j, hj, hK, hj2⟩ := hbetween K hSK hKY
    have hfin : ∀ j < 11, 2 ∈ heIncl[j]! → j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 6 := by decide
    rcases hfin j hj hj2 with rfl | rfl | rfl | rfl
    · exact Or.inl (hK.trans heCtx.Y_zero)
    · exact Or.inr (Or.inl hK)
    · exact Or.inr (Or.inr (Or.inr hK))
    · exact Or.inr (Or.inr (Or.inl hK))
  have hfin : ∀ j < 11, heLs[j]! = 3 → heWit1.czv[j]! ≠ true → j = 1 ∨ j = 6 := by decide
  refine ⟨he_S_sylow, heCtx.S_le_Y 1, heCtx.S_le_Y 6, hY12, hY62, hne, hsup, ?_, ?_, ?_, hlat,
    ⟨z₀, hz2, hZ, fun hle => hnc (hY12.trans hle)⟩,
    fun hle => hnc (le_centralizer_of_le_normalizer_of_centerOf_eq hz2 hZ hle),
    Idx9Wit.sound heCtx heWit9 h.2, fun α hα => ?_⟩
  · rw [he_member_card 1 (by norm_num), he_card_S]
    decide
  · rw [he_member_card 6 (by norm_num), he_card_S]
    decide
  · rw [he_member_card 2 (by norm_num), he_card_S]
    decide
  · obtain ⟨j, hj, hZj, hj3, hjc⟩ := HeAux.map_Y_idx3_member heCtx hz2 hZ heWit1 hok hL
      (by decide) (by decide) (by rw [hN]; norm_num) α hα
    rcases hfin j (by simpa [heLs] using hj) hj3 hjc with rfl | rfl
    · exact Or.inl hZj
    · exact Or.inr hZj

theorem threeD_of_idx3Data_nineData {G : Type} [Group G] [Finite G] {L S : Subgroup G} {z : G}
    (hS2 : IsPGroup 2 ↥S) (hSN : S ≤ Subgroup.normalizer (L : Set G))
    (hSyl : IsSylowTwoOf (S ⊓ L) L) (hz : z ∈ centerOf (S ⊓ L))
    (hnc : ¬ L ≤ Subgroup.centralizer ({z} : Set G)) {Γ : Type} [Group Γ] [Finite Γ]
    {S₀ Y₁ Y₆ P₉ : Subgroup Γ} (hS₀ : IsSylowTwoOf S₀ ⊤) (h3 : Idx3Data Γ S₀ Y₁)
    (h9 : NineData Γ S₀ Y₁ Y₆ P₉) (e₀ : ↥L ≃* Γ) :
    ∃ P : Subgroup G, P ≤ L ∧ S ⊓ L ≤ P ∧ S ≤ Subgroup.normalizer (P : Set G) ∧
      ¬ P ≤ Subgroup.centralizer ({z} : Set G) ∧ CharTwo P ∧
      IsMinParabolicOf (P ⊔ S) (P ⊔ S) ∧ NumC126 (P ⊔ S) ∧
      oPrimeResidualOf 3 P ⊔ (S ⊓ L) = P := by
  obtain ⟨e, he⟩ := E2P.SporB.exists_equiv_sylow e₀ hSyl hS₀
  by_cases hin : S ≤ Subgroup.normalizer ((pullG e Y₁ : Subgroup G) : Set G)
  · exact ⟨_, threeD_of_pull hS2 hz hnc e he h3 hin⟩
  · exact ⟨_, threeD_of_pull_nine hS2 hSN hz hnc e he h9 hin⟩

theorem he_threeD_of_checks
    [HeOverFacts] (h : heCheckK) : ThreeDLocFor .He := by
  intro G _ _ L S hL hS2 hSN hSyl z hz hnc
  obtain ⟨e₀⟩ := hL
  exact threeD_of_idx3Data_nineData hS2 hSN hSyl hz hnc he_S_sylow
    (he_idx3Data h) (he_nineData h) (e₀.trans CFSG.Sporadic.He.heEquivJ)

end CFSG.Quasithin.S151S9T
