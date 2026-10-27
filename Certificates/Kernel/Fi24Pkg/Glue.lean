module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicPermutesPackage
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24
public import Certificates.Certificate2198
public import Certificates.Certificate2205
public import Certificates.Certificate3046
import Certificates.Kernel.Fi24Pkg.Checks
import CFSG.Certificates.Kernel.M24QSpan
import CFSG.Quasithin.Vol2.Ch12Sec5KGM24
import CFSG.Quasithin.Vol2.Ch4Sec2InspM22SporMid
import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Local
import CFSG.RankThree.Asc83Table.E9
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicModelGlue
public import CFSG.GH74.SmallRanks.AltM11
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalFamily
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearStrong
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.Hyp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicPermutesCover
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Quasithin.Background.A1cA132Action
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.Background.E4Solv
public import CFSG.Quasithin.Background.F6Amalgams
public import CFSG.Quasithin.Background.F6SolvableQuotient
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.HFF
public import CFSG.Quasithin.Background.HPairBridge
public import CFSG.Quasithin.Background.HSL3Inner
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4OutBase
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S153Baum
public import CFSG.Quasithin.EmptyFaithful.S153Nine
public import CFSG.Quasithin.EmptyFaithful.T1531Close2
public import CFSG.Quasithin.EmptyFaithful.T1531In66b
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.Quasithin.Vol2.Ch4Sec1Lem415
public import CFSG.Quasithin.Vol2.Ch4Sec4Lem445
public import CFSG.Sporadic.Schreier.J4SCommGenBase1
public import CFSG.Sporadic.Schreier.J4SLocalNodes
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M11
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M12
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M23
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.Walter.JRFacts

set_option maxRecDepth 100000

namespace CFSG.KD.Fi24Pkg

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.H13.S125KG.M24
open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.M24
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Sporadic.Mathieu (m24a m24b)
open scoped commutatorElement


theorem pow_three_of_tab {g : Γ} {t : List ℕ} (ht : tab 24 g = t) (h : cubeT t = List.range 24) :
    g ^ 3 = 1 :=
  eq_of_tab_eq (by rw [pow_three, tab_mul, tab_mul, ht, tab_one]; exact h)

theorem ne_one_of_tab {g : Γ} {t : List ℕ} (ht : tab 24 g = t) (h : t ≠ List.range 24) :
    g ≠ 1 := fun e => h (by rw [← ht, e, tab_one])

theorem ne_of_tab {g h : Γ} {t u : List ℕ} (ht : tab 24 g = t) (hu : tab 24 h = u) (hne : t ≠ u) :
    g ≠ h := fun e => hne (by rw [← ht, ← hu, e])

theorem exists_sg (i : ℕ) (hi : i < 4) : ∃ s ∈ m24Ctx.sg, tab 24 s = sTabsK.getD i [] := by
  have hmem : sTabsK.getD i [] ∈ sTabsK := by
    interval_cases i <;> decide
  have hs : sTabsK = m24Ctx.sg.map (tab 24) := by
    rw [← sTabs_eq]
    have h1 : genTabs 24 m24Ctx.sg = m24STabs := by
      rw [m24Ctx.hsg, m24_D_sTabs]
      rfl
    rw [← h1, genTabs, List.map_map]
    rfl
  have key : ∀ t ∈ sTabsK, ∃ s ∈ m24Ctx.sg, tab 24 s = t := by
    rw [hs]
    intro t ht
    exact List.mem_map.mp ht
  exact key _ hmem

theorem gens_eq {j : ℕ} {w : List ℕ} (h : m24LatK.mw[j]! = [w]) : m24Ctx.gens j = [elt w] := by
  change (m24LatK.mw[j]!).map (wordElt m24a m24b) = _
  rw [h]
  rfl

theorem words : m24LatK.mw[5]! = [w5] ∧ m24LatK.mw[11]! = [w11] := by
  have h := fi24WordsOK_ok
  simp only [fi24WordsOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem elt_mem_Y {j : ℕ} {w : List ℕ} (h : m24LatK.mw[j]! = [w]) : elt w ∈ m24Ctx.Y j :=
  m24Ctx.gens_mem_Y _ (by rw [gens_eq h]; exact List.mem_singleton_self _)

theorem sg_mem_Y {s : Γ} (hs : s ∈ m24Ctx.sg) (j : ℕ) : s ∈ m24Ctx.Y j :=
  m24Ctx.S_le_Y j (m24Ctx.sg_mem_S s hs)

theorem normalizer_S :
    Subgroup.normalizer (m24Ctx.S : Set Γ) = m24Ctx.S := by
  have hU := m24_S_sylow
  refine CFSG.EvenSporadicStandard.M24Std.normalizer_eq_of_sylow
    (⟨MulEquiv.refl _⟩ : CFSG.Blueprint.NativeSporadic.IsSporadic Γ .M24) hU.2.1 ?_
  have h := hU.2.2
  have e : (m24Ctx.S.subgroupOf ⊤).index = m24Ctx.S.index := Subgroup.relIndex_top_right _
  rwa [e] at h

theorem map_eq
    {P : Subgroup Γ} (hSP : m24Ctx.S ≤ P) (α : MulAut Γ)
    (hα : m24Ctx.S.map α.toMonoidHom = m24Ctx.S) : P.map α.toMonoidHom = P := by
  obtain ⟨d, hd⟩ : ∃ d : Γ, ∀ y, α y = d * y * d⁻¹ := CFSG.Quasithin.H13.Ch4.m24_all_inner α
  have hαeq : α = MulAut.conj d := MulEquiv.ext fun x => by rw [hd x, MulAut.conj_apply]
  rw [hαeq] at hα ⊢
  have hdN : d ∈ Subgroup.normalizer (m24Ctx.S : Set Γ) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hα
  rw [normalizer_S] at hdN
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (hSP hdN))

theorem card_Y {j : ℕ} (hj : j < 13) (m : ℕ)
    (hm : (#[1, 315, 63, 135, 21, 9, 21, 3, 3, 3, 9, 3, 9] : Array ℕ)[j]! = m) :
    Nat.card (m24Ctx.Y j) = m * Nat.card m24Ctx.S := by
  have hk : m24Ctx.k = 10 := rfl
  rw [m24_member_card j hj, m24Ctx.S_card, hk, hm]
  norm_num

theorem indexNine :
    IndexNinePackage Γ := by
  obtain ⟨s, hs, hsT⟩ := exists_sg 0 (by norm_num)
  have hw5 := words.1
  set v := elt w5
  have hv : tab 24 v = wTab w5 := tab_elt w5
  set x := v * v
  set y := s * (v * (s * v))
  have hxT : tab 24 x = xT := by rw [tab_mul, hv]; rfl
  have hyT : tab 24 y = yT := by
    rw [tab_mul, tab_mul, tab_mul, hv, hsT]
    rfl
  have hvY := elt_mem_Y hw5
  have hsY := sg_mem_Y hs 5
  have hxY : x ∈ m24Ctx.Y 5 := mul_mem hvY hvY
  have hyY : y ∈ m24Ctx.Y 5 := mul_mem hsY (mul_mem hvY (mul_mem hsY hvY))
  clear_value x y
  have h := fi24NineOK_ok
  simp only [fi24NineOK, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne]
    at h
  obtain ⟨⟨⟨⟨⟨⟨hx3, hy3⟩, hxy⟩, hx1⟩, hy1⟩, hyx⟩, hyx2⟩ := h
  have hx3' := pow_three_of_tab hxT hx3
  have hy3' := pow_three_of_tab hyT hy3
  have hcomm : x * y = y * x := eq_of_tab_eq (by rw [tab_mul, tab_mul, hxT, hyT]; exact hxy)
  have hx1' := ne_one_of_tab hxT hx1
  have hy1' := ne_one_of_tab hyT hy1
  have hyx' := ne_of_tab hyT hxT hyx
  have hyx2' : y ≠ x ^ 2 := ne_of_tab hyT (by rw [pow_two, tab_mul, hxT]) hyx2
  have hnz : y ∉ Subgroup.zpowers x := by
    intro hz
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hge : 0 ≤ n % (3 : ℤ) := Int.emod_nonneg n (by norm_num)
    have hlt : n % (3 : ℤ) < 3 := Int.emod_lt_of_pos n (by norm_num)
    rw [zpow_eq_zpow_emod' n hx3'] at hn
    interval_cases h : n % (3 : ℤ)
    · rw [zpow_zero] at hn
      exact hy1' hn.symm
    · rw [zpow_one] at hn
      exact hyx' hn.symm
    · rw [zpow_two] at hn
      exact hyx2' hn.symm
  have hcomm' : ⁅x, y⁆ = 1 := by rw [commutatorElement_eq_one_iff_mul_comm]; exact hcomm
  refine ⟨m24Ctx.S, m24Ctx.Y 5, Subgroup.closure {x, y}, m24_S_sylow, m24Ctx.S_le_Y 5,
    card_Y (by norm_num) 9 rfl, map_eq (m24Ctx.S_le_Y 5), ?_,
    CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine hx3' hy3' hcomm hx1' hnz,
    fun q hq => ?_⟩
  · rw [Subgroup.closure_le]
    intro w hw
    rcases hw with rfl | rfl
    · exact hxY
    · exact hyY
  · exact pow_three_eq_one_of_mem_closure_cubic hx3' hy3'
      (by rw [hcomm']; exact Commute.one_left x) (by rw [hcomm']; exact Commute.one_left y) hq

theorem indexThree :
    IndexThreePackage Γ := by
  obtain ⟨s, hs, hsT⟩ := exists_sg 1 (by norm_num)
  have hw11 := words.2
  set v := elt w11
  have hv : tab 24 v = wTab w11 := tab_elt w11
  set a := s * v
  have haT : tab 24 a = aT := by rw [tab_mul, hv, hsT]; rfl
  have hgT : tab 24 s = gT := hsT
  have haY : a ∈ m24Ctx.Y 11 := mul_mem (sg_mem_Y hs 11) (elt_mem_Y hw11)
  clear_value a
  have h := fi24ThreeOK_ok
  simp only [fi24ThreeOK, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne]
    at h
  obtain ⟨⟨ha3, ha1⟩, hga⟩ := h
  have ha3' := pow_three_of_tab haT ha3
  have hga' : s * a = a * a * s :=
    eq_of_tab_eq (by rw [tab_mul, tab_mul, tab_mul, haT, hgT]; exact hga)
  have hinv : s * a * s⁻¹ = a⁻¹ := by
    rw [hga', mul_inv_cancel_right]
    refine (eq_inv_of_mul_eq_one_left ?_)
    rw [← pow_three']
    exact ha3'
  exact ⟨m24Ctx.S, m24Ctx.Y 11, a, s, m24_S_sylow, m24Ctx.S_le_Y 11, card_Y (by norm_num) 3 rfl,
    map_eq (m24Ctx.S_le_Y 11), haY, ne_one_of_tab haT ha1, ha3', hinv⟩

end CFSG.KD.Fi24Pkg

public section

namespace CFSG.KD.Fi24Pkg

theorem package744112 :
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.IndexNinePackage
        ↥CFSG.Blueprint.NativeSporadic.M24 ∧
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.IndexThreePackage
        ↥CFSG.Blueprint.NativeSporadic.M24 :=
  ⟨indexNine, indexThree⟩

end CFSG.KD.Fi24Pkg
