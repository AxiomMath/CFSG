module

public import Certificates.Kernel.IdxFour.OrbOK
public import Certificates.Kernel.IdxFour.Sift
public import CFSG.Certificates.Kernel.IdxFourOrbitSound
public import CFSG.GF2Type.Smith1979.IdxFourModelStab

public section

namespace CFSG.KD.IF4O

open CFSG.KC.IF4C CFSG.KC.IF4O CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.IdxFour

theorem exists_gen {g : Nat} (hg : g < 5) : ∃ s ∈ stabIn E0 a0V, IsP s (look SP g) := by
  have htop := cf17641top
  unfold top at htop
  rw [Bool.and_eq_true, allBelow_iff] at htop
  have h := htop.2 g hg
  unfold genOK at h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨hP, hinv⟩, hfix⟩ := h
  obtain ⟨s, hs⟩ := IsP.exists_of_mul hinv
  have hlen : g < E0Chk.sGensE0.length := hg
  have hr : E0Chk.sGensE0.getD g #[] ∈ E0Chk.sGensE0 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some]
    exact List.getElem_mem _
  have hrows := CFSG.KD.IF4R.rowsP_packR (E0Chk.sGensE0.getD g #[])
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_right _ hr)))))
  have hgen : s ∈ Viol.genGrp E0Chk.sGensE0 := Subgroup.subset_closure
    ⟨_, hr, (CFSG.KC.IF4R.isP_iff_of_rowsP hrows s).1 (hP ▸ hs)⟩
  refine ⟨s, mem_stabIn.2 ⟨CFSG.KD.IF4R.sift17605.2.1 hgen, ?_⟩, hs⟩
  change s (vecOf 15) = vecOf 15
  rw [hs.apply_code, hfix]

theorem sub6 {U : Submodule (ZMod 2) V12} (hinv : ∀ s ∈ stabIn E0 a0V, ∀ u ∈ U, s u ∈ U)
    (hcard : 4 < Nat.card U) : ∃ w ∈ U, Orb.inO378b (codeOf w) = true := by
  have hU : ∀ g < 5, ∀ x, vecOf x ∈ U → vecOf (ap12 (look SP g) x) ∈ U := by
    intro g hg x hx
    obtain ⟨s, hs, hsP⟩ := exists_gen hg
    rw [← hsP.apply_code]
    exact hinv s hs _ hx
  have hU' : ∀ g < 5, ∀ x, vecOf (ap12 (look SP g) x) ∈ U → vecOf x ∈ U := by
    intro g hg x hx
    obtain ⟨s, hs, hsP⟩ := exists_gen hg
    rw [← hsP.apply_code] at hx
    have := hinv s⁻¹ (inv_mem hs) _ hx
    rw [← LinearEquiv.mul_apply, inv_mul_cancel] at this
    exact this
  obtain ⟨u, huU, huD⟩ : ∃ u ∈ U, codeOf u ∉ E0Chk.dCodes := by
    by_contra hcon'
    have hcon : ∀ u ∈ U, codeOf u ∈ E0Chk.dCodes := fun u hu => by
      by_contra hn
      exact hcon' ⟨u, hu, hn⟩
    let f : U → ↥(E0Chk.dCodes.toFinset) := fun u =>
      ⟨codeOf u.1, List.mem_toFinset.2 (hcon u.1 u.2)⟩
    have hf : Function.Injective f := fun a b h => Subtype.ext (by
      have := congrArg (fun c : ↥(E0Chk.dCodes.toFinset) => vecOf c.1) h
      simpa [f, vecOf_codeOf] using this)
    have h1 := Nat.card_le_card_of_injective f hf
    rw [Nat.card_eq_fintype_card (α := ↥(E0Chk.dCodes.toFinset)), Fintype.card_coe] at h1
    have h4 : E0Chk.dCodes.toFinset.card = 4 := by decide
    omega
  have hcnt := cf17641top
  unfold top at hcnt
  rw [Bool.and_eq_true] at hcnt
  obtain ⟨w, hw4, hw, hwU⟩ := exists_P_of_blk (K := 32) cf17641all hcnt.1 (by norm_num)
    (by decide) (by decide) (by decide) hU hU' (codeOf_lt u) huD (by rwa [vecOf_codeOf])
  exact ⟨vecOf w, hwU, by rwa [codeOf_vecOf hw4]⟩

end CFSG.KD.IF4O

end
