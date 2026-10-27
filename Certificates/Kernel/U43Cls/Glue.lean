module

public import Certificates.Kernel.U43Cls.Sound
public import Certificates.Data.U43NoL3

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU43Cls

open CFSG.KC.Enum CFSG.KC.U43Mod CFSG.KC.U43Cls CFSG.KS CFSG.KS.U43Mod CFSG.KS.U43Cls
  CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.KGroups.Native
  CFSG.KGroups.U43 CFSG.LieType.Multipliers.U43 CFSG.Quasithin.H13.U43
  CFSG.Sporadic.SmallOddCore CFSG.EvenSporadicStandard.M24Std.CU43 CertificateChecks.KernelU43Mod


theorem cls_cover {f : Equiv.Perm (Fin 820)} (hf : f ∈ conjClass P (CP 0)) :
    ∃ i < 2835, clsE i = f := by
  obtain ⟨h1, h2, -⟩ := cls_sound
  have hsub : clsE '' Set.Iio 2835 ⊆ conjClass P (CP 0) := by
    rintro _ ⟨i, hi, rfl⟩
    exact h1 i hi
  have hcard : (clsE '' Set.Iio 2835).ncard = 2835 := by
    have hinj : Set.InjOn clsE (Set.Iio 2835) := fun i hi i' hi' e => h2 i hi i' hi' e
    rw [hinj.ncard_image, Set.ncard_Iio_nat]
  have he := Set.eq_of_subset_of_ncard_le hsub (by rw [ncard_classA, hcard]) (Set.toFinite _)
  rw [← he] at hf
  obtain ⟨i, hi, e⟩ := hf
  exact ⟨i, hi, e⟩

theorem rep_x : Rep 820 (wArr 820 tabA tabB sevenWord) xP := by
  have h := rep_wArr' (w := sevenWord) (by decide)
  have e : evalG CP sevenWord = xP := by
    simp [evalG, sevenWord, letterVal, xP]
  rwa [e] at h

theorem not_both {f : Equiv.Perm (Fin 820)} (hf : f ∈ conjClass P (CP 0)) :
    ¬(f * (xP * (f * xP⁻¹)) = xP * (f * xP⁻¹) * f ∧
      f * (xP * xP * (f * (xP⁻¹ * xP⁻¹))) = xP * xP * (f * (xP⁻¹ * xP⁻¹)) * f) := by
  obtain ⟨i, hi, rfl⟩ := cls_cover hf
  obtain ⟨s, hs, hne⟩ := cls_sound.2.2 i hi
  rintro ⟨e1, e2⟩
  interval_cases s
  · have e : yv 0 = xP := by simp [yv]
    rw [e] at hne
    exact hne (by simpa [mul_assoc] using e1)
  · have e : yv 1 = xP * xP := by simp [yv]
    rw [e, mul_inv_rev] at hne
    exact hne (by simpa [mul_assoc] using e2)

theorem noSeven_ok : noSevenCheck 820 tabA tabB = true := by
  have hx := rep_x
  have hxi : Rep 820 (invCand 820 (wArr 820 tabA tabB sevenWord)) xP⁻¹ :=
    CFSG.KS.Raw.rep_invCand hx
  have hx2 := rep_compA hx hx
  have hxi2 := rep_compA hxi hxi
  obtain ⟨hn, hL, -⟩ := orb_enum
  simp only [noSevenCheck, Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨⟨⟨⟨⟨invsOK_AB, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact (eqA_iff (rep_compA rep_A rep_A) rep_idA).2 CP0_sq
  · exact isInvA_of_rep hx hxi
  · refine (eqA_iff (rep_compA hx2 (rep_compA hx2 (rep_compA hx2 hx))) rep_idA).2 ?_
    rw [← xP_pow]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  · exact Bool.eq_false_iff.2 fun h => xP_ne ((eqA_iff hx rep_idA).1 h)
  · rw [allLt_iff]
    intro i hi
    obtain ⟨f, hf, hr⟩ := hL i (by rw [hn]; exact hi)
    rw [Bool.not_eq_true', Bool.and_eq_false_iff]
    by_contra hc
    simp only [not_or, Bool.not_eq_false, commuteArr, conjugateA] at hc
    exact not_both hf ⟨(eqA_iff (rep_compA hr (rep_compA hx (rep_compA hr hxi)))
      (rep_compA (rep_compA hx (rep_compA hr hxi)) hr)).1 hc.1,
      (eqA_iff (rep_compA hr (rep_compA hx2 (rep_compA hr hxi2)))
        (rep_compA (rep_compA hx2 (rep_compA hr hxi2)) hr)).1 hc.2⟩

end CertificateChecks.KernelU43Cls

end
