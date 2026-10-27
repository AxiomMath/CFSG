module

public import Certificates.Kernel.HcReplay.Elts
public import Certificates.Kernel.HcReplay.Subs

public section

namespace CFSG.KC.HcPack

@[expose] def invK : List ℕ :=
  [983144943190448394916308416787086744588252755557,
    561805518922342064548809781554527933916404146383,
    429161991104182283319765724322406958292896933102,
    762013451518800896532149628630613642255994127447,
    705361760321647787868167855158079331018478784140,
    1057681983215152949167768939102767487563327600528,
    262051964875263731122081836569932903273683185493,
    661163032299983715975786060237733692383972397769,
    143228294630446395956112231509926355400016248377,
    187343477019917762792240456844040818768780147288,
    284672477448414701423196030843861204025690202518,
    118699506227149327151473913904030579582363500058,
    871647158621772585852716140654538563439056878268,
    328960321215049162280021570103708662676223405364,
    64679161844213441313329300224674744181374665723,
    595194787902770378585277208068204688113645705181,
    457325609588197951382881991026957023299542772606,
    14320458276727698256824768896778270823228928959]

theorem chk_cent_1 : ∀ c ∈ hcElts.E, mulP cA0 c = mulP c cA0 → c ∈ clC1.E := by decide +kernel

theorem chk_cent_2 : ∀ c ∈ hcElts.E, mulP cA2 c = mulP c cA2 → c ∈ clC2.E := by decide +kernel

theorem chk_cent_yp : ∀ c ∈ hcElts.E, mulP cYp c = mulP c cYp → c ∈ clPZ.E := by decide +kernel

theorem chk_cent_ym : ∀ c ∈ hcElts.E, mulP cYm c = mulP c cYm → c ∈ clPZ.E := by decide +kernel

theorem chk_cent_p : ∀ c ∈ hcElts.E, mulP cA0 c = mulP c cA0 → mulP cA2 c = mulP c cA2 →
    c ∈ clPZ.E := by
  decide +kernel

theorem chk_gens_cent : (∀ s ∈ [cA0, cA2, cA3], mulP cA0 s = mulP s cA0) ∧
    (∀ s ∈ [cA2, cA0, cA1], mulP cA2 s = mulP s cA2) ∧
    (∀ s ∈ [cA0, cA2, cZ], mulP cA0 s = mulP s cA0 ∧ mulP cA2 s = mulP s cA2) ∧
    (∀ s ∈ [cA0, cA2, cZ], mulP cYp s = mulP s cYp) ∧
    (∀ s ∈ [cA0, cA2, cZ], mulP cYm s = mulP s cYm) := by
  decide +kernel

theorem chk_norm_1 : ∀ c ∈ hcElts.E, (∀ p ∈ [cA0], ∃ d ∈ clS1.E, mulP c p = mulP d c) →
    c ∈ clN1.E := by
  decide +kernel

theorem chk_norm_2 : ∀ c ∈ hcElts.E, (∀ p ∈ [cA2], ∃ d ∈ clS2.E, mulP c p = mulP d c) →
    c ∈ clN2.E := by
  decide +kernel

theorem chk_norm_p : ∀ c ∈ hcElts.E, (∀ p ∈ [cA0, cA2], ∃ d ∈ clP.E, mulP c p = mulP d c) →
    c ∈ clPE.E := by
  decide +kernel

theorem chk_norm_yp : ∀ c ∈ hcElts.E, (∀ p ∈ [cYp], ∃ d ∈ clYp.E, mulP c p = mulP d c) →
    c ∈ clPE.E := by
  decide +kernel

theorem chk_norm_ym : ∀ c ∈ hcElts.E, (∀ p ∈ [cYm], ∃ d ∈ clYm.E, mulP c p = mulP d c) →
    c ∈ clPE.E := by
  decide +kernel

theorem chk_gens_norm :
    (∀ s ∈ [cA0, cA2, cA3, cA4], ∀ p ∈ [cA0], ∃ d ∈ clS1.E, mulP s p = mulP d s) ∧
    (∀ s ∈ [cA2, cA0, cA1, cA4], ∀ p ∈ [cA2], ∃ d ∈ clS2.E, mulP s p = mulP d s) ∧
    (∀ s ∈ [cA0, cA2, cA4, cZ], ∀ p ∈ [cA0, cA2], ∃ d ∈ clP.E, mulP s p = mulP d s) ∧
    (∀ s ∈ [cA0, cA2, cA4, cZ], ∀ p ∈ [cYp], ∃ d ∈ clYp.E, mulP s p = mulP d s) ∧
    (∀ s ∈ [cA0, cA2, cA4, cZ], ∀ p ∈ [cYm], ∃ d ∈ clYm.E, mulP s p = mulP d s) := by
  decide +kernel

theorem chk_small :
    (∀ c ∈ clH2.E, c ∈ clS1.E → c = 1459980823972598128486511383358617792788444579872) ∧
    (∀ c ∈ clH1.E, c ∈ clS2.E → c = 1459980823972598128486511383358617792788444579872) ∧
    (∃ c ∈ clT2.E, mulP c cA4 = mulP (mulP cA4 cZ) c) ∧
    (∃ c ∈ clT1.E, mulP c cA4 = mulP (mulP cA4 cZ) c) ∧
    (∀ c ∈ clH1.E, mulP cA0 c = mulP c cA0 → c ∈ clL1.E) ∧
    (∀ s ∈ [cA0, cZ], mulP cA0 s = mulP s cA0 ∧ s ∈ clH1.E) ∧
    (∀ c ∈ clH2.E, mulP cA2 c = mulP c cA2 → c ∈ clL2.E) ∧
    (∀ s ∈ [cA2, cZ], mulP cA2 s = mulP s cA2 ∧ s ∈ clH2.E) := by
  decide +kernel

theorem chk_invert_1 : ∀ c ∈ hcElts.E, mulP cA0 c = mulP c cA0 → mulP c cA2 ≠ mulP cA2I c := by
  decide +kernel

theorem chk_invert_2 : ∀ c ∈ hcElts.E, mulP cA2 c = mulP c cA2 → mulP c cA0 ≠ mulP cA0I c := by
  decide +kernel

theorem chk_invK_sub : ∀ c ∈ clK.E,
    (mulP c c = 1459980823972598128486511383358617792788444579872 ∧
      c ≠ 1459980823972598128486511383358617792788444579872 ∧ c ≠ cZ) → c ∈ invK := by
  decide +kernel

theorem chk_invK_conj : ∀ c ∈ invK, ∀ c' ∈ invK, ∃ h ∈ hcElts.E, mulP h c = mulP c' h := by
  decide +kernel

theorem chk_card_t : (hcElts.E.filter fun c => decide (mulP cA4 c = mulP c cA4)).length = 8 := by
  decide +kernel

end CFSG.KC.HcPack

end
