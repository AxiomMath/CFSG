
module

public import Certificates.Kernel.Fin76bOm.AutEChk
public import Certificates.Kernel.Fin76bOm.UGlue
public import Certificates.Kernel.Fin76bAut.Rec
public import CFSG.Certificates.Kernel.Fin76bOm.AutESound

public section

namespace CertificateChecks.KernelC24608

open CFSG.KS.EAut CertificateChecks.KernelFin76bAut CFSG.EvenSporadicStandard.Fin76b
  CFSG.EvenSporadicStandard.Fin76b.AutETable CFSG.EvenSporadicStandard.Fin76b.W16
  CFSG.KC.Fin76bU

theorem autEFact_of_realizes_mulE0 {H : Type*} [Group H] {M : Array (Array ℕ)} {elt : ℕ → H}
    (R : Realizes H 32 M elt) (hM : ∀ a < 32, ∀ b < 32, mt M a b = mulE0 a b) : AutEFact H :=
  autEFact_of_eAEK R (fun a ha b hb => (hM a ha b hb).trans (eTabK_spec ch24614Tab a ha b hb).symm)
    (rec_all_of_realizes R hM).1 ch24608AutE

theorem autEFact_of_labelling_mulE0 {G : Type*} [Group G] {E : Subgroup G} {t : G} {tI : ℕ}
    {eltE : ℕ → G} (hL : ELabelling E t mulE0 tI eltE) : AutEFact ↥E := by
  obtain ⟨elt, R, -⟩ := E69.realizes_of_labelling hL
  exact autEFact_of_realizes_mulE0 R fun a ha b hb => mt_tab2 mulE0 ha hb

theorem autEFact_of_labelling_mulEJ3 {G : Type*} [Group G] {E : Subgroup G} {t : G} {tI : ℕ}
    {eltE : ℕ → G} (hL : ELabelling E t mulEJ3 tI eltE) : AutEFact ↥E := by
  obtain ⟨h0, hmul, hinj⟩ := eAEIsoU_spec ch24608Iso
  have h2 := tblU_of j2U_tbl
  have h3 := tblU_of j3U_tbl
  have hlt : ∀ k, fldU 5 RH k < 32 := fun k => fldU_lt 5 RH k
  have hsurj : ∀ j < 32, ∃ k < 32, fldU 5 RH k = j := by
    intro j hj
    let f : Fin 32 → Fin 32 := fun k => ⟨fldU 5 RH k.1, hlt k⟩
    have hf : Function.Injective f := fun x y hxy =>
      Fin.ext (hinj x x.2 y y.2 (congrArg Fin.val hxy))
    obtain ⟨k, hk⟩ := (Finite.injective_iff_surjective.1 hf) ⟨j, hj⟩
    exact ⟨k, k.2, congrArg Fin.val hk⟩
  refine autEFact_of_labelling_mulE0 (t := 1) (tI := 0) (eltE := fun k => eltE (fldU 5 RH k))
    { mem := fun k _ => hL.mem _ (hlt k)
      surj := fun e he => ?_
      inj := fun a ha b hb hab => hinj a ha b hb (hL.inj _ (hlt a) _ (hlt b) hab)
      lt := fun a ha b hb => h2 a ha b hb ▸ mU_lt J2U.P a b
      mul := fun a ha b hb => ?_
      one := ?_
      tI_lt := by norm_num
      at_tI := ?_ }
  · obtain ⟨j, hj, hje⟩ := hL.surj e he
    obtain ⟨k, hk, hkj⟩ := hsurj j hj
    exact ⟨k, hk, by rw [hkj, hje]⟩
  · rw [← h2 a ha b hb, hmul a ha b hb, h3 _ (hlt a) _ (hlt b)]
    exact hL.mul _ (hlt a) _ (hlt b)
  · rw [h0]
    exact hL.one
  · rw [h0]
    exact hL.one

end CertificateChecks.KernelC24608

end
