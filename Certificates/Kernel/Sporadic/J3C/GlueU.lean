module

public import Certificates.Kernel.Sporadic.J3C.GlueKC

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelSpor.J3CGlue

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.PC CFSG.KS.CentReg CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.J3Data CFSG.Monster.B CFSG.Monster.B.Co2.Native CFSG.Sporadic.J3.Native
  CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen CertificateChecks.KernelSpor
  CertificateChecks.KernelSpor.J3K CertificateChecks.KernelSpor.J3C
  CertificateChecks.KernelSchreierFam

@[expose] noncomputable def υ (i : Nat) : Equiv.Perm (Fin 20520) := Co2.permOfArr 20520 uStrong[i]!

theorem uwOK : ∀ i < 4, lettersOK 2 uWordsK[i]! = true := by
  intro i hi
  interval_cases i <;> decide +kernel

theorem υEq : ∀ i < 4, υ i = wordP σK uWordsK[i]! := by
  intro i hi
  have e : uStrong[i]! = wordA 20520 kStrong kInv uWordsK[i]! :=
    J3CqBind.toArray_map_get _ _ (by have : uWordsK.length = 4 := rfl; omega)
  unfold υ
  rw [e]
  exact poaOfRep (repWP _ (uwOK i hi))

theorem uGetD : ∀ i < 4, List.getD uWordsK i [] = uWordsK[i]! := by
  intro i hi
  interval_cases i <;> rfl

theorem actU : ∀ i < 4, ∀ x < 20520, actN (υ i) x = UL i x := by
  intro i hi x hx
  rw [υEq i hi]
  unfold UL
  rw [uGetD i hi]
  exact (wEval_eq actSK _ (sgnLt _ (uwOK i hi)) x hx).symm

theorem υK : ∀ i < 4, υ i ∈ J3Groups.K := by
  intro i hi
  rw [υEq i hi]
  exact wordP_mem σKK (sgnLt _ (uwOK i hi))

theorem υU : ∀ i < 4, υ i ∈ J3Groups.U := fun i hi => Subgroup.subset_closure ⟨i, hi, rfl⟩

theorem uK : J3Groups.U ≤ J3Groups.K := by
  unfold J3Groups.U J3Groups.gen
  rw [Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  exact υK i hi

theorem uRange : J3Groups.U ≤ Subgroup.closure (Set.range fun t : Fin 4 => υ t.val) := by
  unfold J3Groups.U J3Groups.gen
  rw [Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  exact Subgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩

theorem repTU : TBfs.Rep 20520 0 TU.cnt 4 UL (fun t => t) TU.PTS TU.POS TU.PAR TU.LAB TU.TI :=
  ⟨TBfs.hd_spec tuHd, fun k hk => TBfs.pt_spec (Raw.Orb.allN_iff.1 tuPt k hk)⟩

theorem uFree : ∀ g ∈ J3Groups.U, g (⟨0, root_lt repTU⟩ : Fin 20520) = ⟨0, root_lt repTU⟩ →
    g = 1 :=
  fun g hg => kFree.2.2 g (uK hg)

theorem kFreeU : ∀ g ∈ J3Groups.K, g (⟨0, root_lt repTU⟩ : Fin 20520) = ⟨0, root_lt repTU⟩ →
    g = 1 :=
  kFree.2.2

theorem uCard : Nat.card J3Groups.U = 32 := by
  have h := (card_of_free repTU actU υU (fun _ hg => tree_closed repTU actU (uRange hg))
    uFree).1
  rw [h, Nat.eq_of_beq_eq_true tuCnt]

theorem conjU : ∀ h < 2, ∀ i < 4, κ h * υ i * (κ h)⁻¹ ∈ J3Groups.U :=
  normK_sound repTU actU υU uK kFreeU (KL := KLr) (U := UL) (nk := 2) (nu := 4) (κ := κ) (υ := υ)
    actK actKi actU κK υK normU

theorem kNorm : J3Groups.K ≤ Subgroup.normalizer (J3Groups.U : Set (Equiv.Perm (Fin 20520))) := by
  refine closure_le_normalizer_closure _ _ ?_
  rintro _ ⟨h, hh, rfl⟩ _ ⟨i, hi, rfl⟩
  exact conjU h hh i hi

theorem kCentU : ∀ g ∈ J3Groups.K, (∀ u ∈ J3Groups.U, g * u = u * g) → g ∈ J3Groups.U :=
  fun _ hg hc => centUK_sound repTU actU υU uK kFreeU repTK actSK kRep (U := UL) (nu := 4)
    actU centU hg fun i hi => hc _ (υU i hi)

end CertificateChecks.KernelSpor.J3CGlue

end
