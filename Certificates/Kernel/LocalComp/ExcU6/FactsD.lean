module

public import Certificates.Kernel.LocalComp.ExcU6.FactsR
public import Certificates.Kernel.LocalComp.ExcU6.DTexts
public import Certificates.Kernel.LocalComp.ExcU6.D1
public import Certificates.Kernel.LocalComp.ExcU6.D2
public import Certificates.Kernel.LocalComp.ExcU6.D3
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option linter.unusedSectionVars false

namespace CertificateChecks.KernelLC.ExcU6

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates
open CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu CFSG.ComponentClassification.M12Cover
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.MOC CFSG.KS.M11
open CFSG.KS.SporSch.CodesImg CFSG.KC.Child3 CFSG.KC.LocalComp.ExcDeriv
open CFSG.ComponentClassification.RankTwoClassical.ExcU6 CFSG.EvenSmallLie.UnitarySix
open CertificateChecks.KernelLC.ExcGlue CertificateChecks.KernelU6 CertificateChecks.KernelLC.Slices


theorem d1_eq : d1 = decDerivs D.d1 := by
  rw [d1, T1.eq, CFSG.KC.G13.charsEq_sound kT1]
  exact parseDerivs_derivsC_u6 (by rw [decDerivs, D.d1, List.map_cons]; exact List.cons_ne_nil _ _)

theorem d2_eq : d2 = decDerivs D.d2 := by
  rw [d2, T2.eq, CFSG.KC.G13.charsEq_sound kT2]
  exact parseDerivs_derivsC_u6 (by rw [decDerivs, D.d2, List.map_cons]; exact List.cons_ne_nil _ _)

theorem d3_eq : d3 = decDerivs D.d3 := by
  rw [d3, T3.eq, CFSG.KC.G13.charsEq_sound kT3]
  exact parseDerivs_derivsC_u6 (by rw [decDerivs, D.d3, List.map_cons]; exact List.cons_ne_nil _ _)

theorem derivs_all {reps : List (Equiv.Perm (Fin 693))} {ds : List (List (ℕ × List ℤ × ℕ))}
    {x : Equiv.Perm (Fin 693)} {X : Nat} {forbid : List Nat} {c : Nat} {E : Nat → Nat}
    (hx : imageList x = (unpack 693 10 X).toList) (hl : reps.length = c)
    (hi : ∀ i < c, imageList (reps.getD i 1) = (unpack 693 10 (E i)).toList)
    (hk : ∀ i < c, dOK X E forbid ds i = true) :
    (reps.zip ds).all (fun p => schreierPermEq p.1 x || derivCheck forbid [x, p.1] p.2) = true := by
  refine all_zip_of fun i hr hd => ?_
  have hc : i < c := hl ▸ hr
  have himg := hi i hc
  rw [List.getD_eq_getElem _ _ hr] at himg
  have h := hk i hc
  unfold dOK at h
  rw [List.getD_eq_getElem _ _ hd] at h
  rw [Bool.or_eq_true]
  cases e : Nat.beq (E i) X
  · rw [e] at h
    right
    exact derivSqK_sound_u6 sz one693 alphabet_len imgA (fun j hj => pA j hj) _
      (List.Forall₂.cons hx (List.Forall₂.cons himg List.Forall₂.nil)) h
  · left
    exact schreierPermEq_of_img himg (Nat.eq_of_beq_eq_true e ▸ hx)

theorem deriv_check : censusDerivCheck = true := by
  have h1 : ∀ i < sRepWords.length, dOK J1 (fun i => RS.E (lget RS.OFF i)) [] (decDerivs D.d1) i =
      true := by
    have e : sRepWords.length = 43 := by decide
    rw [e]
    exact of_slices (R := fun i => dOK J1 (fun i => RS.E (lget RS.OFF i)) [] (decDerivs D.d1) i)
      D1.all (by decide)
  have h2 : ∀ i < r2Words.length, dOK X2 (fun i => R2.E (lget R2.OFF i)) [181] (decDerivs D.d2) i =
      true := by
    have e : r2Words.length = 57 := by decide
    rw [e]
    exact of_slices (R := fun i => dOK X2 (fun i => R2.E (lget R2.OFF i)) [181] (decDerivs D.d2) i)
      D2.all (by decide)
  have h3 : ∀ i < r3Words.length, dOK X3 (fun i => R3.E (lget R3.OFF i)) [181, 53]
      (decDerivs D.d3) i = true := by
    have e : r3Words.length = 75 := by decide
    rw [e]
    exact of_slices (R := fun i => dOK X3 (fun i => R3.E (lget R3.OFF i)) [181, 53]
      (decDerivs D.d3) i) D3.all (by decide)
  unfold censusDerivCheck
  rw [d1_eq, d2_eq, d3_eq, derivs_all imgJ1 sReps_len imgRS h1, derivs_all imgX2 r2Reps_len imgR2 h2,
    derivs_all imgX3 r3Reps_len imgR3 h3, sReps_len, r2Reps_len, r3Reps_len]
  rfl

end CertificateChecks.KernelLC.ExcU6

end
