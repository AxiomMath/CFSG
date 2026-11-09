module

public import Certificates.Data.KSU38R.Check
public import CFSG.Certificates.Kernel.U38NSound

public section

namespace CertificateChecks.KSU38RK

open CFSG.LieType.SeitzGeneration.HeisSmall HuppertU38F KSU38R CFSG.KC.HeisN

abbrev toQ (A : M3 ℕ) : M3 Q8 := FK.toL fk8 GF8.ofNat' A

@[expose] def isInvolD (A : M3 ℕ) : Bool := !isScalar (toQ A) && isScalar (toQ (fk8.mMul A A))

@[expose] def invsN : List (M3 ℕ) := (fk8.guListN 8).filter isInvolD

@[expose] def commModD (A B : M3 ℕ) : Bool :=
  (List.range (fk8.p * fk8.p)).any fun n =>
    decide (toQ (fk8.mMul A B) = toQ (fk8.mSmul n (fk8.mMul B A)))

@[expose] def proptoD (A B : M3 ℕ) : Bool :=
  (List.range (fk8.p * fk8.p)).any fun n => decide (toQ A = toQ (fk8.mSmul n B))

@[expose] def noV4N : Bool :=
  fk8.forallUnitaryN 8 (fun A => !isInvolD A || decide (toQ A ∈ invsN.map toQ)) &&
    invsN.all fun U => invsN.all fun V => !commModD U V || proptoD U V

@[expose] noncomputable def mpowN (A : M3 ℕ) (n : ℕ) : M3 ℕ :=
  Nat.rec (motive := fun _ => M3 ℕ) mOne (fun _ acc => fk8.mMul A acc) n

@[expose] noncomputable def expN : Bool :=
  fk8.forallUnitaryN 8 fun A => isScalar (toQ (mpowN A 12))

@[expose] def regFlagD (A : M3 ℕ) : Bool :=
  isScalar (toQ (fk8.mMul (fk8.mMul A A) A)) && decide ((toQ (fk8.mMul (fk8.mMul A A) A)).a00 ^ 3 = 1) &&
    hasCyc (toQ A)

@[expose] noncomputable def dCheckOneN (D : M3 ℕ) : Bool :=
  fk8.forallUnitaryN 8 fun Z =>
    !isScalar (toQ (fk8.mMul (fk8.mMul Z Z) Z)) || isScalar (toQ Z) || !commModD D Z ||
      proptoD Z D || proptoD Z (fk8.mMul D D) ||
      (List.range 3).any fun j => regFlagD (fk8.mMul (mpowN D j) Z)

@[expose] noncomputable def dN : Bool :=
  dCheckOneN (matN [1, 0, 0, 0, 1, 0, 0, 0, 8]) && dCheckOneN (matN [1, 0, 0, 0, 1, 0, 0, 0, 9])

theorem ho : FK.dec fk8 GF8.ofNat' 8 = w0 := by
  ext <;> rfl

theorem toQ_mMul (A B : M3 ℕ) : toQ (fk8.mMul A B) = toQ A * toQ B :=
  FK.toL_mMul fk8_sound A B

theorem toQ_mSmul (n : ℕ) (A : M3 ℕ) :
    toQ (fk8.mSmul n A) = M3.smul (FK.dec fk8 GF8.ofNat' n) (toQ A) :=
  FK.toL_mSmul fk8_sound n A

theorem isInvol_eq (A : M3 ℕ) : isInvol (toQ A) = isInvolD A := by
  rw [isInvol, isInvolD, toQ_mMul]

theorem commMod_eq (A B : M3 ℕ) : commMod (toQ A) (toQ B) = commModD A B := by
  rw [commMod, commModD, Bool.eq_iff_iff, decide_eq_true_iff, List.any_eq_true]
  constructor
  · rintro ⟨l, hl⟩
    obtain ⟨n, hn, hdn⟩ := FK.dec_surj fk8_sound l
    refine ⟨n, List.mem_range.2 hn, decide_eq_true ?_⟩
    rw [toQ_mMul, toQ_mSmul, toQ_mMul, hdn]
    exact hl
  · rintro ⟨n, _, hn⟩
    refine ⟨FK.dec fk8 GF8.ofNat' n, ?_⟩
    have h := of_decide_eq_true hn
    rw [toQ_mMul, toQ_mSmul, toQ_mMul] at h
    exact h

theorem propto_eq (A B : M3 ℕ) : propto (toQ A) (toQ B) = proptoD A B := by
  rw [propto, proptoD, Bool.eq_iff_iff, decide_eq_true_iff, List.any_eq_true]
  constructor
  · rintro ⟨l, hl⟩
    obtain ⟨n, hn, hdn⟩ := FK.dec_surj fk8_sound l
    refine ⟨n, List.mem_range.2 hn, decide_eq_true ?_⟩
    rw [toQ_mSmul, hdn]
    exact hl
  · rintro ⟨n, _, hn⟩
    refine ⟨FK.dec fk8 GF8.ofNat' n, ?_⟩
    have h := of_decide_eq_true hn
    rw [toQ_mSmul] at h
    exact h

theorem invols_eq : invols () = invsN.map toQ := by
  have hf : (isInvol ∘ FK.toL fk8 GF8.ofNat') = isInvolD := funext isInvol_eq
  have e : invols () = ((fk8.guListN 8).filter isInvolD).map (FK.toL fk8 GF8.ofNat') := by
    rw [invols, FK.guList_eq fk8_sound ho, List.filter_map, hf]
  exact e

theorem mpow_toQ (A : M3 ℕ) : ∀ n, mpow (toQ A) n = toQ (mpowN A n)
  | 0 => by
    rw [mpow]
    exact (FK.toL_mOne fk8_sound).symm
  | n + 1 => by
    rw [mpow, mpow_toQ A n]
    exact (toQ_mMul A (mpowN A n)).symm

theorem expCheck_eq : expCheck () = expN := by
  simp only [expCheck, FK.forallUnitary_eq fk8_sound ho, mpow_toQ, expN]

theorem toQ_mMul' (A B : M3 ℕ) : toQ A * toQ B = toQ (fk8.mMul A B) := (toQ_mMul A B).symm

theorem regFlag_eq (A : M3 ℕ) : regFlag (toQ A) = regFlagD A := by
  rw [regFlag, regFlagD, toQ_mMul, toQ_mMul]

theorem dCheckOne_eq (D : M3 ℕ) : dCheckOne (toQ D) = dCheckOneN D := by
  simp only [dCheckOne, FK.forallUnitary_eq fk8_sound ho, mpow_toQ, toQ_mMul', commMod_eq,
    propto_eq, regFlag_eq, dCheckOneN]

theorem dCheck_eq : dCheck () = dN := by
  have e : dCheck () = (dCheckOne (toQ (matN [1, 0, 0, 0, 1, 0, 0, 0, 8])) &&
      (dCheckOne (toQ (matN [1, 0, 0, 0, 1, 0, 0, 0, 9])) && true)) := rfl
  rw [e, dCheckOne_eq, dCheckOne_eq, Bool.and_true]
  rfl

theorem noV4Check_eq : noV4Check () = noV4N := by
  simp only [noV4Check, invols_eq, FK.forallUnitary_eq fk8_sound ho, List.all_map, Function.comp_def,
    commMod_eq, propto_eq, isInvol_eq, noV4N]

end CertificateChecks.KSU38RK
