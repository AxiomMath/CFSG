module

public import Certificates.Kernel.J4Q.B7Ok
import Certificates.Kernel.J4Q.B7A
import Certificates.Kernel.J4Q.B7W
import Certificates.Kernel.J4Q.Orb
import Certificates.Kernel.J4Q.VlE

public section

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.QT2.B7

theorem b7Hyps : B7Hyps := ⟨b7Lit_chk, CFSG.KD.J4Q.ETCA.all, CFSG.KD.J4Q.BW.all⟩

theorem roots_parts : orB (notB (b7Fixed (repK 5))) (inLK (repK 5) FX5) = true ∧
    orB (notB (b7Fixed (repK 6))) (inLK (repK 6) FX6) = true := by
  have h := b7Roots_chk
  unfold b7Roots at h
  rw [andB_eq, Bool.and_eq_true] at h
  exact h

theorem fix5_parts : ∀ i < CH5.length, allLK (fun e => (fun x => orB (notB (b7Fixed x))
    (inLK x FX5)) (Nat.land e rm)) (CH5.getD i []) = true := by
  intro i hi
  have h := CFSG.KD.J4Q.BF5.all i hi
  unfold b7Fix5 b7FixK at h
  rwa [getL_eq] at h

theorem fix6_parts : ∀ i < CH6.length, allLK (fun e => (fun x => orB (notB (b7Fixed x))
    (inLK x FX6)) (Nat.land e rm)) (CH6.getD i []) = true := by
  intro i hi
  have h := CFSG.KD.J4Q.BF6.all i hi
  unfold b7Fix6 b7FixK at h
  rwa [getL_eq] at h

theorem c4111 :
    CFSG.Sporadic.J4.QT2.B7.chkB7V (CFSG.Sporadic.J4.QT2A.wR CFSG.QuasithinUnique.A5.B7.b7TWord)
        CFSG.QuasithinUnique.A5.B7.b7G0 387 = true ∧
      survP (CFSG.Sporadic.J4.QT2A.wR CFSG.QuasithinUnique.A5.B7.b7TWord)
        CFSG.QuasithinUnique.A5.B7.b7G0 CFSG.Sporadic.J4.Native.rootV ∧
      survOrb (CFSG.Sporadic.J4.QT2A.wR CFSG.QuasithinUnique.A5.B7.b7TWord)
        CFSG.QuasithinUnique.A5.B7.b7G0 5 15180 ∧
      survOrb (CFSG.Sporadic.J4.QT2A.wR CFSG.QuasithinUnique.A5.B7.b7TWord)
        CFSG.QuasithinUnique.A5.B7.b7G0 6 28336 ∧
      baseP (CFSG.Sporadic.J4.QT2A.wR CFSG.QuasithinUnique.A5.B7.b7TWord) ∧
      CFSG.Sporadic.J4.QT2.B7.chkCross
          (vRows (CFSG.Sporadic.J4.QT2A.wR CFSG.QuasithinUnique.A5.B7.b7TWord))
          (CFSG.QuasithinUnique.A5.B7.b7ExplicitWords.map CFSG.Sporadic.J4.QT2A.wR).toArray = true ∧
      CFSG.Sporadic.J4.QT2.B7.chkCross
          (CFSG.QuasithinUnique.A5.B7.b7ExplicitWords.map CFSG.Sporadic.J4.QT2A.wR).toArray
          (vRows (CFSG.Sporadic.J4.QT2A.wR CFSG.QuasithinUnique.A5.B7.b7TWord)) = true :=
  ⟨chkB7V_of b7Hyps b7V_chk, survRoot_of b7Hyps,
    survOrb_of b7Hyps (ℓ := 5) (P0 := P05) (by norm_num) size5 CFSG.KD.J4Q.T5.all sinc5
      (spInK_chunks (SQ := SQ5) rfl CFSG.KD.J4Q.I5.all CFSG.KD.J4Q.S5.all) (fun _ hy => pt_of_fx5 hy) fix5_parts
      roots_parts.1,
    survOrb_of b7Hyps (ℓ := 6) (P0 := P06) (by norm_num) size6 CFSG.KD.J4Q.T6.all sinc6
      (spInK_chunks (SQ := SQ6) rfl CFSG.KD.J4Q.I6.all CFSG.KD.J4Q.S6.all) (fun _ hy => pt_of_fx6 hy) fix6_parts
      roots_parts.2,
    baseP_of b7Hyps b7Base_chk, (cross_of b7Hyps b7Cross_chk).1, (cross_of b7Hyps b7Cross_chk).2⟩

end CertificateChecks.KernelJ4Q

end
