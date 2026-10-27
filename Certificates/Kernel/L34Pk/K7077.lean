module

public import Certificates.Kernel.LocalComp.WittLev
public import Certificates.Kernel.L34Pk.Data
public import CFSG.Quasithin.Recognition.M22UniqueDataInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelL34

open CFSG.KC.WCnt CertificateChecks.KernelSpor.M22Syl CertificateChecks.KernelLC.Witt
  CFSG.Quasithin.Asc94

set_option maxRecDepth 100000

theorem k77a : wc (fun σ => ∀ y ∈ m22HexadL, σ y = y) I (fun x => Nat.beq x 0)
    (fun _ x => Nat.beq x 1) (fun _ _ x => Nat.beq x 2) = 16 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k77b : wc (fun σ => (∀ y ∈ m22HexadL, σ y = y) ∧ ¬ ∀ x, σ (σ x) = x) I
    (fun x => Nat.beq x 0) (fun _ x => Nat.beq x 1) (fun _ _ x => Nat.beq x 2) = 0 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k77c : wc (fun σ => (σ 0 = 0 ∧ ∀ p ∈ m22HexadL, σ p ∈ m22HexadL) ∧ σ 3 = 3) I
    (fun x => Nat.beq x 0) (fun _ => inM 655879) (fun _ _ => inM 655879) = 60 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k77d : wc (fun σ => (∀ y ∈ m22HexadL, σ y = y) ∧ σ 3 = 3 ∧ ¬ ∀ x, σ x = x) I
    (fun x => Nat.beq x 0) (fun _ x => Nat.beq x 1) (fun _ _ x => Nat.beq x 2) = 0 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k77e : wc (fun σ => (∀ y ∈ m22HexadL, σ y = y) ∧
      (∀ x, σ (upk22 tB2 x) = upk22 tB2 (σ x)) ∧ ¬ ∀ x, σ x = x) I
    (fun x => Nat.beq x 0) (fun _ x => Nat.beq x 1) (fun _ _ x => Nat.beq x 2) = 0 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

end CertificateChecks.KernelL34

end
