module

public import Certificates.Kernel.MonsterB.Rem3069.Data

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelMonB.R3069

open CFSG.KC.Rem3069

@[expose] noncomputable def bad (f : Nat → Nat) (c : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (RT c) (f (RT c)) (Nat.beq c 100)

theorem neg_vec : chunkOK (bad fun x => Nat.xor x (Nat.shiftLeft 1 111888)) 100 = false := by
  decide +kernel

theorem neg_big : chunkOK (bad fun x => Nat.lor x (Nat.shiftLeft 1 111966)) 100 = false := by
  decide +kernel

theorem neg_par : chunkOK (bad fun x => Nat.xor x (Nat.shiftLeft 1 111968)) 100 = false := by
  decide +kernel

theorem neg_parN : chunkOK (bad fun x => Nat.lor x (Nat.shiftLeft 16777215 111968)) 100 = false := by
  decide +kernel

theorem neg_gen : chunkOK (bad fun x => Nat.xor x (Nat.shiftLeft 1 111992)) 100 = false := by
  decide +kernel

theorem neg_dep : chunkOK (bad fun x => Nat.xor x (Nat.shiftLeft 1 111994)) 100 = false := by
  decide +kernel

theorem neg_seed :
    chunkOK (fun c => Bool.rec (motive := fun _ => Nat) (RT c)
      (Nat.xor (RT c) (Nat.shiftLeft 1 70336)) (Nat.beq c 79)) 79 = false := by
  decide +kernel

end CertificateChecks.KernelMonB.R3069

end
