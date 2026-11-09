module

public import Certificates.Kernel.J4M2.KDefs2

public section

namespace CertificateChecks.KernelJ4M2

open CFSG.KC.J4Q

theorem j4AndB_assoc (x y z : Bool) : andB (andB x y) z = andB x (andB y z) := by
  cases x <;> cases y <;> cases z <;> rfl

theorem j4AllR_add (a b : Nat) (f : Nat → Bool) :
    allR (a + b) f = andB (allR a f) (allR b fun j => f (a + j)) := by
  induction b with
  | zero => show allR a f = andB (allR a f) true; cases allR a f <;> rfl
  | succ n ih =>
    show andB (allR (a + n) f) (f (a + n)) =
      andB (allR a f) (andB (allR n fun j => f (a + j)) (f (a + n)))
    rw [ih, j4AndB_assoc]

@[expose] noncomputable def nBlkA (k : Nat) : Bool :=
  allR 64 fun j => normM loL hiL loiL hiiL (128 * k + j)

@[expose] noncomputable def nBlkB (k : Nat) : Bool :=
  allR 64 fun j => normM loL hiL loiL hiiL (128 * k + 64 + j)

@[expose] noncomputable def nBlkHiA (k : Nat) : Bool := nBlkA (16 + k)

@[expose] noncomputable def nBlkHiB (k : Nat) : Bool := nBlkB (16 + k)

theorem normBlk_of (k : Nat) (ha : nBlkA k = true) (hb : nBlkB k = true) : normBlk k = true := by
  unfold nBlkA at ha
  unfold nBlkB at hb
  simp only [Nat.add_assoc] at hb
  have h := j4AllR_add 64 64 (fun j => normM loL hiL loiL hiiL (128 * k + j))
  rw [ha, hb] at h
  exact h

theorem normBlkHi_of (k : Nat) (ha : nBlkHiA k = true) (hb : nBlkHiB k = true) :
    normBlkHi k = true :=
  normBlk_of (16 + k) ha hb

end CertificateChecks.KernelJ4M2

end
