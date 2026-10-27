module

public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.PermCent.U43P1Cen
public import Certificates.Data.Kernel.PermCent.U43P1Chk
public import Certificates.Data.Kernel.PermCent.U43QuatEls
public import Certificates.Data.Kernel.QuatPack
meta import Certificates.Data.Kernel.PermCent.U43QuatEls

#kmisc_packarrs CertificateChecks.KernelPermCent.U43Quat.QP
  CFSG.ComponentClassification.HarrisLit.P1.U43.Quat.quatArrs 10

public section

namespace CertificateChecks.KernelPermCent.U43Quat

open CFSG.ComponentClassification.HarrisLit.P1.U43.Cover CFSG.ComponentClassification.HarrisLit.P1.U43.Quat
  CFSG.KC.Enum CFSG.KS CFSG.KC.QuatK CertificateChecks.KernelPermCent.U43P1

@[expose] noncomputable def eP : ℕ := pidn 820 10

@[expose] noncomputable def fr (x : ℕ) : ℕ := pc (QP 14) (pc x (QP 6))

@[expose] noncomputable def rF : ℕ := fr (QP 0)

@[expose] noncomputable def u0F : ℕ := fr (QP 1)

@[expose] noncomputable def v0F : ℕ := fr (QP 2)

@[expose] noncomputable def u1F : ℕ := fr (QP 3)

@[expose] noncomputable def v1F : ℕ := fr (QP 4)

@[expose] noncomputable def w0F : ℕ := fr (QP 7)

@[expose] noncomputable def l0F : List ℕ := q8K 820 10 eP rF u0F v0F

@[expose] noncomputable def l1F : List ℕ := q8K 820 10 eP rF u1F v1F

@[expose] noncomputable def twF : List (ℕ × ℕ) :=
  (l1F.drop 2).map fun x => (pc (pc x u1F) (pc x rF), pc (pc x v1F) (pc x rF))

@[expose] noncomputable def powK (p e : ℕ) : ℕ := Nat.rec (motive := fun _ => ℕ) eP (fun _ q => pc p q) e

@[expose] noncomputable def tPK (k : ℕ) : ℕ := pc (powK (QP 16) (k / 4)) (powK (QP 15) (k % 4))

@[expose] noncomputable def sF (k : ℕ) : ℕ := fr (tPK k)

@[expose] noncomputable def gamF (j : ℕ) : ℕ := pc (QP 14) (QP (8 + j))

@[expose] noncomputable def cfgCoset (k : ℕ) : Bool :=
  cfgScanK 820 10 eP u0F v0F u1F v1F twF CgIn.T 1152 (sF k) (cond (Nat.beq k 2) cfgIdx [])

end CertificateChecks.KernelPermCent.U43Quat

end
