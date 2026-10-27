
module

public import CFSG.Monster.B.TwoA.Sp8.QuadCosetCInputs
public import Certificates.Kernel.MonsterB.Quad3078Data

public section

namespace CertificateChecks.KernelMonB.Quad3078

open CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B CFSG.Monster.Code CFSG.KC.Q3078 CFSG.KD.Q3078

theorem cImg_ok : ∀ k < 44,
    (h1ConjN k (false, 0, 127) = Model.Pauli.mul (false, 0, 127) (foldP (cImg k)) ∨
      h1ConjN k (false, 0, 127) = Model.Pauli.mul (false, 0, 127)
        (foldP (cImg k + Pi.single 7 1))) ∧
    cImg k 7 = 0 := by
  decide +kernel

theorem qPoly_ok : ∀ n < 256, qPoly (bvec 8 n) = if qN n then 1 else 0 := by decide +kernel

theorem zm_ok : ∀ n < 256, ZM.testBit n = !qN n := by decide +kernel

theorem rows_ok : ∀ k < 44, ∀ j < 8, byteK RW (8 * k + j) = genRow k j := by decide +kernel

theorem tri_ok : ∀ j < 8, byteK RW (8 * 44 + j) = triRows.getD j 0 := by decide +kernel

theorem trans_ok : ∀ k < 44, byteK CK k = cRows.getD k 256 - 256 := by decide +kernel

theorem trans44 : byteK CK 44 = 0 := by decide +kernel

end CertificateChecks.KernelMonB.Quad3078

end
