module

public import Certificates.Kernel.Mathieu.RootData
public import CFSG.Certificates.Kernel.Mathieu.ChainSound
public import CFSG.Sporadic.Mathieu.M11
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Schreier.M23Gens
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMathieu

open CFSG.KD.Mathieu CFSG.Monster.B.Mathieu CFSG.KC.MathieuK CFSG.Sporadic.Mathieu
  CFSG.Sporadic.Schreier

theorem root11 : MathieuCertificateK "M11" = some m11RecordK ∧ m11RecordK.chain.check 11 = true ∧
    m11RecordK.chain.orbitSizes 11 = [11, 10, 9, 8] ∧
    m11RecordK.chain.generators = [imageList m11gA, imageList m11gB] := by
  obtain ⟨h1, h2⟩ := chain_of_K (c := m11RecordK.chain) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by quickRfl) (by quickRfl)
    (by decide +kernel) Root11.c0.ok
  exact ⟨rfl, h1, h2.trans (by decide +kernel), by decide +kernel⟩

theorem root12 : MathieuCertificateK "M12" = some m12RecordK ∧ m12RecordK.chain.check 12 = true ∧
    m12RecordK.chain.orbitSizes 12 = [12, 11, 10, 9, 8] ∧
    m12RecordK.chain.generators = [imageList m12gA, imageList m12gB] := by
  obtain ⟨h1, h2⟩ := chain_of_K (c := m12RecordK.chain) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by quickRfl) (by quickRfl)
    (by decide +kernel) Root12.c0.ok
  exact ⟨rfl, h1, h2.trans (by decide +kernel), by decide +kernel⟩

theorem root22 : MathieuCertificateK "M22" = some m22RecordK ∧ m22RecordK.chain.check 22 = true ∧
    m22RecordK.chain.orbitSizes 22 = [22, 21, 20, 16, 3] ∧
    m22RecordK.chain.generators = [imageList m22gA, imageList m22gB] := by
  obtain ⟨h1, h2⟩ := chain_of_K (c := m22RecordK.chain) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by quickRfl) (by quickRfl)
    (by decide +kernel) Root22.c0.ok
  exact ⟨rfl, h1, h2.trans (by decide +kernel), by decide +kernel⟩

theorem root23 : MathieuCertificateK "M23" = some m23RecordK ∧ m23RecordK.chain.check 23 = true ∧
    m23RecordK.chain.orbitSizes 23 = [23, 22, 21, 20, 3, 16] ∧
    m23RecordK.chain.generators = [imageList m23PermA, imageList m23PermB] := by
  obtain ⟨h1, h2⟩ := chain_of_K (c := m23RecordK.chain) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by quickRfl) (by quickRfl)
    (by decide +kernel) Root23.c0.ok
  exact ⟨rfl, h1, h2.trans (by decide +kernel), by decide +kernel⟩

theorem root24 : MathieuCertificateK "M24" = some m24RecordK ∧ m24RecordK.chain.check 24 = true ∧
    m24RecordK.chain.orbitSizes 24 = [24, 23, 22, 21, 20, 16, 3] ∧
    m24RecordK.chain.generators = [imageList m24gA, imageList m24gB] := by
  obtain ⟨h1, h2⟩ := chain_of_K (c := m24RecordK.chain) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by quickRfl) (by quickRfl)
    (by decide +kernel) Root24.c0.ok
  exact ⟨rfl, h1, h2.trans (by decide +kernel), by decide +kernel⟩

end CertificateChecks.KernelMathieu

end
