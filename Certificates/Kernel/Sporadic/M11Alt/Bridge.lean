module

public import Certificates.Kernel.Sporadic.M11Alt.Check
public import CFSG.Certificates.Kernel.Spor.M11Sound
public import CFSG.Certificates.Kernel.Spor.M11ClassSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Schreier.M11Data

public section

namespace CertificateChecks.KernelSpor.M11Alt

open CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Monster.B.Mathieu
  CertificateChecks.KernelSpor.M11

theorem tA_eq : tA = imageList m11gA := by decide

theorem tB_eq : tB = imageList m11gB := by decide

theorem W_eq : W = [[1], [2]] ++ m11Words.map (List.map CFSG.KS.M11.shiftLabel) := by decide

set_option maxRecDepth 100000 in
theorem bX : CFSG.KS.M11.pairsBdd 44 XL = true := by quickRfl

set_option maxRecDepth 100000 in
theorem bY : CFSG.KS.M11.pairsBdd 44 Y = true := by quickRfl

set_option maxRecDepth 100000 in
theorem pairs : CFSG.KS.M11.pairCntL XL Y = 15840 := by
  rw [CFSG.KS.M11Class.pairCntL_class cls, Nat.eq_of_beq_eq_true row]
  rfl

set_option maxRecDepth 20000 in
theorem counts :
    (m11Certificate.check = true ∧ m11Certificate.orderCertificate = 7920)
    ∧ (orderIs m11gA 2 = true ∧ orderIs m11gB 4 = true ∧ orderIs (m11gA * m11gB) 11 = true ∧
      orderIs (m11gA * m11gB * m11gA⁻¹ * m11gB⁻¹) 6 = true ∧
      (m11Elements.filter (orderIs · 2)).length = 165 ∧
      (m11Elements.filter (orderIs · 4)).length = 990 ∧
      ((m11Elements.filter (orderIs · 2) ×ˢ m11Elements.filter (orderIs · 4)).filter
        fun q => orderIs (q.1 * q.2) 11 && orderIs (q.1 * q.2 * q.1⁻¹ * q.2⁻¹) 6).length =
        15840) := by
  have h := CFSG.KS.M11.m11K_sound (gA := m11gA) (gB := m11gB) (words := m11Words)
    (hbs := by decide) tA_eq tB_eq W_eq base (Nat.eq_of_beq_eq_true colX)
    (Nat.eq_of_beq_eq_true colY) bX bY
  obtain ⟨⟨h1, h2⟩, h3, h4, h5, h6, h7, h8, h9⟩ := h
  have hXn : XL.length = 165 := rfl
  have hYn : Y.length = 990 := rfl
  exact ⟨⟨h1, h2⟩, h3, h4, h5, h6, h7.trans hXn, h8.trans hYn, h9.trans pairs⟩

end CertificateChecks.KernelSpor.M11Alt

end
