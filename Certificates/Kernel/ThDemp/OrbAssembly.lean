
module

public import Certificates.Kernel.ThDemp.OrbAssemblyBase

public import CFSG.Certificates.Kernel.ThDemp.OrbBound
public import CFSG.Sporadic.Th.Setup
public import Certificates.Kernel.ThDemp.Data
public import Certificates.Kernel.ThDemp.OrbData
public import Certificates.Kernel.ThDemp.OrbFam
import Certificates.Kernel.ThDemp.Assembly
import Certificates.Kernel.ThDemp.OrbInv
import Certificates.Kernel.ThDemp.OrbB0
import Certificates.Kernel.ThDemp.OrbB1
import Certificates.Kernel.ThDemp.OrbB2
import Certificates.Kernel.ThDemp.OrbB3
import Certificates.Kernel.ThDemp.OrbB4
import Certificates.Kernel.ThDemp.OrbB5
import Certificates.Kernel.ThDemp.OrbB6
import Certificates.Kernel.ThDemp.OrbB7
import Certificates.Kernel.ThDemp.OrbB8
import Certificates.Kernel.ThDemp.OrbC
import Certificates.Kernel.ThDemp.OrbK
import Certificates.Kernel.ThDemp.OrbQ
import Certificates.Kernel.ThDemp.OrbE
import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.Certificates.Kernel.ThDemp.ChainEx
public import CFSG.Certificates.Kernel.ThDemp.OrbUnfold

public section

namespace CertificateChecks.KernelThDemp

open CFSG.KC.ThDemp CFSG.KC.Th CFSG.KC.Th.Spec CFSG.Certificates.ThDemp CFSG.Sporadic.Th

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

theorem th_centralizer_bounds
    (hcard : Nat.card J ≤ 90745943887872000) :
    (∃ x : J, 𝕄 x = pkMat (chainEl dempData orbData.x5) ∧ orderOf x = 5 ∧
      Nat.card (Subgroup.centralizer ({x} : Set J)) ≤ 3000) ∧
    (∃ x : J, 𝕄 x = pkMat (chainEl dempData orbData.x31) ∧ orderOf x = 31 ∧
      Nat.card (Subgroup.centralizer ({x} : Set J)) ≤ 31) := by
  have hF := dempChk_facts dempData demp_chk
  have hk := hF.consts
  obtain ⟨hreg, d₀, d₁, hd₀, hd₁, t, ht, huniq, hDc, hlev5⟩ :=
    exists_chain hF (a := a) (b := b) (by rw [a_val, pkMat_SA]) (by rw [b_val, pkMat_SB])
  have hinv := Unfold.invChk_sound inv_ok
  let C : Stab.Ctx dempData orbData J :=
    { d₀ := d₀
      d₁ := d₁
      t := t
      mem := fun l hl i hi => (ht l hl i hi).1
      mat := fun l hl i hi => (ht l hl i hi).2
      uniq := huniq
      inv := fun l hl i hi => by
        have hi64 : i < 64 := by
          obtain ⟨o0, o1, o2, -⟩ := hF.osz
          rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2) with rfl | rfl | rfl <;> omega
        have e := congrArg pkMat (hinv l hl i hi hi64)
        rw [DempData.mul, pkMat_mulB hk, pkMat_one hk, ← (ht l (by omega) i hi).2] at e
        calc pkMat (orbData.TI l i) = (𝕄 (t l i)⁻¹ * 𝕄 (t l i)) * pkMat (orbData.TI l i) := by
              rw [Stab.mat_inv_mul, Matrix.one_mul]
          _ = 𝕄 (t l i)⁻¹ := by rw [Matrix.mul_assoc, e, Matrix.mul_one]
      osz := hF.osz
      md₀ := hd₀
      md₁ := hd₁
      lev5 := hlev5 }
  obtain ⟨⟨x, -, hx, ho, hcx⟩, ⟨y, -, hy, hoy, hcy⟩⟩ :=
    Bound.Ctx.card_centralizer_bounds C hF hreg orb_checks hcard hDc
  exact ⟨⟨x, hx, ho, hcx⟩, ⟨y, hy, hoy, hcy⟩⟩

end CertificateChecks.KernelThDemp

end
