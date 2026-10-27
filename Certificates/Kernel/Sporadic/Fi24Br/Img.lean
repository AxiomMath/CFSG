
module

public import Certificates.Kernel.Sporadic.Fi24Br.Rels
public import Certificates.Kernel.VecCert.WordProgX
public import Certificates.Data.Kernel.Spor.Fi24Img
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.Fi24Br.Light
import CFSG.Certificates.Kernel.Orders.Fi24p.RelsBind

public section

namespace CertificateChecks.KernelSpor.Fi24Img

open CFSG.KC.Ord CFSG.KD.BrFi24 CFSG.KS.Mat3 CertificateChecks.KernelSpor.Fi24Rels

theorem leaf_eq : ∀ k < 11, CFSG.KD.Fi24Img.MT k = RB (Nat.succ k) :=
  all11 (p := fun k => CFSG.KD.Fi24Img.MT k = RB (Nat.succ k))
    (Nat.eq_of_beq_eq_true (by quickRfl)) (Nat.eq_of_beq_eq_true (by quickRfl))
    (Nat.eq_of_beq_eq_true (by quickRfl)) (Nat.eq_of_beq_eq_true (by quickRfl))
    (Nat.eq_of_beq_eq_true (by quickRfl)) (Nat.eq_of_beq_eq_true (by quickRfl))
    (Nat.eq_of_beq_eq_true (by quickRfl)) (Nat.eq_of_beq_eq_true (by quickRfl))
    (Nat.eq_of_beq_eq_true (by quickRfl)) (Nat.eq_of_beq_eq_true (by quickRfl))
    (Nat.eq_of_beq_eq_true (by quickRfl))

theorem img_eq : ∀ k < 11, CFSG.KD.Fi24Img.img k = mat3 781 609961 (RB (k + 1)) := by
  intro k hk
  rw [CFSG.KD.Fi24Img.img, leaf_eq k hk]

theorem bridge_x : ∃ x : Nat → GL (Fin 781) (ZMod 3),
    (∀ k < 11, (x k : Matrix (Fin 781) (Fin 781) (ZMod 3)) = CFSG.KD.Fi24Img.img k) ∧
    (∀ k, 11 ≤ k → x k = 1) ∧
    (∀ v ∈ TauCeti.Sporadic.fi24PrimePresentation.relatorLetters,
      CFSG.Sporadic.Bridge.wordProd x v = 1) ∧
    ∀ g : GL (Fin 781) (ZMod 3),
      g.val = CFSG.Blueprint.NativeSporadic.decode 3 781 1
          CFSG.Blueprint.NativeSporadic.Fi24primeSeed1 ∨
        g.val = CFSG.Blueprint.NativeSporadic.decode 3 781 1
          CFSG.Blueprint.NativeSporadic.Fi24primeSeed2 →
      g ∈ Subgroup.closure (x '' Set.Iio 11) := by
  obtain ⟨x, hx, h1, hrel', hcl⟩ :=
    CertificateChecks.KernelWPX.units_of_cover hs hroot hinv relB hrel hregs
  refine ⟨x, fun k hk => (hx k hk).trans (img_eq k hk).symm, h1, ?_, ?_⟩
  · rw [CFSG.KD.OrdFi24p.rels_eq]
    exact hrel'
  · rintro g (h | h)
    · exact hcl 23 (by norm_num) (by norm_num) g (h.trans mA_eq)
    · exact hcl 24 (by norm_num) (by norm_num) g (h.trans mB_eq)

end CertificateChecks.KernelSpor.Fi24Img

end
