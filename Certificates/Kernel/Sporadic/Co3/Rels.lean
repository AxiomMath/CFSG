module

public import Certificates.Kernel.VecCert.Co3Bound
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSpor.Co3Rels

open CFSG.KC.Ord CFSG.KS.Ord CFSG.Sporadic.SmallF2 CFSG.KD.OrdCo3 CertificateChecks.KernelVec
  CertificateChecks.KernelVec.Co3Bound

theorem le_range : ∃ φ : TauCeti.Sporadic.co3Presentation.Group →*
      GL (Fin (CFSG.Sporadic.Co3.Native.co3Data ()).d) (ZMod 2),
    J CFSG.Sporadic.Co3.Native.co3Data ≤ φ.range := by
  have hab := (andB_iff _ _).1 hAB
  have hab1 := (andB_iff _ _).1 hab.1
  have hab2 := (andB_iff _ _).1 hab.2
  have hA := (andB_iff _ _).1 hab1.1
  have hB := (andB_iff _ _).1 hab1.2
  have hre : TauCeti.Sporadic.co3Presentation.relatorLetters = rels := by
    rw [CFSG.KBRoute.Co3Alt.rels_eq, rels_eq]
  exact le_range_of_hom _ TauCeti.Sporadic.co3Presentation (hnb := rfl) consts hre gens_eq
    hroots hinv relB hr regs (lt_of_blt hA.1) (lt_of_blt hA.2)
    (lt_of_blt hB.1) (lt_of_blt hB.2) (Nat.eq_of_beq_eq_true hab2.1)
    (Nat.eq_of_beq_eq_true hab2.2) mA_eq mB_eq

theorem neg_rel : notB (relOK RH (mulR 2 6 132 22 4 L H CM RM) [[(0, true)]] 7 ONE 0) = true := by
  quickRfl

end CertificateChecks.KernelSpor.Co3Rels

end
