module

public import Certificates.Kernel.VecCert.Co1Bound
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSpor.Co1Rels

open CFSG.KC.Ord CFSG.KS.Ord CFSG.Sporadic.SmallF2 CFSG.KD.OrdCo1 CertificateChecks.KernelVec
  CertificateChecks.KernelVec.Co1Bound

theorem le_range : ∃ φ : TauCeti.Sporadic.co1Presentation.Group →*
      GL (Fin (CFSG.Sporadic.Co1.Native.co1Data ()).d) (ZMod 2),
    J CFSG.Sporadic.Co1.Native.co1Data ≤ φ.range := by
  have hab := (andB_iff _ _).1 hAB
  have hab1 := (andB_iff _ _).1 hab.1
  have hab2 := (andB_iff _ _).1 hab.2
  have hA := (andB_iff _ _).1 hab1.1
  have hB := (andB_iff _ _).1 hab1.2
  exact le_range_of_hom _ TauCeti.Sporadic.co1Presentation (hnb := rfl) consts rels_eq gens_eq
    hroots hinv relB hr regs (lt_of_blt hA.1) (lt_of_blt hA.2)
    (lt_of_blt hB.1) (lt_of_blt hB.2) (Nat.eq_of_beq_eq_true hab2.1)
    (Nat.eq_of_beq_eq_true hab2.2) mA_eq mB_eq

theorem neg_rel : notB (relOK RH (mulR 2 6 144 24 4 L H CM RM) [[(0, true)]] 8 ONE 0) = true := by
  quickRfl

end CertificateChecks.KernelSpor.Co1Rels

end
