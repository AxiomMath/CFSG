
module

public import Certificates.Kernel.Fin76bAut.Facts
public import Certificates.Kernel.Fin76bAut.Tab
public import CFSG.Certificates.Kernel.Fin76bAut.Card
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CertificateChecks.KernelFin76bAut

open CFSG.KS.EAut CFSG.EvenSporadicStandard.Fin76b CFSG.EvenSporadicStandard.Fin76b.AutETable
  CFSG.EvenSporadicStandard.Fin76b.W16

theorem card_mulAut_le_of_realizes {H : Type*} [Group H] {M : Array (Array ℕ)} {elt : ℕ → H}
    (R : Realizes H 32 M elt) (hM : ∀ a < 32, ∀ b < 32, mt M a b = mulE0 a b) :
    Nat.card (MulAut H) ≤ 1920 :=
  card_aut_le R (fun a ha b hb => (hM a ha b hb).trans (eTabK_spec ch24614Tab a ha b hb).symm)
    ch24614Tup

end CertificateChecks.KernelFin76bAut

end
