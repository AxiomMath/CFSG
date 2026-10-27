module

public import Certificates.Kernel.OmegaEight.C3850Gen
public import Certificates.Kernel.OmegaEight.C3850Gam
public import Certificates.Kernel.OmegaEight.C3850Chain
public import Certificates.Kernel.OmegaEight.Coset3850
public import Certificates.Kernel.OmegaEight.Split3850K
import CFSG.Certificates.Kernel.O8SplitSound

public section

namespace CertificateChecks.KernelO8.C3850

open CFSG.EvenSmallLie.OmegaEight.NSplit CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.CosetTable in
theorem c3850 : (nsGenCheck .plus = true)
    ∧ (nsGenCheck .minus = true)
    ∧ (nsRelCheck .plus = true)
    ∧ (nsRelCheck .minus = true)
    ∧ (Finite (PG 7 relPG) ∧ Nat.card (PG 7 relPG) ≤ 1451520)
    ∧ (nsChainCheck .plus = true)
    ∧ (nsChainCheck .minus = true)
    ∧ (nsGamCheck .plus = true)
    ∧ (nsGamCheck .minus = true)
    ∧ (nsH1Check .plus = true)
    ∧ (nsH1Check .minus = true)
    ∧ (∃ Y : Array ℕ, splitTest .plus (29 * nM .plus) (fmMat .plus) (iotaMat .plus) Y = true)
    ∧ (∃ Y : Array ℕ, splitTest .minus (29 * nM .minus) (fmMat .minus) (iotaMat .minus) Y = true) :=
  ⟨gen_plus, gen_minus, rel_plus, rel_minus, cosetCard3850, chain_plus, chain_minus, gam_plus,
    gam_minus, h1_plus, h1_minus, CFSG.KC.O8Split.ySplit_sound .plus Split3850.plus_ok,
    CFSG.KC.O8Split.ySplit_sound .minus Split3850.minus_ok⟩

end CertificateChecks.KernelO8.C3850

end
