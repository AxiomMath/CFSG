module

public import CFSG.Certificates.Kernel.RouteP.TextLinesJoin
public import Certificates.Kernel.RouteP.Text.CoverGensC0
public import Certificates.Kernel.RouteP.Text.CoverGensC1
public import Certificates.Kernel.RouteP.Text.CoverGensC2
public import Certificates.Kernel.RouteP.Text.CoverGensC3
public import Certificates.Kernel.RouteP.Text.CoverGensC4
public import CFSG.Certificates.Kernel.Common.ForallTree
meta import CFSG.Certificates.Kernel.Common.ForallTree

public section

namespace CertificateChecks.KernelRouteP

open CFSG.KC CFSG.KC.RouteP CFSG.KD.RouteP CFSG.KS.RouteP
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native

#kc_forall_tree pcg_all (fun j => CertificateChecks.KernelRouteP.pcgPc j = true) 38
  CertificateChecks.KernelRouteP.pcgPc

theorem pcg_chars : PCG.chars = pcgCs.flatten := by
  simp only [PCG.chars, pcgCs, List.flatten_cons, List.flatten_nil, List.append_nil]

theorem cg_chk : nlChk CGD (fun _ => 306936) (PCG.chars.map Char.toNat) 0 0 0 0 0 1 (nlEnd 4) =
    true := by
  rw [pcg_chars]
  exact nlChk_chunks CGD (fun _ => 306936) (nlEnd 4) pcgCs pcgSt (fun j hj => pcg_all j hj)
    (by decide +kernel)

theorem coverGens_lines : (numLines coverGensText).size = 4 ∧ ∀ k < 4,
    ((numLines coverGensText)[k]!).size = 306936 ∧
      ∀ p < 306936, ((numLines coverGensText)[k]!)[p]! = UInt32.ofNat (CGD k p) := by
  rw [PCG.eq]
  exact numLines_of_chk CGD (fun _ => 306936) cg_chk

end CertificateChecks.KernelRouteP
