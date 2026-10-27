module

public import Certificates.Data.Kernel.E64FactsK
public import Certificates.Kernel.E64Aut.Checks

public noncomputable section

namespace CFSG.KD.E64FactsK

open CFSG.KC.WrTwin CFSG.KC.E64AutK CFSG.KC.E64FactsK CFSG.KD.E64Aut
  CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr Certificates.AE117
  Certificates.E64Aut Certificates.E64Facts

theorem e64f_cent : fanoLines.all (fun ℓ =>
    centCOK pi14 P168 V64 ((memSK ℓ).map enc) ((centK ℓ).map enc)) = true := by
  decide +kernel

theorem e64f_g1 : fanoLines.all (fun ℓ =>
    (centK ℓ).all (fun c => inM c && commP pi14 (enc c) ((memSK ℓ).map enc)) &&
    decide ((centK ℓ).length = 8) &&
    decide (((centK ℓ).map enc).Pairwise fun c d => inModPi pi14 c [d] = false) &&
    ((centK ℓ).map enc).all (fun c => Nat.beq (pm c c) e14) &&
    ((centK ℓ).map enc).all fun c => ((centK ℓ).map enc).all fun d =>
      Nat.beq (pm c d) (pm d c)) = true := by
  decide +kernel

theorem e64f_g2 : (fanoLines.all fun ℓ => fanoLines.all fun ℓ' => decide (ℓ = ℓ') ||
    ((centK ℓ).map enc).all fun c => !commP pi14 c ((memSK ℓ').map enc) ||
      inModPi pi14 c [e14] || inModPi pi14 c ((a7 ()).map enc)) &&
    decide (((a7 ()).map enc).Pairwise fun c d => inModPi pi14 c [d] = false) &&
    (a7 ()).all (fun a => inM a && Nat.beq (pm (enc a) (enc a)) e14 &&
      !inModPi pi14 (enc a) [e14] &&
      decide ((fanoLines.filter fun ℓ => commP pi14 (enc a) ((memSK ℓ).map enc)).length = 3)) =
    true := by
  decide +kernel

theorem e64f_conj : conjCheck () = true := by
  decide +kernel

end CFSG.KD.E64FactsK

end
