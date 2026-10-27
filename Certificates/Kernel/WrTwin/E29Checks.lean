module

public import Certificates.Data.Kernel.WrTwin
public import Certificates.Data.Holder272.E29Model
public import Certificates.Kernel.WrTwin.Data

public section

namespace CFSG.KD.WrTwin

open CFSG.KC.WrTwin CFSG.ClassicalInvolution.Q3.E29Data CFSG.ClassicalInvolution.Q3.AE

@[expose] def mem29 (σ : Equiv.Perm (Fin 8)) : Bool :=
  decide ((∀ s ∈ affinePlanes, s.map σ.toEmbedding ∈ affinePlanes ∧
    s.map σ⁻¹.toEmbedding ∈ affinePlanes) ∧ Equiv.Perm.sign σ = 1)

@[expose] noncomputable def chain29 : List (List (Equiv.Perm (Fin 8))) := c29.map (·.map cycPerm8)

theorem e29_tab : tabOK 56 g29 i29 nG = true := by decide +kernel

theorem e29_id : id16 = enc (1 : Wr 8) := by decide +kernel

theorem e29_pi : pi8 = enc (Wr.allOnes 8) := by decide +kernel

theorem e29_chain : chainOK mem29 [0, 1, 2, 4] chain29 = true := by decide +kernel

theorem e29_chain_len : (chain29.map List.length).prod = 1344 := by decide +kernel

end CFSG.KD.WrTwin

end
