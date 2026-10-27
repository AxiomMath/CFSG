module

public import Certificates.Data.Kernel.WrTwin
public import Certificates.Data.Holder255.E64Model
public import Certificates.Kernel.WrTwin.Data

public section

namespace CFSG.KD.WrTwin

open CFSG.KC.WrTwin CFSG.ClassicalInvolution.Q3.E64Data CFSG.ClassicalInvolution.Q3.AE

@[expose] def mem64 (σ : Equiv.Perm (Fin 7)) : Bool :=
  decide ((∀ s ∈ fanoLines, s.map σ.toEmbedding ∈ fanoLines ∧ s.map σ⁻¹.toEmbedding ∈ fanoLines) ∧
    Equiv.Perm.sign σ = 1)

@[expose] noncomputable def chain64 : List (List (Equiv.Perm (Fin 7))) := c64.map (·.map cycPerm)

theorem e64_tab : tabOK 28 g64 i64 mG = true := by decide +kernel

theorem e64_id : id14 = enc (1 : Wr 7) := by decide +kernel

theorem e64_rows : e64ConjData.all (rowOK 14 id14 28 g64 i64) = true := by decide +kernel

theorem e64_chain : chainOK mem64 [0, 1, 2] chain64 = true := by decide +kernel

theorem e64_chain_len : (chain64.map List.length).prod = 168 := by decide +kernel

end CFSG.KD.WrTwin

end
