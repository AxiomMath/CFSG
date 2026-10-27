module

public import CFSG.Blueprint.NativeSporadic
public import Certificates.Kernel.Sporadic.Fi24Alpha.All
public import Certificates.Kernel.Sporadic.Fi24Alpha.Struct
public import CFSG.Certificates.Kernel.Ssa3FreeSound
public import CFSG.Certificates.Kernel.Ssa3MatSound
import Certificates.Kernel.Sporadic.Fi24Tc.Glue
import Certificates.Kernel.Sporadic.Fi24Br.K
import Certificates.Kernel.Sporadic.Fi24Br.Rels
import Certificates.Kernel.AlphaMc.Fi24DataGlue
import CFSG.Certificates.Kernel.AlphaFunKSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaOrbDefs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.Fi24Alpha

open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaFi24
  CFSG.Blueprint CFSG.KC.Ssa3 CFSG.KS.Mat3 CFSG.KD.BrFi24
  CFSG.RankThree.Asc83Table CFSG.RankThree.Asc83Table.Native CertificateChecks.KernelAM.Fi24

theorem cmp_all : ∀ q < SD.qk.length,
    cmpM (val (mat3 781 609961 (RB 23)) (mat3 781 609961 (RB 24)) SD) SD q :=
  cmpM_of_chunks (R := AR) consts rfl CFSG.KD.Fi24Tc.canonA CFSG.KD.Fi24Tc.canonB struct_ok
    nchunks fun c hc => chk_all c hc

theorem facts_all : ∀ g ∈ fi24Mod.modFactsW 3 fi24Tops,
    g.Holds (slpRegs (NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed1)
      (NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed2) fi24Prog) fi24Nregs := by
  intro g hg
  refine holds_of_factM ssa_ok ?_
  rw [CertificateChecks.KernelSpor.Fi24Rels.mA_eq, CertificateChecks.KernelSpor.Fi24Rels.mB_eq]
  exact factM_of_cover struct_ok cmps_ok cmp_all cover_ok g hg

theorem mod_ok : 2 ≤ fi24Nregs ∧ fi24Prog.all (Op.lt fi24Nregs) = true ∧
    (∀ f ∈ fi24Mod.modFactsW 3 fi24Tops, f.Holds
      (slpRegs (NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed1)
        (NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed2) fi24Prog) fi24Nregs) ∧
    fi24Mod.wfO 3 fi24Orb = true ∧ pcWf (fi24Tops ++ fi24Mod.basisPc 3) = true ∧
    fi24Tops.all (fun g => fi24Mod.acts.any (·.reg == g.reg)) = true ∧
    fi24Mod.wOK 3 fi24Tops fi24Tidx 16 = true ∧ 3 ≤ fi24Mod.basis.length ∧
    fi24Mod.funOK 3 fi24Cf = true ∧ fi24Mod.altOK 3 fi24Ci fi24Ct tgtAlt = true :=
  ⟨ssaOK_two ssa_ok, ssaOK_prog ssa_ok, facts_all, w_wfO, w_pc, w_top, w_wOK, by decide,
    funOK_of_funW (fun _ _ _ => rfl) w_fun,
    altOK_of_altW (fun _ _ _ _ _ => rfl) (fun _ _ _ _ => rfl) w_alt⟩

end CFSG.KD.Fi24Alpha

end
