module

public import CFSG.Blueprint.NativeSporadic
public import Certificates.Kernel.Sporadic.Fi24Cp.All
public import Certificates.Kernel.Sporadic.Fi24Cp.Struct
public import CFSG.Certificates.Kernel.Ssa3FreeSound
public import CFSG.Certificates.Kernel.Ssa3MatSound
import Certificates.Kernel.Sporadic.Fi24Tc.Glue
import Certificates.Kernel.Sporadic.Fi24Br.K
import Certificates.Kernel.Sporadic.Fi24Br.Rels

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.Fi24Cp

open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.Fi24Three
  CFSG.Blueprint CFSG.KC.Ssa3 CFSG.KS.Mat3 CFSG.KD.BrFi24
  CFSG.RankThree.Asc83Table CFSG.RankThree.Asc83Table.Native

theorem cmp_all : ∀ q < SD.qk.length,
    cmpM (val (mat3 781 609961 (RB 23)) (mat3 781 609961 (RB 24)) SD) SD q :=
  cmpM_of_chunks (R := AR) consts rfl CFSG.KD.Fi24Tc.canonA CFSG.KD.Fi24Tc.canonB struct_ok
    nchunks fun c hc => chk_all c hc

theorem facts_all : ∀ g ∈ cpSpec.facts,
    g.Holds (slpRegs (NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed1)
      (NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed2) cpProg) cpNregs := by
  intro g hg
  refine holds_of_factM ssa_ok ?_
  rw [CertificateChecks.KernelSpor.Fi24Rels.mA_eq, CertificateChecks.KernelSpor.Fi24Rels.mB_eq]
  exact factM_of_cover struct_ok cmps_ok cmp_all cover_ok g hg

theorem cp_ok : 2 ≤ cpNregs ∧ cpProg.all (Op.lt cpNregs) = true ∧ cpSpec.wf = true ∧
    cpSpec.rA < cpNregs ∧ cpSpec.rB < cpNregs ∧
    slpRegs (NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed1)
      (NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed2) cpProg cpSpec.rA =
        NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed1 ∧
    slpRegs (NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed1)
      (NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed2) cpProg cpSpec.rB =
        NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed2 ∧
    ∀ f ∈ cpSpec.facts, f.Holds
      (slpRegs (NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed1)
        (NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed2) cpProg) cpNregs :=
  ⟨ssaOK_two ssa_ok, ssaOK_prog ssa_ok, wf_ok, by decide, by decide,
    by rw [slpRegs_of_ssaOK ssa_ok _ _ (by decide), fv0, val.eq_1],
    by rw [slpRegs_of_ssaOK ssa_ok _ _ (by decide), fv1, val.eq_2], facts_all⟩

theorem nofun_ok : cpSpec.noFun = true := by decide +kernel

end CFSG.KD.Fi24Cp

end
