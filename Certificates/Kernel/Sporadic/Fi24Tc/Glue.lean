module

public import CFSG.Blueprint.NativeSporadic
public import Certificates.Kernel.Sporadic.Fi24Tc.All
public import Certificates.Kernel.Sporadic.Fi24Tc.Struct
public import CFSG.Certificates.Kernel.Ssa3FreeSound
public import CFSG.Certificates.Kernel.Ssa3MatSound
import Certificates.Kernel.Sporadic.Fi24Br.D
import Certificates.Kernel.Sporadic.Fi24Br.K
import Certificates.Kernel.Sporadic.Fi24Br.Rels
import CFSG.Certificates.Kernel.Spor.Dec3Sound

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.Fi24Tc

open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.Fi24Three
  CFSG.Blueprint CFSG.KC.Ssa3 CFSG.KS.Mat3 CFSG.KD.BrFi24
  CFSG.RankThree.Asc83Table CFSG.RankThree.Asc83Table.Native

theorem canonA : Canon3 609961 (RB 23) := CFSG.KS.Dec3.seedDone3_canon (by decide +kernel) d1_end

theorem canonB : Canon3 609961 (RB 24) := CFSG.KS.Dec3.seedDone3_canon (by decide +kernel) d2_end

theorem cmp_all : ∀ q < SD.qk.length,
    cmpM (val (mat3 781 609961 (RB 23)) (mat3 781 609961 (RB 24)) SD) SD q :=
  cmpM_of_chunks (R := AR) consts rfl canonA canonB struct_ok nchunks fun c hc => chk_all c hc

theorem facts_all : ∀ g ∈ tcSpec.facts,
    g.Holds (slpRegs (NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed1)
      (NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed2) tcProg) tcNregs := by
  intro g hg
  refine holds_of_factM ssa_ok ?_
  rw [CertificateChecks.KernelSpor.Fi24Rels.mA_eq, CertificateChecks.KernelSpor.Fi24Rels.mB_eq]
  exact factM_of_cover struct_ok cmps_ok cmp_all cover_ok g hg

theorem seedA_reg : slpRegs (NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed1)
    (NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed2) tcProg tcSpec.rA =
      NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed1 := by
  rw [slpRegs_of_ssaOK ssa_ok _ _ (by decide), fv0, val.eq_1]

theorem seedB_reg : slpRegs (NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed1)
    (NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed2) tcProg tcSpec.rB =
      NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed2 := by
  rw [slpRegs_of_ssaOK ssa_ok _ _ (by decide), fv1, val.eq_2]

theorem head : 2 ≤ tcNregs ∧ tcProg.all (Op.lt tcNregs) = true ∧ tcSpec.wf = true ∧
    tcSpec.rA < tcNregs ∧ tcSpec.rB < tcNregs ∧
    slpRegs (NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed1)
      (NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed2) tcProg tcSpec.rA =
        NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed1 ∧
    slpRegs (NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed1)
      (NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed2) tcProg tcSpec.rB =
        NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed2 ∧
    ∀ f ∈ tcSpec.facts.take 170, f.Holds
      (slpRegs (NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed1)
        (NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed2) tcProg) tcNregs :=
  ⟨ssaOK_two ssa_ok, ssaOK_prog ssa_ok, wf_ok, by decide, by decide, seedA_reg, seedB_reg,
    fun g hg => facts_all g (List.mem_of_mem_take hg)⟩

theorem tail : ∀ f ∈ tcSpec.facts.drop 170, f.Holds
    (slpRegs (NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed1)
      (NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed2) tcProg) tcNregs :=
  fun g hg => facts_all g (List.mem_of_mem_drop hg)

end CFSG.KD.Fi24Tc

end
