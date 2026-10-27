module

public import Certificates.Data.Kernel.Misc.Sp6
public import Certificates.Kernel.Misc.Sp6Data
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneOqDataSylow
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.ON.Gen
public import Mathlib.Data.Nat.Bitwise

public section

set_option maxRecDepth 100000

namespace CFSG.KD.Misc.Sp6

open CFSG.KC.Misc CFSG.KC.Misc.Sp6 CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne

theorem treeF : treeK 0 (pGens false) PF PQF PParF PGenF PDepF = true := by quickRfl
theorem invF : invChk PF PQF IVF IVIF CMF = true := by quickRfl
theorem tabsF : tabsK 0 (nthN XEL) (nthN XVL) Q0F = true := by quickRfl
theorem lenF : Nat.beq (lenN ELF) 241 = true := by quickRfl

theorem treeT : treeK 1 (pGens true) PT PQT PParT PGenT PDepT = true := by quickRfl
theorem invT : invChk PT PQT IVT IVIT CMT = true := by quickRfl
theorem tabsT : tabsK 1 (nthN XEL) (nthN XVL) Q0T = true := by quickRfl
theorem lenT : Nat.beq (lenN ELT) 161 = true := by quickRfl

@[expose] noncomputable def closFc (c : Nat) : Bool := closK PQF (16 * c) 16

@[expose] noncomputable def eaFc (c : Nat) : Bool :=
  eaChunk 0 12 (nthN XEL) (nthN XVL) Q0F PQF IVF IVIF CMF ELF ELParF ELExtF (16 * c) 16

@[expose] noncomputable def closTc (c : Nat) : Bool := closK PQT (16 * c) 16

@[expose] noncomputable def eaTc (c : Nat) : Bool :=
  eaChunk 1 9 (nthN XEL) (nthN XVL) Q0T PQT IVT IVIT CMT ELT ELParT ELExtT (16 * c) 16

end CFSG.KD.Misc.Sp6

set_option Elab.async false

#kon_slices CFSG.KD.Misc.Sp6.closFc 0 8
#kon_join CFSG.KD.Misc.Sp6.closF CFSG.KD.Misc.Sp6.closFc 8
#kon_slices CFSG.KD.Misc.Sp6.eaFc 0 16
#kon_join CFSG.KD.Misc.Sp6.eaF CFSG.KD.Misc.Sp6.eaFc 16
#kon_slices CFSG.KD.Misc.Sp6.closTc 0 8
#kon_join CFSG.KD.Misc.Sp6.closT CFSG.KD.Misc.Sp6.closTc 8
#kon_slices CFSG.KD.Misc.Sp6.eaTc 0 11
#kon_join CFSG.KD.Misc.Sp6.eaT CFSG.KD.Misc.Sp6.eaTc 11

end
