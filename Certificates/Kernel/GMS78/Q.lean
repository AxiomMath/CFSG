module

public import CFSG.Certificates.Kernel.GMS78RuSound
public import Certificates.Kernel.GMS78.Gen
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
import Batteries.Tactic.Init

public section

namespace CertificateChecks.KernelGMS78

open CFSG.KC.GMS

@[expose] noncomputable def QT : Nat := nat_lit 1117201878843361681494085987627740835461300345721927342519310045770204599344304097568244122331803109032201145496153667223143149957524859295310471942760100240804453086901176361639740752826270395980996490502201418267086752034788704256

@[expose] noncomputable def SD : Nat := nat_lit 392586423483308803097144965832347045703274095265415454248072594466191489354256191581049671306235662201471003649388316641497358783231613079446459756189709347812152340902202479397070252872651123688436299595849396664181452451831395575407650835494268173824435626434950833340858130533526488922753379995264329692814785884451969409405060207

theorem bindMul_ok : bindMul CFSG.GMS78Ru.mulTab = true := by quickRfl
theorem mul_ok : mulOK = true := by quickRfl
theorem pairs_ok : pairsOK = true := by quickRfl
theorem bindSpec_ok : bindSpec CFSG.GMS78Ru.specialList = true := by quickRfl
theorem bindQ_ok : bindQ CFSG.GMS78RuQ.qTab QT = true := by quickRfl
theorem bindSD_ok : bindSD CFSG.GMS78RuSim.steinData SD = true := by quickRfl
theorem q0_ok : kQ0 QT SD = true := by quickRfl

theorem q0Check_eq : CFSG.GMS78RuQ.q0Check = true := by
  rw [q0_eq]
  exact q0_sound _ _ _ bindMul_ok bindQ_ok bindSD_ok q0_ok

end CertificateChecks.KernelGMS78

end
