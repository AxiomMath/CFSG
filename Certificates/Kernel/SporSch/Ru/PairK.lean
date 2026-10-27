module

public import Certificates.Data.Kernel.SporSch.RuPair
public import Certificates.Data.Kernel.SporSch.Ru2250K
public import Certificates.Kernel.SporSch.Ru.WitData
public import Certificates.Kernel.SporSch.Ru.Gens
public import Certificates.Kernel.SporSch.Ru.TreePL
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.FactsB1Inputs
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSporSch.RuPair

open CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.RuInv CFSG.KC.Misc.RuPair CFSG.KS.Ru2250
  CFSG.EvenSporadicStandard.RuStd CertificateChecks.KernelSporSch

@[expose] noncomputable def invW (w : List Int) : List Int := (w.map fun z => -z).reverse

@[expose] noncomputable def GP : Nat := wordP RuW.LG RuW.LGI pairWordG

@[expose] noncomputable def HP : Nat := wordP RuW.LG RuW.LGI pairWordH

@[expose] noncomputable def GIP : Nat := wordP RuW.LG RuW.LGI (invW pairWordG)

@[expose] noncomputable def HIP : Nat := wordP RuW.LG RuW.LGI (invW pairWordH)

@[expose] noncomputable def TP : Nat :=
  pwK 4060 12 (mask 12) RuG.A0 RuG.A1 (pidn 4060 12) 64 (pathK RuTree.plK 64 108)

theorem pG : strictB GP (fun G => strictB GIP (fun GI => RuG.pk G GI)) = true := by quickRfl

theorem pH : strictB HP (fun H => strictB HIP (fun HI => RuG.pk H HI)) = true := by quickRfl

theorem comm : strictB GP (fun G => strictB HP (fun H => strictB GIP (fun GI =>
    strictB HIP (fun HI => strictB TP (fun T => commK G H GI HI T RuG.Z))))) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.RuPair

end
