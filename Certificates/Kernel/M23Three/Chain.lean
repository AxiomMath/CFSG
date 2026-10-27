module

public import Certificates.Kernel.M23Three.Data
public import Certificates.Data.M23ThreeKD
public import Certificates.Data.Kernel.PermCent.SmallB

public section

namespace CertificateChecks.KernelM23Three

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.LocalAnalysis.GLTheoremA.KD264M23
  CFSG.Certificates.Kernel.PkCV

@[expose] def decI (c : Nat) : Int :=
  if c % 2 = 0 then ((c / 2 + 1 : Nat) : Int) else -((c / 2 + 1 : Nat) : Int)

@[expose] noncomputable def baseV : Vector (Fin 23) 6 :=
  ⟨(base.map fun k => (Fin.ofNat 23 k : Fin 23)).toArray, by decide⟩

@[expose] noncomputable def QF : RawSchreierDatum 23 :=
  certificate (by decide) m23S (words.map (List.map decI)) baseV (by decide)

@[expose] noncomputable def wW : List Int := w.map decI

@[expose] noncomputable def genC : List (CV 23) := m23S.map cOf

@[expose] noncomputable def zC : CV 23 := evCodesB genC zW
@[expose] noncomputable def m1C : CV 23 := evCodesB genC m1W
@[expose] noncomputable def m2C : CV 23 := evCodesB genC m2W
@[expose] noncomputable def m3C : CV 23 := evCodesB genC m3W
@[expose] noncomputable def wC : CV 23 := evCodesB genC wW

@[expose] noncomputable def relC : Bool :=
  decide (zC ^ 3 = 1) && !decide (zC = 1) && decide (m1C ^ 3 = 1) && decide (m2C ^ 2 = 1) &&
    decide (m3C ^ 2 = 1) && decide ((m1C * m2C) ^ 3 = 1) && decide ((m2C * m3C) ^ 3 = 1) &&
    decide ((m1C * m3C) ^ 2 = 1) && !decide (m1C = 1) && decide (m1C * zC = zC * m1C) &&
    decide (m2C * zC = zC * m2C) && decide (m3C * zC = zC * m3C) &&
    decide (wC * zC * wC⁻¹ = zC * zC)

@[expose] noncomputable def fixC : Bool :=
  (List.finRange 23).all fun x => decide (ev zC x = x) == decide (x ∈ QF.base.toList.take 5)

end CertificateChecks.KernelM23Three
