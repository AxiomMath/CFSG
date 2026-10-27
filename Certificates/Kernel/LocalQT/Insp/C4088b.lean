module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM22Orb
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM23Data

set_option maxRecDepth 100000
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4088

open scoped Pointwise
open CFSG.QuasithinUnique.Vol2Native.L239 CFSG.QuasithinUnique.Vol2Native.L239.M23Insp
  CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.X1

theorem H_nodup : data.H.Nodup := by decide +kernel
theorem cover : AllMem data.H (fun B => B ≠ data.B₀ → B ∈ data.R₁ ∨ B ∈ data.R₂) := by
  decide +kernel
theorem lev₁ : AllMem data.H
    (fun B => B ≠ data.B₀ → (B ∈ data.R₁ ↔ (B ∩ data.B₀).card = data.c₁)) := by decide +kernel
theorem lev₂ : AllMem data.H
    (fun B => B ≠ data.B₀ → (B ∈ data.R₂ ↔ (B ∩ data.B₀).card = data.c₂)) := by decide +kernel
theorem Es_comm : ∀ e ∈ data.Es, ∀ f ∈ data.Es, e * f = f * e := by decide +kernel

end CFSG.KD.LQT.C4088

end
