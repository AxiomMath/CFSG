module

public import Certificates.Data.Kernel.S1277KCand
public import Certificates.Kernel.S1277.ModData
public import Certificates.Kernel.S1277.LatData
public import Certificates.Kernel.S1277.CandData
public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Lce

public section

namespace CFSG.KP.S1277Cand

open CFSG.KC.S1277Lat CFSG.KC.S1277Cand CFSG.KD.S1277Mod CFSG.KD.S1277Lat CFSG.KD.S1277Cand

noncomputable abbrev Mg : Mdl := ⟨24, apg, cpg, ipg, oneg⟩

noncomputable abbrev Mn : Mdl := ⟨48, apn, cpn, ipn, onen⟩

theorem nc_g : ncAll Mg (oneg * 64 + 5) nmg ngg ncig nckg = true := by quickRfl
theorem nc_n : ncAll Mn (onen * 64 + 5) nmn ngn ncin nckn = true := by quickRfl
theorem nf_n : nfAll Mn nmn ngn nfin nfxn nfpn nfgn nfrn nftn = true := by quickRfl
theorem v_g : vAll Mg nmg ngg vig vbg = true := by quickRfl
theorem v_n : vAll Mn nmn ngn vin vbn = true := by quickRfl

end CFSG.KP.S1277Cand

end
