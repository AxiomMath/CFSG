module

public import Certificates.Data.Kernel.S1277KFr
public import Certificates.Kernel.S1277.ModData
public import Certificates.Kernel.S1277.LatData
public import Certificates.Kernel.S1277.FrData
public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Lce

public section

namespace CFSG.KP.S1277Fr

open CFSG.KC.S1277Lat CFSG.KC.S1277Fr CFSG.KD.S1277Mod CFSG.KD.S1277Lat CFSG.KD.S1277Fr

noncomputable abbrev Mg : Mdl := ⟨24, apg, cpg, ipg, oneg⟩

noncomputable abbrev Mn : Mdl := ⟨48, apn, cpn, ipn, onen⟩

theorem fr_g : frAll Mg (oneg * 64 + 5) nmg ngg ntg sgig sgpg sggg sgrg sgtg sgcg sgdg sgwg sgyg
    sglg = true := by quickRfl

theorem fr_n : frAll Mn (onen * 64 + 5) nmn ngn ntn sgin sgpn sggn sgrn sgtn sgcn sgdn sgwn sgyn
    sgln = true := by quickRfl

end CFSG.KP.S1277Fr

end
