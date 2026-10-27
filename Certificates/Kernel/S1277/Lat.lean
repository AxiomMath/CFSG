module

public import Certificates.Data.Kernel.S1277KLat
public import Certificates.Kernel.S1277.ModData
public import Certificates.Kernel.S1277.LatData
public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Lce

public section

namespace CFSG.KP.S1277Lat

open CFSG.KC.S1277Lat CFSG.KD.S1277Mod CFSG.KD.S1277Lat

noncomputable abbrev Mg : Mdl := ⟨24, apg, cpg, ipg, oneg⟩

noncomputable abbrev Mn : Mdl := ⟨48, apn, cpn, ipn, onen⟩

theorem gen_g : genChk Mg kgg ktg = true := by quickRfl
theorem nodes_g : nodesChk Mg kgg nmg ngg ntg nxg = true := by quickRfl
theorem cls_g : clsChk Mg nmg crg cgg ckg ctg = true := by quickRfl
theorem ox_g : oxChk Mg nmg crg oxg olg = true := by quickRfl
theorem join_g : joinChk Mg nmg ngg crg nmg jtg = true := by quickRfl
theorem bot_g : botChk Mg nmg = true := by quickRfl
theorem quot_g : quotChk Mg nmg nxg olg (abg.getD 0 0) (abg.getD 1 0) = true := by quickRfl

theorem gen_n : genChk Mn kgn ktn = true := by quickRfl
theorem nodes_n : nodesChk Mn kgn nmn ngn ntn nxn = true := by quickRfl
theorem cls_n : clsChk Mn nmn crn cgn ckn ctn = true := by quickRfl
theorem ox_n : oxChk Mn nmn crn oxn oln = true := by quickRfl
theorem join_n : joinChk Mn nmn ngn crn nmn jtn = true := by quickRfl
theorem bot_n : botChk Mn nmn = true := by quickRfl
theorem quot_n : quotChk Mn nmn nxn oln (abn.getD 0 0) (abn.getD 1 0) = true := by quickRfl

end CFSG.KP.S1277Lat

end
