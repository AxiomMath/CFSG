module

public import Certificates.Data.Kernel.E27Orth.Orth
public import Certificates.Kernel.E27Orth.O8pData

public section

namespace CertificateChecks.KernelE27Orth.O8p

open CFSG.KC.Enum CFSG.KC.E27Orth CFSG.KC.Misc.G24

theorem o8p131006_om : allN 4 (fun j => omI 8 U (G j) (Y j) (Yi j)) = true := by decide +kernel

theorem o8p131006_base : baseI (cnF2 8) (oneF2 8) 4 G = true := by decide +kernel

theorem o8p131006_tree : allN 243 (treeI (mulF2 8) (cnF2 8) (oneF2 8) 4 G E Tr) = true := by
  decide +kernel

theorem o8p131006_key : allN 243 (keyI 243 E Ss) = true := by decide +kernel

theorem o8p131006_left : allN 972 (leftI (mulF2 8) 243 G E Lf) = true := by decide +kernel

theorem o8p131006_omB : allN 4 (fun j => omI 8 U (GB j) (YB j) (YBi j)) = true := by
  decide +kernel

theorem o8p131006_baseB : baseI (cnF2 8) (oneF2 8) 4 GB = true := by decide +kernel

theorem o8p131006_treeB : allN 81 (treeI (mulF2 8) (cnF2 8) (oneF2 8) 4 GB EB TrB) = true := by
  decide +kernel

theorem o8p131006_keyB : allN 81 (keyI 81 EB SB) = true := by decide +kernel

theorem o8p131006_leftB : allN 324 (leftI (mulF2 8) 81 GB EB LfB) = true := by decide +kernel

theorem o8p131006_comm : allN 16 (commI 8 4 GB) = true := by decide +kernel

theorem o8p131006_wit : allN 131 (fun w => orthI 8 U (Wg w) (Wgi w)) = true := by decide +kernel

theorem o8p131006_cover : allN 243 (coverI 8 (oneF2 8) 81 131 E EB Wg Cv) = true := by
  decide +kernel

end CertificateChecks.KernelE27Orth.O8p

end
