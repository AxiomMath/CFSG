module

public import Certificates.Data.Kernel.E27Orth.Orth
public import Certificates.Kernel.E27Orth.O10pData

public section

namespace CertificateChecks.KernelE27Orth.O10p

open CFSG.KC.Enum CFSG.KC.E27Orth CFSG.KC.Misc.G24

theorem o10p131007_om : allN 3 (fun j => omI 10 U (G j) (Y j) (Yi j)) = true := by
  decide +kernel

theorem o10p131007_base : baseI (cnF2 10) (oneF2 10) 3 G = true := by decide +kernel

theorem o10p131007_tree : allN 243 (treeI (mulF2 10) (cnF2 10) (oneF2 10) 3 G E Tr) = true := by
  decide +kernel

theorem o10p131007_key : allN 243 (keyI 243 E Ss) = true := by decide +kernel

theorem o10p131007_left : allN 729 (leftI (mulF2 10) 243 G E Lf) = true := by decide +kernel

theorem o10p131007_omB : allN 4 (fun j => omI 10 U (GB j) (YB j) (YBi j)) = true := by
  decide +kernel

theorem o10p131007_baseB : baseI (cnF2 10) (oneF2 10) 4 GB = true := by decide +kernel

theorem o10p131007_treeB : allN 81 (treeI (mulF2 10) (cnF2 10) (oneF2 10) 4 GB EB TrB) = true := by
  decide +kernel

theorem o10p131007_keyB : allN 81 (keyI 81 EB SB) = true := by decide +kernel

theorem o10p131007_leftB : allN 324 (leftI (mulF2 10) 81 GB EB LfB) = true := by decide +kernel

theorem o10p131007_comm : allN 16 (commI 10 4 GB) = true := by decide +kernel

theorem o10p131007_wit : allN 131 (fun w => orthI 10 U (Wg w) (Wgi w)) = true := by
  decide +kernel

theorem o10p131007_cover : allN 243 (coverI 10 (oneF2 10) 81 131 E EB Wg Cv) = true := by
  decide +kernel

end CertificateChecks.KernelE27Orth.O10p

end
