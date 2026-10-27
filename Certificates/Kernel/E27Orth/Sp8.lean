module

public import Certificates.Data.Kernel.E27Orth.Sp
public import Certificates.Kernel.E27Orth.Sp8Data

public section

namespace CertificateChecks.KernelE27Orth.Sp8

open CFSG.KC.Enum CFSG.KC.E27Orth CFSG.KC.Misc.G24

theorem sp8131003_sp : allN 3 (fun j => spOK 8 J (G j)) = true := by decide +kernel

theorem sp8131003_base : baseI (cnF2 8) (oneF2 8) 3 G = true := by decide +kernel

theorem sp8131003_tree : allN 243 (treeI (mulF2 8) (cnF2 8) (oneF2 8) 3 G E Tr) = true := by
  decide +kernel

theorem sp8131003_key : allN 243 (keyI 243 E Ss) = true := by decide +kernel

theorem sp8131003_left : allN 729 (leftI (mulF2 8) 243 G E Lf) = true := by decide +kernel

theorem sp8131003_spB : allN 4 (fun j => spOK 8 J (GB j)) = true := by decide +kernel

theorem sp8131003_baseB : baseI (cnF2 8) (oneF2 8) 4 GB = true := by decide +kernel

theorem sp8131003_treeB : allN 81 (treeI (mulF2 8) (cnF2 8) (oneF2 8) 4 GB EB TrB) = true := by
  decide +kernel

theorem sp8131003_keyB : allN 81 (keyI 81 EB SB) = true := by decide +kernel

theorem sp8131003_leftB : allN 324 (leftI (mulF2 8) 81 GB EB LfB) = true := by decide +kernel

theorem sp8131003_comm : allN 16 (commI 8 4 GB) = true := by decide +kernel

theorem sp8131003_wit : allN 131 (fun w => spOK 8 J (Wg w)) = true := by decide +kernel

theorem sp8131003_cover : allN 243 (coverI 8 (oneF2 8) 81 131 E EB Wg Cv) = true := by
  decide +kernel

end CertificateChecks.KernelE27Orth.Sp8

end
