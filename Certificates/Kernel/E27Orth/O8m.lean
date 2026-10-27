module

public import Certificates.Data.Kernel.E27Orth.Orth
public import Certificates.Kernel.E27Orth.O8mData

public section

namespace CertificateChecks.KernelE27Orth.O8m

open CFSG.KC.Enum CFSG.KC.E27Orth CFSG.KC.Misc.G24

theorem o8m131004_om : allN 4 (fun j => omI 8 U (G j) (Y j) (Yi j)) = true := by decide +kernel

theorem o8m131004_base : baseI (cnF2 8) (oneF2 8) 4 G = true := by decide +kernel

theorem o8m131004_tree : allN 81 (treeI (mulF2 8) (cnF2 8) (oneF2 8) 4 G E Tr) = true := by
  decide +kernel

theorem o8m131004_key : allN 81 (keyI 81 E Ss) = true := by decide +kernel

theorem o8m131004_left : allN 324 (leftI (mulF2 8) 81 G E Lf) = true := by decide +kernel

theorem o8m131004_cen : allN 81 (cenI 8 (oneF2 8) 4 4 G E) = true := by decide +kernel

theorem o8m131004_fs : allN 81 (fsI 8 (oneF2 8) 4 8 E Fl Fm) = true := by decide +kernel

theorem o8m131004_pair : allN 64 (pairI 8 (oneF2 8) 4 8 E Fl Pw) = true := by decide +kernel

end CertificateChecks.KernelE27Orth.O8m

end
