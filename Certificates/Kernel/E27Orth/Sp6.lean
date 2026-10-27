module

public import Certificates.Data.Kernel.E27Orth.Sp
public import Certificates.Kernel.E27Orth.Sp6Data

public section

namespace CertificateChecks.KernelE27Orth.Sp6

open CFSG.KC.Enum CFSG.KC.E27Orth CFSG.KC.Misc.G24

theorem sp6131002_sp : allN 2 (fun j => spOK 6 J (G j)) = true := by decide +kernel

theorem sp6131002_base : baseI (cnF2 6) (oneF2 6) 2 G = true := by decide +kernel

theorem sp6131002_tree : allN 81 (treeI (mulF2 6) (cnF2 6) (oneF2 6) 2 G E Tr) = true := by
  decide +kernel

theorem sp6131002_key : allN 81 (keyI 81 E Ss) = true := by decide +kernel

theorem sp6131002_left : allN 162 (leftI (mulF2 6) 81 G E Lf) = true := by decide +kernel

theorem sp6131002_cen : allN 81 (cenI 6 (oneF2 6) 2 1 G E) = true := by decide +kernel

theorem sp6131002_fs : allN 81 (fsI 6 (oneF2 6) 1 8 E Fl Fm) = true := by decide +kernel

theorem sp6131002_pair : allN 64 (pairI 6 (oneF2 6) 1 8 E Fl Pw) = true := by decide +kernel

end CertificateChecks.KernelE27Orth.Sp6

end
