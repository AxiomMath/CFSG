module

public import Certificates.Kernel.Misc.Perm.Fuse.Data
public import Certificates.Kernel.Misc.Perm.SylCent.Data
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.Fuse

open CFSG.KC.Ord CFSG.KS CFSG.KC.Misc.Clos CFSG.KC.Misc.ClosW CFSG.KC.Misc.Fuse
open CFSG.KC.LQT.P (allN)
open CFSG.KC.Enum (pcomp pidn)
open CertificateChecks.KernelMisc.SylCent (GC)

theorem kw2 : allN 2 (wWordAt 42 6 GC 3 KW2 KG2) = true := by quickRfl
theorem kc2 : allN 2 (fun j => commK 42 6 (KG2 j) (GC 4)) = true := by quickRfl
theorem tree2 : allN 168 (treeAt (pcomp 42 6 (mask 6)) (pidn 42 6) KG2 2 E2 PA2) = true := by
  quickRfl
theorem sort2 : allN 168 (sortAt 168 E2 SG2) = true := by quickRfl
theorem cl2 : allN 168 (closedAt (pcomp 42 6 (mask 6)) KG2 2 168 E2 CT2) = true := by quickRfl
theorem ot2 : allN 120 (treeAt (conjM 42 6) (GC 4) GC 3 O2 OP2) = true := by quickRfl
theorem os2 : allN 120 (sortAt 120 O2 OS2) = true := by quickRfl
theorem f2 : allN 168 (fuseAt 42 6 (GC 4) E2 GC 3 SW2 SC2) = true := by quickRfl

theorem kw3 : allN 2 (wWordAt 42 6 GC 3 KW3 KG3) = true := by quickRfl
theorem kc3 : allN 2 (fun j => commK 42 6 (KG3 j) (GC 5)) = true := by quickRfl
theorem tree3 : allN 60 (treeAt (pcomp 42 6 (mask 6)) (pidn 42 6) KG3 2 E3 PA3) = true := by
  quickRfl
theorem sort3 : allN 60 (sortAt 60 E3 SG3) = true := by quickRfl
theorem cl3 : allN 60 (closedAt (pcomp 42 6 (mask 6)) KG3 2 60 E3 CT3) = true := by quickRfl
theorem ot3 : allN 336 (treeAt (conjM 42 6) (GC 5) GC 3 O3 OP3) = true := by quickRfl
theorem os3 : allN 336 (sortAt 336 O3 OS3) = true := by quickRfl
theorem f3 : allN 60 (fuseAt 42 6 (GC 5) E3 GC 3 SW3 SC3) = true := by quickRfl

theorem kw4 : allN 2 (wWordAt 42 6 GC 3 KW4 KG4) = true := by quickRfl
theorem kc4 : allN 2 (fun j => commK 42 6 (KG4 j) (pcomp 42 6 (mask 6) (GC 4) (GC 5))) = true := by
  quickRfl
theorem tree4 : allN 72 (treeAt (pcomp 42 6 (mask 6)) (pidn 42 6) KG4 2 E4 PA4) = true := by
  quickRfl
theorem sort4 : allN 72 (sortAt 72 E4 SG4) = true := by quickRfl
theorem cl4 : allN 72 (closedAt (pcomp 42 6 (mask 6)) KG4 2 72 E4 CT4) = true := by quickRfl
theorem ot4 :
    allN 280 (treeAt (conjM 42 6) (pcomp 42 6 (mask 6) (GC 4) (GC 5)) GC 3 O4 OP4) = true := by
  quickRfl
theorem os4 : allN 280 (sortAt 280 O4 OS4) = true := by quickRfl
theorem f4 :
    allN 72 (fuseAt 42 6 (pcomp 42 6 (mask 6) (GC 4) (GC 5)) E4 GC 3 SW4 SC4) = true := by
  quickRfl

end CertificateChecks.KernelMisc.Fuse

end
