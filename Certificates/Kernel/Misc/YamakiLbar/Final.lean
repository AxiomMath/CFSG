module

public import CFSG.Certificates.Kernel.Misc.YamakiLbarSound4
public import Certificates.Kernel.Misc.YamakiLbar.Checks
public import Certificates.Kernel.Misc.YamakiA0.Final

public section

namespace CFSG.KD.YamakiLbar

open CFSG.KC.YamakiLbar CFSG.ClassicalInvolution.Sp62Rec

theorem cert550104_ok :
    (z6LbarCheck () = true) ∧ (z6OrbCheck () = true) ∧ (z6NormCheck () = true) :=
  cert550104_of CFSG.KD.YamakiA0.ya0_gens CFSG.KD.YamakiA0.ya0_tab_ok yl_coord_ok yl_gl_ok
    yl_tab_ok yl_mem_ok yl_orb_ok yl_rep_ok yl_ia_ok yl_ib_ok yl_tree_ok yl_cand_ok

end CFSG.KD.YamakiLbar

end
