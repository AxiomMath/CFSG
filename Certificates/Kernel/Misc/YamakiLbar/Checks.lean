module

public import Certificates.Data.Kernel.Misc.YamakiLbar
public import Certificates.Kernel.Misc.YamakiA0.Rec
public import Certificates.Kernel.Misc.YamakiLbar.Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.YamakiLbar

open CFSG.KD.YamakiA0 (REC)

theorem yl_coord_ok : coordK REC QREC = true := by quickRfl

theorem yl_gl_ok : glK REC QREC = true := by quickRfl

theorem yl_tab_ok : lbTabK QREC = true := by quickRfl

theorem yl_mem_ok : lbMemK QREC = true := by quickRfl

theorem yl_orb_ok : orbK QREC = true := by quickRfl

theorem yl_ia_ok : iaK QREC = true := by quickRfl

theorem yl_ib_ok : ibK QREC = true := by quickRfl

theorem yl_rep_ok : repK QREC = true := by quickRfl

theorem yl_tree_ok : treeK QREC = true := by quickRfl

theorem yl_cand_ok : candK QREC WREC = true := by quickRfl

end CFSG.KD.YamakiLbar

end
