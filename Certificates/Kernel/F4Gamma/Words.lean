module

public import Certificates.Kernel.F4Gamma.Data
public import Certificates.Data.Kernel.F4Syl3PhiInv

public section

namespace CFSG.KD.F4Gamma

open CFSG.KC.F4Salt CFSG.KC.F4Syl3

theorem flip_ok : allN 3 (fun k => flipOK (ws.getD k 0) (fs.getD k 0) (ls.getD k 0)) = true := by
  decide +kernel

theorem word0_ok : eqS (wordS (ws.getD 0 0) (ls.getD 0 0)) (saltOf (gs.getD 0 0)) = true := by
  decide +kernel

theorem flip0_ok : eqS (wordS (fs.getD 0 0) (ls.getD 0 0)) (saltOf (gs.getD 0 0)) = true := by
  decide +kernel

theorem word1_ok : eqS (wordS (ws.getD 1 0) (ls.getD 1 0)) (saltOf (gs.getD 1 0)) = true := by
  decide +kernel

theorem flip1_ok : eqS (wordS (fs.getD 1 0) (ls.getD 1 0)) (saltOf (gs.getD 1 0)) = true := by
  decide +kernel

theorem word2_ok : eqS (wordS (ws.getD 2 0) (ls.getD 2 0)) (saltOf (gs.getD 2 0)) = true := by
  decide +kernel

theorem flip2_ok : eqS (wordS (fs.getD 2 0) (ls.getD 2 0)) (saltOf (gs.getD 2 0)) = true := by
  decide +kernel

end CFSG.KD.F4Gamma

end
