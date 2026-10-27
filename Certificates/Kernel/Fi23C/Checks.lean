module

public import Certificates.Data.Kernel.Fi23C.Defs
public import Certificates.Data.CFSGNative.Fi23.CentralizerData
public import CFSG.Certificates.Kernel.Spor.PK.Str
public import Certificates.Kernel.Fi23K.Tabs
public import Certificates.Kernel.Fi23C.Data
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Misc.KernelRfl

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Fi23C

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23C CFSG.KD.Fi23K CFSG.Sporadic.Fi23.Native CFSG.KS.PK

set_option Elab.async false

theorem ea_ok : eaK G H = true := by quickRfl
theorem ep_ok : epK G H = true := by quickRfl
theorem phi_ok : phiK H = true := by quickRfl
theorem d2_ok : d2K G = true := by quickRfl
theorem tree_ok : treeK G H = true := by quickRfl
theorem sw_ok : swK H starWord = true := by quickRfl
theorem pow_ok : powK G starWord (nat_lit 11)
    [nat_lit 0, nat_lit 1, nat_lit 2, nat_lit 3, nat_lit 4, nat_lit 5] = true := by quickRfl

theorem lit_ok : starPhi () = natsOf (strL (render (hList H (nat_lit 2) (nat_lit 0) (nat_lit 3510)))) := by
  kernelRfl

theorem neg_row : Bool.not (rowSl G H (nat_lit 3) (nat_lit 0)) = true := by quickRfl
theorem neg_pow : Bool.not (powK G starWord (nat_lit 10)
    [nat_lit 0, nat_lit 1, nat_lit 2, nat_lit 3, nat_lit 4, nat_lit 5]) = true := by quickRfl
theorem neg_sw : Bool.not (swK H [nat_lit 0]) = true := by quickRfl
theorem neg_tree : Bool.not (Nat.beq (cJ G (tb H (nat_lit 0) (tb H (nat_lit 8) (nat_lit 1)))
    (tb H (nat_lit 0) (tb H (nat_lit 4) (nat_lit 0)))) (tb H (nat_lit 0) (tb H (nat_lit 4) (nat_lit 0))))
    = true := by quickRfl

end CFSG.KD.Fi23C

end
