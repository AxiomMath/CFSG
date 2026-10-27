module

public import Certificates.Data.Kernel.Fi23T.Defs
public import Certificates.Data.CFSGNative.Fi23.TrData
public import Certificates.Data.CFSGNative.Fi22.LHData
public import CFSG.Certificates.Kernel.Spor.PK.Str
public import Certificates.Kernel.Fi23K.Tabs
public import Certificates.Kernel.Fi23C.Data
public import Certificates.Kernel.Fi23T.Data
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Misc.KernelRfl

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Fi23T

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23T CFSG.KC.Fi23C CFSG.KD.Fi23K CFSG.Sporadic.Fi23.Native CFSG.KS.PK

set_option Elab.async false

theorem t_list : listK H (nat_lit 0) (nat_lit 1) (nat_lit 3240) (nat_lit 31671) = true := by quickRfl
theorem o_list : listK H (nat_lit 2) (nat_lit 3) (nat_lit 1080) (nat_lit 31671) = true := by quickRfl
theorem l0_list : listK H (nat_lit 4) (nat_lit 5) (nat_lit 351) (nat_lit 3510) = true := by quickRfl
theorem l1_list : listK H (nat_lit 6) (nat_lit 7) (nat_lit 351) (nat_lit 3510) = true := by quickRfl
theorem o_sub : allN (nat_lit 1080) (fun i => domT H (tb H (nat_lit 2) i)) = true := by quickRfl

theorem tr_lit : trData () = natsOf (strL (render (hList H (nat_lit 0) (nat_lit 0) (nat_lit 3240)))) := by
  kernelRfl
theorem c_lit : cData () = natsOf (strL (render (hList H (nat_lit 2) (nat_lit 0) (nat_lit 1080)))) := by
  kernelRfl
theorem lh_lit : CFSG.Sporadic.Fi22.Native.lhData () =
    #[(hList H (nat_lit 4) (nat_lit 0) (nat_lit 351)).toArray,
      (hList H (nat_lit 6) (nat_lit 0) (nat_lit 351)).toArray] := by
  kernelRfl

theorem xi_lit : hList H (nat_lit 40) (nat_lit 0) (nat_lit 10) =
    [nat_lit 1, nat_lit 32, nat_lit 37, nat_lit 39, nat_lit 49, nat_lit 52, nat_lit 53, nat_lit 59,
      nat_lit 64, nat_lit 71] := by kernelRfl
theorem cg_lit : hList H (nat_lit 41) (nat_lit 0) (nat_lit 9) =
    [nat_lit 1, nat_lit 32, nat_lit 37, nat_lit 39, nat_lit 49, nat_lit 52, nat_lit 53, nat_lit 59,
      nat_lit 64] := by kernelRfl
theorem k_lit : hList H (nat_lit 42) (nat_lit 0) (nat_lit 5) =
    [nat_lit 37, nat_lit 53, nat_lit 78, nat_lit 92, nat_lit 226] := by kernelRfl
theorem kv_lit : hList H (nat_lit 43) (nat_lit 0) (nat_lit 5) =
    [nat_lit 1, nat_lit 146, nat_lit 189, nat_lit 218, nat_lit 222] := by kernelRfl

theorem star_ok : starK G H CFSG.KD.Fi23C.H (nat_lit 11504) (nat_lit 351) (nat_lit 351) = true := by
  quickRfl

end CFSG.KD.Fi23T

end
