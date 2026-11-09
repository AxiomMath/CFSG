module

public import Certificates.Kernel.HNLocal.Data
public import Certificates.Data.Kernel.HNLocalD
public import CFSG.Certificates.Kernel.Orders.HN.Data.Const
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HNLocal

@[expose] def D12a : List Nat :=
  [44, 812, 844, 892, 1324, 1356, 1404, 1580, 2348, 2380, 2428, 2604, 3116, 3884, 3916, 3964, 4124,
    4684, 4732, 4892, 5196, 5244]

@[expose] def D12b : List Nat :=
  [5404, 5660, 6220, 6268, 6428, 6684, 7196, 7756, 7804, 7964, 8492, 8524, 8572, 8748, 9260, 10028,
    10060, 10108, 10284, 11052, 11084]

@[expose] def D12c : List Nat :=
  [11132, 11564, 11596, 11644, 11820, 12364, 12412, 12572, 12828, 13340, 13900, 13948, 14108,
    14364, 14924, 14972, 15132, 15436, 15484, 15644, 15900]

theorem ceV12 : CFSG.KC.HNLocal.cenVDAt vm PC TG (D12a ++ (D12b ++ D12c)) (nat_lit 0x0)
    (nat_lit 0xc) (nat_lit 0x4) (nat_lit 0xa) = true := by
  quickRfl

end CFSG.KD.HNLocal

end
